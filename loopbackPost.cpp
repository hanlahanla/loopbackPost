#define UNICODE
#define _UNICODE
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX

#include <windows.h>
#include <conio.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <ksmedia.h>
#include <winhttp.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <deque>
#include <iostream>
#include <limits>
#include <string>
#include <thread>
#include <vector>

#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "uuid.lib")
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "winhttp.lib")

static std::atomic_bool g_stop{false};
static std::atomic_uint g_volumeUpRequests{0};
static std::atomic_uint g_volumeDownRequests{0};
static std::atomic_bool g_reconnectRequested{false};
static HHOOK g_keyboardHook = nullptr;
static HANDLE g_keyboardHookReadyEvent = nullptr;
static HANDLE g_keyboardHookStopEvent = nullptr;
static HANDLE g_keyboardHookThread = nullptr;
static DWORD g_keyboardHookError = ERROR_SUCCESS;
static bool g_volumeUpPressed = false;
static bool g_volumeDownPressed = false;
static bool g_volumeMutePressed = false;

// 单次写入超过 1 ms，才认为是实际发送阻塞并计入补偿欠账。
static constexpr double kBlockedWriteMs = 5.0;

// 本次连接内累计“实际阻塞”的毫秒数
static double g_blockedMs = 0.0;
static uint64_t g_writeCalls = 0;
static uint64_t g_writeOver1MsCalls = 0;
static double g_writeMaxMs = 0.0;
static DWORD g_lastWinHttpError = ERROR_SUCCESS;

static void ResetWriteStats()
{
    g_blockedMs = 0.0;
    g_writeCalls = 0;
    g_writeOver1MsCalls = 0;
    g_writeMaxMs = 0.0;
}

static void PrintHr(const wchar_t* where, HRESULT hr);

// Configure short-period, event-driven shared-mode loopback capture.
static bool InitializeLowLatencyLoopback(IMMDevice* device,
                                         IAudioClient** audioClient,
                                         const WAVEFORMATEX* format,
                                         HANDLE audioEvent)
{
    constexpr REFERENCE_TIME fallbackDuration = 50000; // 5 ms
    REFERENCE_TIME bufferDuration = fallbackDuration;
    UINT32 minPeriodFrames = 0;
    UINT32 defaultPeriodFrames = 0;

    IAudioClient3* audioClient3 = nullptr;
    HRESULT hr = (*audioClient)->QueryInterface(
        __uuidof(IAudioClient3),
        reinterpret_cast<void**>(&audioClient3));
    if (SUCCEEDED(hr) && audioClient3) {
        UINT32 fundamentalPeriodFrames = 0;
        UINT32 maxPeriodFrames = 0;
        hr = audioClient3->GetSharedModeEnginePeriod(
            format,
            &defaultPeriodFrames,
            &fundamentalPeriodFrames,
            &minPeriodFrames,
            &maxPeriodFrames);
        if (SUCCEEDED(hr) && minPeriodFrames > 0 &&
            format->nSamplesPerSec > 0) {
            bufferDuration = static_cast<REFERENCE_TIME>(
                (static_cast<uint64_t>(minPeriodFrames) * 10000000ULL +
                 format->nSamplesPerSec - 1) /
                format->nSamplesPerSec);
        } else if (FAILED(hr)) {
            PrintHr(L"IAudioClient3::GetSharedModeEnginePeriod", hr);
        }
        audioClient3->Release();
    } else if (hr != E_NOINTERFACE) {
        PrintHr(L"QueryInterface(IAudioClient3)", hr);
    }

    const auto reactivateAudioClient = [&]() -> bool {
        (*audioClient)->Release();
        *audioClient = nullptr;
        const HRESULT activateHr = device->Activate(
            __uuidof(IAudioClient), CLSCTX_ALL, nullptr,
            reinterpret_cast<void**>(audioClient));
        if (FAILED(activateHr)) {
            PrintHr(L"IMMDevice::Activate(IAudioClient,polling fallback)", activateHr);
            return false;
        }
        return true;
    };

    hr = (*audioClient)->Initialize(
        AUDCLNT_SHAREMODE_SHARED,
        AUDCLNT_STREAMFLAGS_LOOPBACK |
            AUDCLNT_STREAMFLAGS_EVENTCALLBACK,
        bufferDuration,
        0,
        format,
        nullptr);
    if (FAILED(hr)) {
        PrintHr(L"IAudioClient::Initialize(loopback,event-driven)", hr);
        if (!reactivateAudioClient())
            return false;
        hr = (*audioClient)->Initialize(
            AUDCLNT_SHAREMODE_SHARED,
            AUDCLNT_STREAMFLAGS_LOOPBACK,
            bufferDuration,
            0,
            format,
            nullptr);
        if (FAILED(hr)) {
            PrintHr(L"IAudioClient::Initialize(loopback,polling fallback)", hr);
            return false;
        }
        std::wcout << L"Event-driven capture unavailable; using polling fallback.\n";
        return true;
    }
    hr = (*audioClient)->SetEventHandle(audioEvent);
    if (FAILED(hr)) {
        PrintHr(L"IAudioClient::SetEventHandle(loopback fallback)", hr);
        if (!reactivateAudioClient())
            return false;
        hr = (*audioClient)->Initialize(
            AUDCLNT_SHAREMODE_SHARED,
            AUDCLNT_STREAMFLAGS_LOOPBACK,
            bufferDuration,
            0,
            format,
            nullptr);
        if (FAILED(hr)) {
            PrintHr(L"IAudioClient::Initialize(loopback,polling fallback)", hr);
            return false;
        }
        std::wcout << L"Event handle unavailable; using polling fallback.\n";
        return true;
    }
    std::wcout << L"Event-driven loopback capture; ";
    if (minPeriodFrames > 0) {
        std::wcout << L"IAudioClient3 minimum shared period: "
                   << (static_cast<double>(minPeriodFrames) * 1000.0 /
                       format->nSamplesPerSec)
                   << L" ms, requested buffer: ";
    } else {
        std::wcout << L"IAudioClient3 period query unavailable, requesting ";
    }
    std::wcout << (static_cast<double>(bufferDuration) / 10000.0)
               << L" ms\n";
    return true;
}

// 累计被阻塞到这个程度后，不重连，优先丢掉 WASAPI 捕获缓冲中的旧音频。
static double kDropBacklogMs = 20.0;

// 拥塞补偿时“丢弃段”的最小粒度。
// 每个分片丢一半：按kDropUnitMs粒度交替丢,然后发送留下的部分
static constexpr double kDropUnitMs = 1.0;
// 延迟已经非常大时，直接把旧数据全部丢掉，避免用户长时间听到快进/跳跃。
static constexpr double kDropAllBacklogMs = 1000.0;

// HTTP/网络重连最多自动尝试 3 次；只有真正写出音频数据后才清零。
static constexpr int kMaxAutoReconnectAttempts = 3;

// 使用命令行 URL 启动时，3 次自动重连全部失败后继续后台运行，
// 每 10 秒重新尝试一次，适合开机启动；交互模式仍等待 Enter。
static constexpr auto kServiceRetryDelay = std::chrono::seconds(10);

// 拥塞/手动重连：先停采集并清空捕获缓冲，等待服务端释放旧的 aplay 后再恢复采集。
static constexpr auto kCongestionReconnectDelay =
    std::chrono::milliseconds(200);

BOOL WINAPI ConsoleHandler(DWORD type)
{
    switch (type) {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
    case CTRL_CLOSE_EVENT:
    case CTRL_LOGOFF_EVENT:
    case CTRL_SHUTDOWN_EVENT:
        g_stop = true;
        return TRUE;
    default:
        return FALSE;
    }
}

static void PrintWinError(const wchar_t* where, DWORD err = GetLastError())
{
    std::wcerr << where << L" failed, error=" << err << L" (0x"
               << std::hex << err << std::dec << L")\n";
}

static void PrintHr(const wchar_t* where, HRESULT hr)
{
    std::wcerr << where << L" failed, HRESULT=0x"
               << std::hex << static_cast<unsigned long>(hr) << std::dec << L"\n";
}

// 实现媒体按键音量键的拦截,实际控制音箱的音量
static LRESULT CALLBACK LowLevelKeyboardProc(int code,
                                              WPARAM message,
                                              LPARAM data)
{
    if (code == HC_ACTION) {
        const auto* key =
            reinterpret_cast<const KBDLLHOOKSTRUCT*>(data);

        if (key->vkCode == VK_VOLUME_UP) {
            if (message == WM_KEYDOWN || message == WM_SYSKEYDOWN) {
                if (!g_volumeUpPressed) {
                    g_volumeUpRequests.fetch_add(1);
                    g_volumeUpPressed = true;
                }
                return 1;
            }

            if (message == WM_KEYUP || message == WM_SYSKEYUP) {
                g_volumeUpPressed = false;
                return 1;
            }
        } else if (key->vkCode == VK_VOLUME_DOWN) {
            if (message == WM_KEYDOWN || message == WM_SYSKEYDOWN) {
                if (!g_volumeDownPressed) {
                    g_volumeDownRequests.fetch_add(1);
                    g_volumeDownPressed = true;
                }
                return 1;
            }

            if (message == WM_KEYUP || message == WM_SYSKEYUP) {
                g_volumeDownPressed = false;
                return 1;
            }
        } else if (key->vkCode == VK_VOLUME_MUTE) {
            if (message == WM_KEYDOWN || message == WM_SYSKEYDOWN) {
                if (!g_volumeMutePressed) {
                    g_reconnectRequested.store(true);
                    g_volumeMutePressed = true;
                }
                return 1;
            }

            if (message == WM_KEYUP || message == WM_SYSKEYUP) {
                g_volumeMutePressed = false;
                return 1;
            }
        }
    }

    return CallNextHookEx(g_keyboardHook, code, message, data);
}

static DWORD WINAPI KeyboardHookThreadProc(void*)
{
    MSG message{};
    PeekMessageW(&message, nullptr, WM_USER, WM_USER, PM_NOREMOVE);
    g_keyboardHook = SetWindowsHookExW(
        WH_KEYBOARD_LL,
        LowLevelKeyboardProc,
        GetModuleHandleW(nullptr),
        0);

    if (!g_keyboardHook)
        g_keyboardHookError = GetLastError();

    SetEvent(g_keyboardHookReadyEvent);

    if (!g_keyboardHook)
        return 1;

    for (;;) {
        const DWORD waitResult = MsgWaitForMultipleObjects(
            1,
            &g_keyboardHookStopEvent,
            FALSE,
            INFINITE,
            QS_ALLINPUT);

        if (waitResult == WAIT_OBJECT_0)
            break;

        if (waitResult == WAIT_OBJECT_0 + 1) {
            while (PeekMessageW(&message, nullptr, 0, 0, PM_REMOVE)) {
                if (message.message == WM_QUIT)
                    goto finished;

                TranslateMessage(&message);
                DispatchMessageW(&message);
            }
            continue;
        }

        PrintWinError(L"MsgWaitForMultipleObjects(keyboard hook)");
        break;
    }

finished:
    if (!UnhookWindowsHookEx(g_keyboardHook))
        PrintWinError(L"UnhookWindowsHookEx");
    g_keyboardHook = nullptr;
    return 0;
}

static bool StartKeyboardHook()
{
    g_keyboardHookReadyEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_keyboardHookReadyEvent) {
        PrintWinError(L"CreateEvent(keyboard hook ready)");
        return false;
    }

    g_keyboardHookStopEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_keyboardHookStopEvent) {
        PrintWinError(L"CreateEvent(keyboard hook stop)");
        CloseHandle(g_keyboardHookReadyEvent);
        g_keyboardHookReadyEvent = nullptr;
        return false;
    }

    g_keyboardHookThread = CreateThread(
        nullptr,
        0,
        KeyboardHookThreadProc,
        nullptr,
        0,
        nullptr);

    if (!g_keyboardHookThread) {
        PrintWinError(L"CreateThread(keyboard hook)");
        CloseHandle(g_keyboardHookStopEvent);
        CloseHandle(g_keyboardHookReadyEvent);
        g_keyboardHookStopEvent = nullptr;
        g_keyboardHookReadyEvent = nullptr;
        return false;
    }

    const DWORD waitResult =
        WaitForSingleObject(g_keyboardHookReadyEvent, INFINITE);
    if (waitResult != WAIT_OBJECT_0) {
        if (waitResult == WAIT_FAILED)
            PrintWinError(L"WaitForSingleObject(keyboard hook ready)");
        else
            std::wcerr << L"Unexpected keyboard hook startup wait result.\n";
    } else if (g_keyboardHook) {
        std::wcout
            << L"Media volume keys are captured; system volume will not change.\n";
        return true;
    } else {
        PrintWinError(L"SetWindowsHookEx(WH_KEYBOARD_LL)", g_keyboardHookError);
    }

    SetEvent(g_keyboardHookStopEvent);
    if (WaitForSingleObject(g_keyboardHookThread, INFINITE) != WAIT_OBJECT_0)
        PrintWinError(L"WaitForSingleObject(keyboard hook thread)");
    CloseHandle(g_keyboardHookThread);
    CloseHandle(g_keyboardHookStopEvent);
    CloseHandle(g_keyboardHookReadyEvent);
    g_keyboardHookThread = nullptr;
    g_keyboardHookStopEvent = nullptr;
    g_keyboardHookReadyEvent = nullptr;
    return false;
}

static void StopKeyboardHook()
{
    if (!g_keyboardHookThread)
        return;

    if (!SetEvent(g_keyboardHookStopEvent))
        PrintWinError(L"SetEvent(keyboard hook stop)");

    if (WaitForSingleObject(g_keyboardHookThread, INFINITE) != WAIT_OBJECT_0)
        PrintWinError(L"WaitForSingleObject(keyboard hook thread)");
    CloseHandle(g_keyboardHookThread);
    CloseHandle(g_keyboardHookStopEvent);
    CloseHandle(g_keyboardHookReadyEvent);
    g_keyboardHookThread = nullptr;
    g_keyboardHookStopEvent = nullptr;
    g_keyboardHookReadyEvent = nullptr;
}

struct UrlParts {
    std::wstring host;
    std::wstring path;
    INTERNET_PORT port = 0;
    bool https = false;
    bool portSpecified = false;
};

static bool HasExplicitPort(const std::wstring& url) {
    const size_t schemeEnd = url.find(L"://");
    const size_t authorityBegin =
        schemeEnd == std::wstring::npos ? 0 : schemeEnd + 3;
    const size_t authorityEnd =
        url.find_first_of(L"/?#", authorityBegin);
    std::wstring authority = url.substr(
        authorityBegin,
        authorityEnd == std::wstring::npos
            ? std::wstring::npos
            : authorityEnd - authorityBegin);

    const size_t userInfoEnd = authority.rfind(L'@');
    if (userInfoEnd != std::wstring::npos) {
        authority.erase(0, userInfoEnd + 1);
    }

    size_t portSeparator = std::wstring::npos;
    if (!authority.empty() && authority.front() == L'[') {
        const size_t hostEnd = authority.find(L']');
        if (hostEnd != std::wstring::npos &&
            hostEnd + 1 < authority.size() &&
            authority[hostEnd + 1] == L':') {
            portSeparator = hostEnd + 1;
        }
    } else {
        portSeparator = authority.rfind(L':');
    }

    if (portSeparator == std::wstring::npos ||
        portSeparator + 1 == authority.size()) {
        return false;
    }

    return std::all_of(
        authority.begin() + portSeparator + 1,
        authority.end(),
        [](wchar_t c) { return c >= L'0' && c <= L'9'; });
}

static bool IsConnectionFailure(DWORD error) {
    return error == ERROR_WINHTTP_CANNOT_CONNECT ||
           error == ERROR_WINHTTP_CONNECTION_ERROR ||
           error == ERROR_WINHTTP_TIMEOUT;
}

static bool AdvancePortFallback(UrlParts& parts) {
    if (parts.https) {
        return false;
    }

    if (!parts.portSpecified && parts.port == INTERNET_DEFAULT_HTTP_PORT) {
        parts.port = 8080;
    } else if (parts.port == 8080) {
        parts.port = 8880;
    } else {
        return false;
    }

    return true;
}

static bool CrackUrl(const std::wstring& url, UrlParts& out)
{
    URL_COMPONENTS uc{};
    uc.dwStructSize = sizeof(uc);

    wchar_t host[512] = {};
    wchar_t path[4096] = {};
    wchar_t extra[4096] = {};

    uc.lpszHostName = host;
    uc.dwHostNameLength = _countof(host);

    uc.lpszUrlPath = path;
    uc.dwUrlPathLength = _countof(path);

    uc.lpszExtraInfo = extra;
    uc.dwExtraInfoLength = _countof(extra);

    std::wstring fullUrl = url;

    // 没有 scheme 时按 HTTP 处理，路径则在解析后单独补齐。
    if (fullUrl.rfind(L"http", 0) != 0) {
        fullUrl = L"http://" + fullUrl;
    }

    if (!WinHttpCrackUrl(fullUrl.c_str(), 0, 0, &uc)) {
        PrintWinError(L"WinHttpCrackUrl");
        return false;
    }

    out.https = (uc.nScheme == INTERNET_SCHEME_HTTPS);
    out.port = uc.nPort;
    out.portSpecified = HasExplicitPort(fullUrl);

    if (uc.dwHostNameLength == 0) {
        std::wcerr << L"Invalid URL: missing host.\n";
        return false;
    }

    out.host.assign(host, uc.dwHostNameLength);

    if (uc.dwUrlPathLength > 0)
        out.path.assign(path, uc.dwUrlPathLength);
    else
        out.path = L"/aplay";

    if (out.path == L"/")
        out.path = L"/aplay";

    if (uc.dwExtraInfoLength > 0)
        out.path.append(extra, uc.dwExtraInfoLength);

    return true;
}

static void SetQueryParameter(std::wstring& path,
                              const std::wstring& name,
                              const std::wstring& value)
{
    const size_t q = path.find(L'?');

    if (q == std::wstring::npos) {
        path += L"?" + name + L"=" + value;
        return;
    }

    const size_t queryBegin = q + 1;
    const size_t fragment = path.find(L'#', queryBegin);
    const size_t queryEnd =
        (fragment == std::wstring::npos) ? path.size() : fragment;

    std::wstring query = path.substr(queryBegin, queryEnd - queryBegin);

    std::wstring out;
    bool found = false;
    size_t pos = 0;

    while (pos <= query.size()) {
        size_t amp = query.find(L'&', pos);

        if (amp == std::wstring::npos)
            amp = query.size();

        const std::wstring item = query.substr(pos, amp - pos);

        const size_t eq = item.find(L'=');
        const std::wstring key =
            (eq == std::wstring::npos) ? item : item.substr(0, eq);

        if (key == name) {
            if (!found) {
                if (!out.empty())
                    out += L'&';

                out += name + L"=" + value;
                found = true;
            }
        } else if (!item.empty()) {
            if (!out.empty())
                out += L'&';

            out += item;
        }

        if (amp == query.size())
            break;

        pos = amp + 1;
    }

    if (!found) {
        if (!out.empty())
            out += L'&';

        out += name + L"=" + value;
    }

    path = path.substr(0, queryBegin) + out +
           ((fragment == std::wstring::npos)
                ? L""
                : path.substr(fragment));
}

static std::wstring BuildAudioUrl(const std::wstring& originalUrl,
                                   DWORD sampleRate,
                                   WORD channels)
{
    UrlParts parts;

    if (!CrackUrl(originalUrl, parts))
        return L"";

    SetQueryParameter(
        parts.path,
        L"rate",
        std::to_wstring(sampleRate));

    SetQueryParameter(
        parts.path,
        L"channels",
        std::to_wstring(channels));

    const std::wstring scheme =
        parts.https ? L"https://" : L"http://";

    std::wstring result = scheme + parts.host;

    const bool defaultPort =
        (parts.https &&
         parts.port == INTERNET_DEFAULT_HTTPS_PORT) ||
        (!parts.https &&
         parts.port == INTERNET_DEFAULT_HTTP_PORT);

    if (!defaultPort || parts.portSpecified)
        result += L":" + std::to_wstring(parts.port);

    result += parts.path;

    return result;
}

static std::wstring BuildVolumeUrl(const UrlParts& source,
                                   const wchar_t* volumePath)
{
    UrlParts parts = source;

    if (parts.port == 8880)
        parts.port = 8080;

    parts.path = volumePath;

    const std::wstring scheme =
        parts.https ? L"https://" : L"http://";

    std::wstring result = scheme + parts.host;

    const bool defaultPort =
        (parts.https &&
         parts.port == INTERNET_DEFAULT_HTTPS_PORT) ||
        (!parts.https &&
         parts.port == INTERNET_DEFAULT_HTTP_PORT);

    if (!defaultPort)
        result += L":" + std::to_wstring(parts.port);

    result += parts.path;
    return result;
}

static bool SendVolumeRequest(const UrlParts& source,
                              const wchar_t* volumePath)
{
    UrlParts parts = source;

    if (parts.port == 8880)
        parts.port = 8080;

    parts.path = volumePath;

    HINTERNET session = WinHttpOpen(
        L"workdayAlarmClockGo/1.0",
        WINHTTP_ACCESS_TYPE_NO_PROXY,
        WINHTTP_NO_PROXY_NAME,
        WINHTTP_NO_PROXY_BYPASS,
        0);

    if (!session) {
        PrintWinError(L"WinHttpOpen(volume)");
        return false;
    }

    WinHttpSetTimeouts(session, 1000, 1000, 1000, 1000);

    HINTERNET connect = WinHttpConnect(
        session,
        parts.host.c_str(),
        parts.port,
        0);

    if (!connect) {
        PrintWinError(L"WinHttpConnect(volume)");
        WinHttpCloseHandle(session);
        return false;
    }

    HINTERNET request = WinHttpOpenRequest(
        connect,
        L"GET",
        parts.path.c_str(),
        nullptr,
        WINHTTP_NO_REFERER,
        WINHTTP_DEFAULT_ACCEPT_TYPES,
        parts.https ? WINHTTP_FLAG_SECURE : 0);

    if (!request) {
        PrintWinError(L"WinHttpOpenRequest(volume)");
        WinHttpCloseHandle(connect);
        WinHttpCloseHandle(session);
        return false;
    }

    bool ok = false;

    if (WinHttpSendRequest(
            request,
            WINHTTP_NO_ADDITIONAL_HEADERS,
            0,
            WINHTTP_NO_REQUEST_DATA,
            0,
            0,
            0) &&
        WinHttpReceiveResponse(request, nullptr)) {
        DWORD status = 0;
        DWORD statusSize = sizeof(status);

        if (WinHttpQueryHeaders(
                request,
                WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER,
                WINHTTP_HEADER_NAME_BY_INDEX,
                &status,
                &statusSize,
                WINHTTP_NO_HEADER_INDEX)) {
            ok = (status >= 200 && status < 300);

            if (!ok) {
                std::wcerr
                    << L"Volume request failed, HTTP status="
                    << status
                    << L"\n";
            }
        }
    } else {
        PrintWinError(L"Volume request");
    }

    WinHttpCloseHandle(request);
    WinHttpCloseHandle(connect);
    WinHttpCloseHandle(session);

    return ok;
}

static void HandlePendingVolumeRequests(const UrlParts& parts)
{
    const unsigned int upRequests = g_volumeUpRequests.exchange(0);
    const unsigned int downRequests = g_volumeDownRequests.exchange(0);

    for (unsigned int i = 0; i < upRequests; ++i) {
        if (SendVolumeRequest(parts, L"/volp"))
            std::wcout << L"Volume up.\n";
    }

    for (unsigned int i = 0; i < downRequests; ++i) {
        if (SendVolumeRequest(parts, L"/volm"))
            std::wcout << L"Volume down.\n";
    }
}

static void SleepWhileHandlingVolumeRequests(
    std::chrono::milliseconds duration,
    const UrlParts& parts)
{
    const auto end = std::chrono::steady_clock::now() + duration;

    while (!g_stop.load()) {
        HandlePendingVolumeRequests(parts);

        const auto remaining = end - std::chrono::steady_clock::now();
        if (remaining <= std::chrono::steady_clock::duration::zero())
            break;

        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }
}

static bool ReadHttpResponse(HINTERNET request,
                              DWORD& status,
                              std::string& body,
                              std::wstring& location)
{
    status = 0;
    body.clear();
    location.clear();

    if (!WinHttpReceiveResponse(request, nullptr))
        return false;

    DWORD statusSize = sizeof(status);
    if (!WinHttpQueryHeaders(
            request,
            WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER,
            WINHTTP_HEADER_NAME_BY_INDEX,
            &status,
            &statusSize,
            WINHTTP_NO_HEADER_INDEX)) {
        status = 0;
    }

    DWORD locationSize = 0;
    WinHttpQueryHeaders(
        request,
        WINHTTP_QUERY_LOCATION,
        WINHTTP_HEADER_NAME_BY_INDEX,
        nullptr,
        &locationSize,
        WINHTTP_NO_HEADER_INDEX);

    if (GetLastError() == ERROR_INSUFFICIENT_BUFFER && locationSize > 0) {
        std::vector<wchar_t> buffer(locationSize / sizeof(wchar_t) + 1);
        if (WinHttpQueryHeaders(
                request,
                WINHTTP_QUERY_LOCATION,
                WINHTTP_HEADER_NAME_BY_INDEX,
                buffer.data(),
                &locationSize,
                WINHTTP_NO_HEADER_INDEX)) {
            location.assign(buffer.data(), locationSize / sizeof(wchar_t));
        }
    }

    for (;;) {
        DWORD available = 0;
        if (!WinHttpQueryDataAvailable(request, &available))
            break;

        if (available == 0)
            break;

        std::vector<char> buffer(available);
        DWORD read = 0;
        if (!WinHttpReadData(
                request,
                buffer.data(),
                available,
                &read)) {
            break;
        }

        if (read == 0)
            break;

        body.append(buffer.data(), read);
    }

    return true;
}

static void PrintHttpResponse(DWORD status,
                              const std::string& body,
                              const std::wstring& location)
{
    if (status != 0)
        std::wcerr << L"HTTP status: " << status << L"\n";

    if (!location.empty())
        std::wcerr << L"HTTP Location: " << location << L"\n";

    if (!body.empty()) {
        std::wcerr << L"HTTP response body: ";
        std::cerr.write(body.data(), static_cast<std::streamsize>(body.size()));
        std::cerr << "\n";
    }
}

static bool WriteRaw(HINTERNET request,
                     const BYTE* data,
                     DWORD bytes)
{
    while (bytes > 0) {
        DWORD written = 0;

        const auto writeStart = std::chrono::steady_clock::now();

        if (!WinHttpWriteData(
                request,
                data,
                bytes,
                &written)) {
            g_lastWinHttpError = GetLastError();
            PrintWinError(L"WinHttpWriteData", g_lastWinHttpError);
            return false;
        }

        const double writeMs =
            std::chrono::duration<double, std::milli>(
                std::chrono::steady_clock::now() - writeStart).count();

        ++g_writeCalls;
        if (writeMs >= 1.0)
            ++g_writeOver1MsCalls;
        g_writeMaxMs = std::max(g_writeMaxMs, writeMs);

        if (writeMs > kBlockedWriteMs)
            g_blockedMs += writeMs;

        g_lastWinHttpError = ERROR_SUCCESS;

        if (written == 0) {
            std::wcerr
                << L"WinHttpWriteData wrote 0 bytes.\n";
            return false;
        }

        data += written;
        bytes -= written;
    }

    return true;
}

static bool WritePcm(HINTERNET request,
                     const BYTE* data,
                     DWORD bytes)
{
    return WriteRaw(request, data, bytes);
}

static int16_t FloatToS16(float value)
{
    if (!std::isfinite(value))
        value = 0.0f;

    value = std::clamp(value, -1.0f, 1.0f);

    if (value >= 1.0f)
        return 32767;

    if (value <= -1.0f)
        return -32768;

    const float scaled = value * 32768.0f;

    long v = std::lround(scaled);

    if (v > 32767)
        v = 32767;

    if (v < -32768)
        v = -32768;

    return static_cast<int16_t>(v);
}

static int16_t S24ToS16(const BYTE* p)
{
    int32_t value =
        static_cast<int32_t>(p[0]) |
        (static_cast<int32_t>(p[1]) << 8) |
        (static_cast<int32_t>(p[2]) << 16);

    if (value & 0x00800000)
        value |= 0xFF000000;

    // 24-bit signed -> 16-bit signed
    value >>= 8;

    if (value > 32767)
        value = 32767;

    if (value < -32768)
        value = -32768;

    return static_cast<int16_t>(value);
}

static int16_t S32ToS16(const BYTE* p)
{
    int32_t value = 0;

    std::memcpy(&value, p, sizeof(value));

    // 32-bit signed -> 16-bit signed
    value >>= 16;

    if (value > 32767)
        value = 32767;

    if (value < -32768)
        value = -32768;

    return static_cast<int16_t>(value);
}

enum class SampleType {
    S16,
    S24,
    S32,
    FLOAT32,
    UNSUPPORTED
};

static SampleType GetSampleType(const WAVEFORMATEX* format)
{
    if (!format)
        return SampleType::UNSUPPORTED;

    if (format->wFormatTag == WAVE_FORMAT_EXTENSIBLE) {
        const auto* ext =
            reinterpret_cast<const WAVEFORMATEXTENSIBLE*>(format);

        if (IsEqualGUID(
                ext->SubFormat,
                KSDATAFORMAT_SUBTYPE_IEEE_FLOAT)) {
            if (format->wBitsPerSample == 32)
                return SampleType::FLOAT32;

            return SampleType::UNSUPPORTED;
        }

        if (IsEqualGUID(
                ext->SubFormat,
                KSDATAFORMAT_SUBTYPE_PCM)) {
            switch (format->wBitsPerSample) {
            case 16:
                return SampleType::S16;
            case 24:
                return SampleType::S24;
            case 32:
                return SampleType::S32;
            default:
                return SampleType::UNSUPPORTED;
            }
        }

        return SampleType::UNSUPPORTED;
    }

    if (format->wFormatTag == WAVE_FORMAT_IEEE_FLOAT) {
        if (format->wBitsPerSample == 32)
            return SampleType::FLOAT32;

        return SampleType::UNSUPPORTED;
    }

    if (format->wFormatTag == WAVE_FORMAT_PCM) {
        switch (format->wBitsPerSample) {
        case 16:
            return SampleType::S16;
        case 24:
            return SampleType::S24;
        case 32:
            return SampleType::S32;
        default:
            return SampleType::UNSUPPORTED;
        }
    }

    return SampleType::UNSUPPORTED;
}

static const wchar_t* SampleTypeName(SampleType type)
{
    switch (type) {
    case SampleType::S16:
        return L"s16";
    case SampleType::S24:
        return L"s24";
    case SampleType::S32:
        return L"s32";
    case SampleType::FLOAT32:
        return L"float32";
    default:
        return L"unsupported";
    }
}

static bool ConvertToS16(
    const BYTE* input,
    UINT32 frames,
    const WAVEFORMATEX* format,
    SampleType type,
    std::vector<int16_t>& output)
{
    if (!input || !format)
        return false;

    const UINT32 channels = format->nChannels;

    if (channels == 0)
        return false;

    const size_t sampleCount =
        static_cast<size_t>(frames) * channels;

    output.resize(sampleCount);

    switch (type) {
    case SampleType::S16:
        {
            std::memcpy(
                output.data(),
                input,
                sampleCount * sizeof(int16_t));
        }
        return true;

    case SampleType::FLOAT32:
        {
            const float* src =
                reinterpret_cast<const float*>(input);

            for (size_t i = 0; i < sampleCount; ++i)
                output[i] = FloatToS16(src[i]);
        }
        return true;

    case SampleType::S24:
        {
            for (size_t i = 0; i < sampleCount; ++i)
                output[i] = S24ToS16(input + i * 3);
        }
        return true;

    case SampleType::S32:
        {
            for (size_t i = 0; i < sampleCount; ++i)
                output[i] = S32ToS16(input + i * 4);
        }
        return true;

    default:
        return false;
    }
}

int wmain(int argc, wchar_t* argv[])
{
    std::wstring url;

    if (argc >= 2) {
        url = argv[1];
    } else {
        std::wcout
            << L"workdayAlarmClockGo URL end with /aplay: ";

        std::getline(std::wcin, url);
    }

    if (argc >= 3) {
        // 第二个参数是同步延迟ms
        kDropBacklogMs = std::wcstod(argv[2], nullptr);
    }

    if (url.empty()) {
        std::wcerr << L"No URL.\n";
        return 1;
    }

    UrlParts parts;

    if (!CrackUrl(url, parts))
        return 1;

    if (!SetConsoleCtrlHandler(
            ConsoleHandler,
            TRUE)) {
        PrintWinError(L"SetConsoleCtrlHandler");
        return 1;
    }

    HRESULT hr =
        CoInitializeEx(nullptr, COINIT_MULTITHREADED);

    if (FAILED(hr)) {
        PrintHr(L"CoInitializeEx", hr);
        return 1;
    }

    HINTERNET session = nullptr;
    HINTERNET connect = nullptr;
    HINTERNET request = nullptr;

    IMMDeviceEnumerator* enumerator = nullptr;
    IMMDevice* device = nullptr;
    IAudioClient* audioClient = nullptr;
    IAudioCaptureClient* captureClient = nullptr;
    WAVEFORMATEX* format = nullptr;
    HANDLE audioCaptureEvent = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    if (!audioCaptureEvent) {
        PrintWinError(L"CreateEventW(audio capture)");
        CoUninitialize();
        SetConsoleCtrlHandler(ConsoleHandler, FALSE);
        return 1;
    }

    bool ok = false;
    bool keyboardHookStarted = false;

    do {
        hr = CoCreateInstance(
            __uuidof(MMDeviceEnumerator),
            nullptr,
            CLSCTX_ALL,
            __uuidof(IMMDeviceEnumerator),
            reinterpret_cast<void**>(&enumerator));

        if (FAILED(hr)) {
            PrintHr(
                L"CoCreateInstance(MMDeviceEnumerator)",
                hr);
            break;
        }

        hr = enumerator->GetDefaultAudioEndpoint(
            eRender,
            eMultimedia,
            &device);

        if (FAILED(hr)) {
            PrintHr(
                L"GetDefaultAudioEndpoint",
                hr);
            break;
        }

        hr = device->Activate(
            __uuidof(IAudioClient),
            CLSCTX_ALL,
            nullptr,
            reinterpret_cast<void**>(&audioClient));

        if (FAILED(hr)) {
            PrintHr(
                L"IMMDevice::Activate(IAudioClient)",
                hr);
            break;
        }

        hr = audioClient->GetMixFormat(&format);

        if (FAILED(hr)) {
            PrintHr(
                L"IAudioClient::GetMixFormat",
                hr);
            break;
        }

        // 保存当前默认输出设备的 ID。每次重连都会重新查询默认输出，
        // 如果设备发生变化，就重新建立 loopback capture。
        std::wstring deviceId;
        {
            LPWSTR rawId = nullptr;
            hr = device->GetId(&rawId);
            if (FAILED(hr)) {
                PrintHr(L"IMMDevice::GetId", hr);
                break;
            }
            if (rawId) {
                deviceId = rawId;
                CoTaskMemFree(rawId);
            }
        }

        SampleType sampleType = GetSampleType(format);

        if (sampleType == SampleType::UNSUPPORTED) {
            std::wcerr
                << L"Unsupported WASAPI sample format.\n";
            break;
        }

        std::wcout
            << L"Capture format: "
            << format->nSamplesPerSec
            << L" Hz, "
            << format->nChannels
            << L" ch, "
            << format->wBitsPerSample
            << L" bit, block="
            << format->nBlockAlign;

        if (format->wFormatTag == WAVE_FORMAT_PCM)
            std::wcout << L", PCM";
        else if (format->wFormatTag == WAVE_FORMAT_IEEE_FLOAT)
            std::wcout << L", IEEE float";
        else if (format->wFormatTag == WAVE_FORMAT_EXTENSIBLE)
            std::wcout << L", WAVE_FORMAT_EXTENSIBLE";

        std::wcout
            << L", source="
            << SampleTypeName(sampleType)
            << L"\n";

        std::wstring finalUrl =
            BuildAudioUrl(
                url,
                format->nSamplesPerSec,
                format->nChannels);

        if (finalUrl.empty())
            break;

        UrlParts finalParts;

        if (!CrackUrl(finalUrl, finalParts))
            break;

        // 当前实际使用的地址。302 时优先使用 Location；如果服务端只做 8080 -> 8880，
        // 也会自动切换到 8880。
        UrlParts activeParts = finalParts;

        if (!StartKeyboardHook())
            break;
        keyboardHookStarted = true;

        std::wcout
            << L"Output format: "
            << format->nSamplesPerSec
            << L" Hz, "
            << format->nChannels
            << L" ch, s16le\n";

        std::wcout
            << L"Streaming PCM to: "
            << finalUrl
            << L"\n";

        const auto closeHttp = [&]() {
            if (request) { WinHttpCloseHandle(request); request = nullptr; }
            if (connect) { WinHttpCloseHandle(connect); connect = nullptr; }
            if (session) { WinHttpCloseHandle(session); session = nullptr; }
        };

        const auto openHttp = [&]() -> bool {
            for (;;) {
                closeHttp();
                DWORD failureError = ERROR_SUCCESS;

                session = WinHttpOpen(
                    L"workdayAlarmClockGo/1.0", WINHTTP_ACCESS_TYPE_NO_PROXY,
                    WINHTTP_NO_PROXY_NAME, WINHTTP_NO_PROXY_BYPASS, 0);
                if (!session) {
                    failureError = GetLastError();
                    PrintWinError(L"WinHttpOpen", failureError);
                } else {
                    // 设置超时：Resolve、Connect、Send、Receive
                    WinHttpSetTimeouts(session, 5000, 5000, 5000, 5000);
                    connect = WinHttpConnect(
                        session,
                        activeParts.host.c_str(),
                        activeParts.port,
                        0);
                    if (!connect) {
                        failureError = GetLastError();
                        PrintWinError(L"WinHttpConnect", failureError);
                    } else {
                        request = WinHttpOpenRequest(
                            connect, L"PUT", activeParts.path.c_str(), nullptr,
                            WINHTTP_NO_REFERER, WINHTTP_DEFAULT_ACCEPT_TYPES,
                            finalParts.https ? WINHTTP_FLAG_SECURE : 0);
                        if (!request) {
                            failureError = GetLastError();
                            PrintWinError(L"WinHttpOpenRequest", failureError);
                        } else {
                            const wchar_t headers[] =
                                L"Content-Type: application/octet-stream\r\n"
                                L"Content-Length: 68719476735\r\n"
                                L"Expect: 100-continue\r\n";
                            if (WinHttpSendRequest(
                                    request, headers, static_cast<DWORD>(-1),
                                    WINHTTP_NO_REQUEST_DATA, 0,
                                    WINHTTP_IGNORE_REQUEST_TOTAL_LENGTH, 0)) {
                                return true;
                            }
                            failureError = GetLastError();
                            PrintWinError(L"WinHttpSendRequest", failureError);
                        }
                    }
                }
                closeHttp();
                if (IsConnectionFailure(failureError) &&
                    AdvancePortFallback(activeParts)) {
                    std::wcout
                        << L"Cannot connect; trying port "
                        << activeParts.port << L".\n";
                    continue;
                }
                return false;
            }
        };

        // 重连时只 Stop + Reset，不要在这里 Start。
        // 这样在等待网络/服务端恢复的这段时间里，WASAPI 不会继续产生
        // 捕获数据，避免 200 ms（或普通重连等待期间）产生新的积压。
        const auto stopAndFlushAudioCapture = [&]() -> bool {
            if (!audioClient)
                return false;

            hr = audioClient->Stop();
            if (FAILED(hr)) {
                PrintHr(L"IAudioClient::Stop(reconnect)", hr);
                return false;
            }

            hr = audioClient->Reset();
            if (FAILED(hr)) {
                PrintHr(L"IAudioClient::Reset(reconnect)", hr);
                return false;
            }
            ResetEvent(audioCaptureEvent);

            return true;
        };

        const auto startAudioCapture = [&]() -> bool {
            if (!audioClient)
                return false;

            ResetEvent(audioCaptureEvent);
            hr = audioClient->Start();
            if (FAILED(hr)) {
                PrintHr(L"IAudioClient::Start(reconnect)", hr);
                return false;
            }

            return true;
        };

        // 每次真正重连前重新读取默认输出设备。
        // 当前设备没变：保持已经 Stop+Reset 的状态，不再次启动。
        // 设备变了：完整释放旧 endpoint，并建立新的 loopback，但仍不 Start，
        // 等 HTTP 连接成功后再统一启动，这样重连等待期间绝不会积累音频。
        const auto refreshAudioDevice = [&]() -> bool {
            IMMDevice* currentDevice = nullptr;

            hr = enumerator->GetDefaultAudioEndpoint(
                eRender,
                eMultimedia,
                &currentDevice);

            if (FAILED(hr)) {
                PrintHr(L"GetDefaultAudioEndpoint(reconnect)", hr);
                return false;
            }

            LPWSTR rawId = nullptr;
            hr = currentDevice->GetId(&rawId);
            if (FAILED(hr)) {
                PrintHr(L"IMMDevice::GetId(reconnect)", hr);
                currentDevice->Release();
                return false;
            }

            std::wstring currentId = rawId ? rawId : L"";
            if (rawId)
                CoTaskMemFree(rawId);

            if (currentId == deviceId) {
                currentDevice->Release();
                return true;
            }

            std::wcout
                << L"Default audio output changed; switching capture device.\n";

            if (audioClient) {
                // 正常情况下这里应该已经 Stop；失败也不影响后面释放重建。
                audioClient->Stop();
            }

            if (captureClient) {
                captureClient->Release();
                captureClient = nullptr;
            }

            if (audioClient) {
                audioClient->Release();
                audioClient = nullptr;
            }

            if (device) {
                device->Release();
                device = nullptr;
            }

            if (format) {
                CoTaskMemFree(format);
                format = nullptr;
            }

            device = currentDevice;
            currentDevice = nullptr;
            deviceId = currentId;

            hr = device->Activate(
                __uuidof(IAudioClient),
                CLSCTX_ALL,
                nullptr,
                reinterpret_cast<void**>(&audioClient));

            if (FAILED(hr)) {
                PrintHr(L"IMMDevice::Activate(IAudioClient,reconnect)", hr);
                return false;
            }

            hr = audioClient->GetMixFormat(&format);
            if (FAILED(hr)) {
                PrintHr(L"IAudioClient::GetMixFormat(reconnect)", hr);
                return false;
            }

            sampleType = GetSampleType(format);
            if (sampleType == SampleType::UNSUPPORTED) {
                std::wcerr
                    << L"Unsupported WASAPI sample format after device switch.\n";
                return false;
            }

            finalUrl = BuildAudioUrl(
                url,
                format->nSamplesPerSec,
                format->nChannels);

            if (finalUrl.empty() || !CrackUrl(finalUrl, finalParts))
                return false;

            if (!InitializeLowLatencyLoopback(
                    device, &audioClient, format, audioCaptureEvent)) {
                return false;
            }

            UINT32 actualBufferFrames = 0;
            if (SUCCEEDED(audioClient->GetBufferSize(&actualBufferFrames)) &&
                format->nSamplesPerSec > 0) {
                std::wcout
                    << L"Actual capture buffer: "
                    << actualBufferFrames
                    << L" frames ("
                    << (actualBufferFrames * 1000ULL) /
                           format->nSamplesPerSec
                    << L" ms)\n";
            }

            hr = audioClient->GetService(
                __uuidof(IAudioCaptureClient),
                reinterpret_cast<void**>(&captureClient));

            if (FAILED(hr)) {
                PrintHr(
                    L"IAudioClient::GetService(IAudioCaptureClient,reconnect)",
                    hr);
                return false;
            }

            // 注意：这里故意不 Start。等 HTTP 真正连接成功后，由主循环统一 Start。
            return true;
        };

        if (!InitializeLowLatencyLoopback(
                device, &audioClient, format, audioCaptureEvent)) {
            break;
        }

        // 共享模式下申请值不一定被采纳，把真实缓冲大小打出来，
        // 这样才能知道这一项到底省下了多少延迟
        UINT32 actualBufferFrames = 0;

        if (SUCCEEDED(audioClient->GetBufferSize(&actualBufferFrames)) &&
            format->nSamplesPerSec > 0) {
            std::wcout
                << L"Actual capture buffer: "
                << actualBufferFrames
                << L" frames ("
                << (actualBufferFrames * 1000ULL) /
                       format->nSamplesPerSec
                << L" ms)\n";
        }

        hr = audioClient->GetService(
            __uuidof(IAudioCaptureClient),
            reinterpret_cast<void**>(&captureClient));

        if (FAILED(hr)) {
            PrintHr(
                L"IAudioClient::GetService(IAudioCaptureClient)",
                hr);
            break;
        }

        // 不在这里启动采集。
        // 首次 HTTP 连接成功后，由主循环统一 Start；这样启动阶段也不会
        // 在网络还没建立时产生无法发送的 WASAPI 积压。
        std::wcout
            << L"Press Enter to reconnect, Ctrl+C to stop.\n";

        ok = true;

        std::vector<int16_t> pcm16;
        const bool serviceMode = (argc >= 2);

        bool connected = false;
        bool streamConfirmed = false; // 已持续成功写出多块音频数据
        int successfulChunks = 0;
        int autoReconnectAttempts = 0;
        bool retryAfterDelay = false; // 普通断线：等 1 秒再重连
        bool serviceRetryDelay = false; // 开机启动模式：3 次失败后等 10 秒
        bool shortReconnectDelay = false; // 手动重连：等待 200 ms
        // 当前还需要从历史音频中跳过的旧帧总量。
        uint64_t dropFrames = 0;
        bool dropBacklogActive = false;

        // 丢弃粒度（1ms）对应的帧数。
        const uint64_t dropUnitFrames = std::max<uint64_t>(
            1,
            static_cast<uint64_t>(
                static_cast<double>(format->nSamplesPerSec) *
                kDropUnitMs / 1000.0));

        const auto clearCompensation = [&]() {
            dropFrames = 0;
            dropBacklogActive = false;
        };

        // 发送一段 PCM：转换 + 写入 + 计数。返回是否成功。
        const auto sendPcmSegment = [&](const BYTE* segmentData,
                                        UINT32 segmentFrames,
                                        DWORD flags) -> bool {
            const size_t sampleCount =
                static_cast<size_t>(segmentFrames) * format->nChannels;
            const DWORD outputBytes =
                static_cast<DWORD>(sampleCount * sizeof(int16_t));

            if (flags & AUDCLNT_BUFFERFLAGS_SILENT) {
                static BYTE zeroBuffer[64 * 1024]{};
                DWORD left = outputBytes;

                while (left > 0 && !g_stop.load()) {
                    DWORD chunk =
                        (left < static_cast<DWORD>(sizeof(zeroBuffer)))
                            ? left
                            : static_cast<DWORD>(sizeof(zeroBuffer));

                    if (!WritePcm(request, zeroBuffer, chunk))
                        return false;

                    ++successfulChunks;
                    if (!streamConfirmed && successfulChunks >= 3) {
                        streamConfirmed = true;
                        autoReconnectAttempts = 0;
                        serviceRetryDelay = false;
                        retryAfterDelay = false;
                        std::wcout << L"Connected. Audio data flowing.\n";
                    }

                    left -= chunk;
                }
                return true;
            }

            if (segmentData == nullptr || segmentFrames == 0)
                return true;

            if (!ConvertToS16(
                    segmentData,
                    segmentFrames,
                    format,
                    sampleType,
                    pcm16)) {
                std::wcerr << L"PCM conversion failed.\n";
                return false;
            }

            if (!WritePcm(
                    request,
                    reinterpret_cast<const BYTE*>(pcm16.data()),
                    outputBytes))
                return false;

            ++successfulChunks;
            if (!streamConfirmed && successfulChunks >= 3) {
                streamConfirmed = true;
                autoReconnectAttempts = 0;
                serviceRetryDelay = false;
                retryAfterDelay = false;
                std::wcout << L"Connected. Audio data flowing.\n";
            }
            return true;
        };

        while (!g_stop.load()) {
            HandlePendingVolumeRequests(activeParts);

            if (!connected) {
                if (serviceRetryDelay) {
                    SleepWhileHandlingVolumeRequests(
                        kServiceRetryDelay,
                        activeParts);
                } else if (retryAfterDelay) {
                    SleepWhileHandlingVolumeRequests(
                        std::chrono::seconds(1),
                        activeParts);
                } else if (shortReconnectDelay) {
                    // 200 ms 等待期间采集已经 Stop+Reset，因此不会产生新的音频积压。
                    SleepWhileHandlingVolumeRequests(
                        kCongestionReconnectDelay,
                        activeParts);
                }

                if (g_stop.load())
                    break;

                if (!refreshAudioDevice()) {
                    std::wcerr
                        << L"Audio capture reinitialization failed. Retrying in 1 second.\n";
                    retryAfterDelay = true;
                    shortReconnectDelay = false;
                    continue;
                }

                std::wcout << L"Connecting...\n";
                connected = openHttp();

                retryAfterDelay = false;
                shortReconnectDelay = false;

                if (!connected) {
                    ++autoReconnectAttempts;
                    if (serviceMode && serviceRetryDelay) {
                        // 已进入后台重试阶段：之后每次失败都固定等待 10 秒。
                        std::wcerr
                            << L"HTTP connect failed; retrying in 10 seconds.\n";
                        retryAfterDelay = false;
                        shortReconnectDelay = false;
                    } else if (autoReconnectAttempts < kMaxAutoReconnectAttempts) {
                        std::wcerr
                            << L"HTTP connect failed; retrying in 1 second (attempt "
                            << autoReconnectAttempts << L"/" << kMaxAutoReconnectAttempts << L")...\n";
                        retryAfterDelay = true;
                        shortReconnectDelay = false;
                    } else if (serviceMode) {
                        std::wcerr
                            << L"Reconnect failed 3 times; retrying in 10 seconds.\n";
                        retryAfterDelay = false;
                        serviceRetryDelay = true;
                        shortReconnectDelay = false;
                    } else {
                        std::wcerr
                            << L"Reconnect failed 3 times; press Enter to retry.\n";
                        retryAfterDelay = false;
                        shortReconnectDelay = false;
                        while (!g_stop.load()) {
                            HandlePendingVolumeRequests(activeParts);
                            if ((_kbhit() && _getch() == '\r') ||
                                g_reconnectRequested.exchange(false)) {
                                autoReconnectAttempts = 0;
                                shortReconnectDelay = true;
                                break;
                            }
                            std::this_thread::sleep_for(
                                std::chrono::milliseconds(50));
                        }
                    }
                    continue;
                }

                // HTTP 连接成功后才恢复采集。此前整个等待/重连过程都不会积累 WASAPI 数据。
                if (!startAudioCapture()) {
                    closeHttp();
                    connected = false;
                    ++autoReconnectAttempts;
                    if (serviceMode && serviceRetryDelay) {
                        retryAfterDelay = false;
                    } else {
                        retryAfterDelay = true;
                    }
                    ResetWriteStats();
                    continue;
                }

                ResetWriteStats();
                                streamConfirmed = false;
                                successfulChunks = 0;
                                clearCompensation();
                                std::wcout
                                    << L"HTTP connected; waiting for audio writes...\n";
            }

            const bool reconnectRequested =
                g_reconnectRequested.exchange(false);
            const bool consoleKeyAvailable = _kbhit() != 0;
            if (consoleKeyAvailable || reconnectRequested) {
                const int key = consoleKeyAvailable ? _getch() : 0;

                // Windows 控制台方向键：0/224 后跟具体键值，↑=72，↓=80。
                if (!reconnectRequested && (key == 0 || key == 224)) {
                    const int arrow = _getch();

                    if (arrow == 72) {
                        if (SendVolumeRequest(activeParts, L"/volp")) {
                            std::wcout << L"Volume up.\n";
                        }
                    } else if (arrow == 80) {
                        if (SendVolumeRequest(activeParts, L"/volm")) {
                            std::wcout << L"Volume down.\n";
                        }
                    }

                    continue;
                }

                if (key == '\r' || reconnectRequested) {
                    std::wcout << L"Reconnect requested; flushing capture and refreshing audio output device.\n";
                    closeHttp();
                    connected = false;
                    streamConfirmed = false;
                    successfulChunks = 0;
                    autoReconnectAttempts = 0;
                    retryAfterDelay = false;
                    serviceRetryDelay = false;
                    shortReconnectDelay = true;
                    clearCompensation();

                    // Stop+Reset 丢弃当前捕获积压，并给服务端时间释放旧连接。
                    if (!stopAndFlushAudioCapture()) {
                        std::wcerr
                            << L"Failed to flush audio capture; will rebuild it during reconnect.\n";
                    }

                    clearCompensation();
                    ResetWriteStats();
                    continue;
                }
            }

            // The event wakes immediately when loopback data is ready. A short
            // timeout keeps console controls responsive and polls as a fallback
            // on older Windows builds whose loopback events are not delivered.
            const DWORD audioWait = WaitForSingleObject(audioCaptureEvent, 5);
            if (audioWait == WAIT_FAILED) {
                PrintWinError(L"WaitForSingleObject(audio capture event)");
                connected = false;
                break;
            }

            UINT32 packetFrames = 0;

            hr = captureClient->GetNextPacketSize(
                &packetFrames);

            if (FAILED(hr)) {
                PrintHr(
                    L"IAudioCaptureClient::GetNextPacketSize",
                    hr);
                connected = false;
                break;
            }

            if (packetFrames == 0) {
                continue;
            }

            while (
                packetFrames > 0 &&
                !g_stop.load()) {

                BYTE* data = nullptr;
                UINT32 frames = 0;
                DWORD flags = 0;

                hr = captureClient->GetBuffer(
                    &data,
                    &frames,
                    &flags,
                    nullptr,
                    nullptr);

                if (FAILED(hr)) {
                    PrintHr(
                        L"IAudioCaptureClient::GetBuffer",
                        hr);
                    connected = false;
                    break;
                }

                // 每个分片进来时，如果还有欠账，按 kDropUnitMs 粒度交替“丢/留”，
                // 留的段累积到分片剩余大小后一次性发送；否则正常发送整个分片。
                UINT32 frameOffset = 0;

                if (dropFrames > 0) {
                    // 欠账太大时，直接丢弃整个分片，快速清掉旧音频。
                    const double backlogMs =
                        static_cast<double>(dropFrames) * 1000.0 /
                        static_cast<double>(format->nSamplesPerSec);
                    if (backlogMs >= kDropAllBacklogMs) {
                        dropFrames -= std::min<uint64_t>(
                            dropFrames,
                            static_cast<uint64_t>(frames));
                        if (dropFrames == 0 && dropBacklogActive) {
                            std::wcout << L"Drop backlog cleared.\n";
                            dropBacklogActive = false;
                        }
                        captureClient->ReleaseBuffer(frames);
                        if (!connected || g_stop.load())
                            break;
                        hr = captureClient->GetNextPacketSize(&packetFrames);
                        if (FAILED(hr)) {
                            PrintHr(L"IAudioCaptureClient::GetNextPacketSize", hr);
                            connected = false;
                            break;
                        }
                        continue;
                    }

                    // 本分片丢弃量 = min(分片一半, 剩余欠账)。
                    const uint64_t dropThisPacket = std::min<uint64_t>(
                        static_cast<uint64_t>(frames) / 2,
                        dropFrames);

                    // 按 kDropUnitMs 粒度交替丢/留，留的段累积到 sendTarget 再发。
                    std::vector<BYTE> sendAccum;
                    sendAccum.reserve(
                        static_cast<size_t>(frames) * format->nBlockAlign);
                    uint64_t sendAccumFrames = 0;
                    uint64_t dropped = 0;
                    bool dropNext = true;

                    while (frameOffset < frames && connected && !g_stop.load()) {
                        const UINT32 take = static_cast<UINT32>(
                            std::min<uint64_t>(
                                dropUnitFrames,
                                static_cast<uint64_t>(frames) - frameOffset));

                        if (dropNext && dropped < dropThisPacket) {
                            const UINT32 dropCount = static_cast<UINT32>(
                                std::min<uint64_t>(
                                    take,
                                    dropThisPacket - dropped));
                            dropped += dropCount;

                            const UINT32 sendCount = take - dropCount;
                            if (sendCount > 0 && data != nullptr) {
                                const UINT32 sendOffset = frameOffset + dropCount;
                                sendAccum.insert(
                                    sendAccum.end(),
                                    data + static_cast<size_t>(sendOffset) * format->nBlockAlign,
                                    data + static_cast<size_t>(frameOffset + take) * format->nBlockAlign);
                            }
                            sendAccumFrames += sendCount;
                        } else {
                            // 留这段：累积到 sendAccum。
                            if (data != nullptr) {
                                sendAccum.insert(
                                    sendAccum.end(),
                                    data + static_cast<size_t>(frameOffset) * format->nBlockAlign,
                                    data + static_cast<size_t>(frameOffset + take) * format->nBlockAlign);
                            }
                            sendAccumFrames += take;
                        }

                        frameOffset += take;
                        dropNext = !dropNext;
                    }

                    dropFrames -= dropped;

                    // 发送累积的留段。
                    if (connected && sendAccumFrames > 0) {
                        if (!sendPcmSegment(
                                sendAccum.data(),
                                static_cast<UINT32>(sendAccumFrames),
                                flags)) {
                            connected = false;
                        }
                    }

                    if (dropFrames == 0 && dropBacklogActive) {
                        std::wcout << L"Drop backlog cleared.\n";
                        dropBacklogActive = false;
                    }
                } else {
                    // 无欠账，正常发送整个分片。
                    if (!sendPcmSegment(data, frames, flags))
                        connected = false;
                }

                captureClient->ReleaseBuffer(frames);

                if (!connected || g_stop.load())
                    break;

                // 连续 PCM body 的写入累计达到阈值时，不断开连接。
                // 把 WriteData 耗时转换成历史音频欠账
                if (g_blockedMs >= kDropBacklogMs) {
                    const double dropMs = g_blockedMs;

                    const uint64_t newDropFrames =
                        static_cast<uint64_t>(
                            static_cast<double>(format->nSamplesPerSec) *
                            dropMs / 1000.0);

                    dropFrames += newDropFrames;
                    dropBacklogActive = true;

                    const double backlogMs =
                        static_cast<double>(dropFrames) * 1000.0 /
                        static_cast<double>(format->nSamplesPerSec);

                    const bool dropAll =
                        backlogMs >= kDropAllBacklogMs;

                    const double averageWriteMs =
                        g_writeCalls > 0
                            ? dropMs / static_cast<double>(g_writeCalls)
                            : 0.0;

                    std::wcout
                        << L"Network congested (writes blocked "
                        << static_cast<long long>(dropMs)
                        << L" ms); queued "
                        << static_cast<long long>(backlogMs)
                        << L" ms; calculated "
                        << (dropAll
                                ? L"full drop of old audio."
                                : L"1ms interleaved drop/send.")
                        << L"; WriteData calls="
                        << g_writeCalls
                        << L", avg="
                        << averageWriteMs
                        << L" ms, max="
                        << g_writeMaxMs
                        << L" ms, >=1ms="
                        << g_writeOver1MsCalls
                        << L"\n";

                    ResetWriteStats();
                }

                hr = captureClient->GetNextPacketSize(
                    &packetFrames);

                if (FAILED(hr)) {
                    PrintHr(
                        L"IAudioCaptureClient::GetNextPacketSize",
                        hr);
                    connected = false;
                    break;
                }
            }

            if (!connected && !g_stop.load()) {
                DWORD httpStatus = 0;
                std::string responseBody;
                std::wstring location;
                bool portFallbackApplied = false;

                // WinHttpWriteData 失败时，服务端可能已经返回 404/500/302。
                // 尝试把响应读出来，至少把状态码和 JSON 错误打印给用户。
                if (request) {
                    if (ReadHttpResponse(request, httpStatus, responseBody, location)) {
                        PrintHttpResponse(httpStatus, responseBody, location);

                        // 302/301/307/308：优先跟随 Location。对于常见的
                        // 8080 -> 8880 重定向，即使 Location 没拿到，也走 8880。
                        if (httpStatus >= 300 && httpStatus < 400) {
                            UrlParts redirected;
                            bool redirectedOk =
                                !location.empty() &&
                                CrackUrl(location, redirected);

                            if (redirectedOk) {
                                SetQueryParameter(
                                    redirected.path, L"rate",
                                    std::to_wstring(format->nSamplesPerSec));
                                SetQueryParameter(
                                    redirected.path, L"channels",
                                    std::to_wstring(format->nChannels));
                                activeParts = redirected;
                                std::wcout
                                    << L"Following HTTP redirect to "
                                    << (activeParts.https ? L"https://" : L"http://")
                                    << activeParts.host << L":" << activeParts.port
                                    << activeParts.path << L"\n";
                            } else if (AdvancePortFallback(activeParts)) {
                                portFallbackApplied = true;
                                std::wcout
                                    << L"HTTP redirect detected; trying port "
                                    << activeParts.port << L".\n";
                            }
                        }
                    }
                }

                if (!portFallbackApplied &&
                    IsConnectionFailure(g_lastWinHttpError) &&
                    AdvancePortFallback(activeParts)) {
                    std::wcout
                        << L"WinHTTP connection error; trying port "
                        << activeParts.port << L".\n";
                }

                closeHttp();
                stopAndFlushAudioCapture();
                dropFrames = 0;
                dropBacklogActive = false;
                                streamConfirmed = false;

                ++autoReconnectAttempts;

                if (serviceMode && serviceRetryDelay) {
                    // 已进入后台重试阶段：之后每次失败都固定等待 10 秒。
                    std::wcerr
                        << L"Connection interrupted; capture stopped, retrying in 10 seconds.\n";
                    retryAfterDelay = false;
                    shortReconnectDelay = false;
                } else if (autoReconnectAttempts < kMaxAutoReconnectAttempts) {
                    std::wcerr
                        << L"Connection interrupted; capture stopped, retrying in 1 second (attempt "
                        << autoReconnectAttempts << L"/" << kMaxAutoReconnectAttempts << L").\n";
                    retryAfterDelay = true;
                    shortReconnectDelay = false;
                } else if (serviceMode) {
                    std::wcerr
                        << L"Reconnect failed 3 times; retrying automatically in 10 seconds.\n";
                    retryAfterDelay = false;
                    serviceRetryDelay = true;
                    shortReconnectDelay = false;
                } else {
                    std::wcerr
                        << L"Reconnect failed 3 times; press Enter to retry.\n";
                    retryAfterDelay = false;
                    serviceRetryDelay = false;
                    shortReconnectDelay = false;

                    while (!g_stop.load()) {
                        HandlePendingVolumeRequests(activeParts);
                        if ((_kbhit() && _getch() == '\r') ||
                            g_reconnectRequested.exchange(false)) {
                            autoReconnectAttempts = 0;
                            shortReconnectDelay = true;
                            break;
                        }
                        std::this_thread::sleep_for(
                            std::chrono::milliseconds(50));
                    }
                }
            }
        }

        audioClient->Stop();

        // 连续 PCM body 使用长 Content-Length，不发送 chunk 结束标记。
        // 停止/重连时直接关闭请求，服务端会结束当前 body。
        closeHttp();

    } while (false);

    if (keyboardHookStarted)
        StopKeyboardHook();

    if (format)
        CoTaskMemFree(format);

    if (captureClient)
        captureClient->Release();

    if (audioClient)
        audioClient->Release();

    if (device)
        device->Release();

    if (enumerator)
        enumerator->Release();

    if (request)
        WinHttpCloseHandle(request);

    if (audioCaptureEvent)
        CloseHandle(audioCaptureEvent);

    if (connect)
        WinHttpCloseHandle(connect);

    if (session)
        WinHttpCloseHandle(session);

    CoUninitialize();

    SetConsoleCtrlHandler(
        ConsoleHandler,
        FALSE);

    return ok ? 0 : 1;
}

#include <windows.h>
#include <winnt.h>

#include "utils.h"
#include "platform.h"

struct win32_offscreen_buffer
{
    // NOTE: pixels are 32-bit wide, memory order "BB GG RR XX"
    BITMAPINFO info;
    void       *memory;
    s32        width;
    s32        height;
    s32        pitch;
    s32        bytes_per_pixel;
};

global_variable win32_offscreen_buffer globalBackBuffer;
global_variable b32 globalRunning;
global_variable s64 globalPerfCountFrequency;

struct win32_window_dimension
{
    int width;
    int height;
};

internal win32_window_dimension
win32GetWindowDimension(HWND window)
{
    win32_window_dimension result;
    RECT client_rect;
    GetClientRect(window, &client_rect);
    result.width  = client_rect.right - client_rect.left;
    result.height = client_rect.bottom - client_rect.top;
    return(result);
}

internal void
win32DisplayBufferInWindow(win32_offscreen_buffer *buffer, HDC window_dc,
                           int window_width, int window_height)
{
    int offsetX = 10;
    int offsetY = 10;

    // NOTE: Clear the gutter area that we don't draw to, while avoiding clearing the game content
    // in-between frame flips
    PatBlt(window_dc, 0, 0, window_width, offsetY, BLACKNESS);
    PatBlt(window_dc, 0, 0, offsetX, window_height, BLACKNESS);
    PatBlt(window_dc, offsetX, offsetY+buffer->height, window_width, window_height, BLACKNESS);
    PatBlt(window_dc, offsetX+buffer->width, 0, window_width, window_height, BLACKNESS);

    // TODO: Aspect ratio correction
    StretchDIBits(window_dc,
                  offsetX, offsetY, buffer->width, buffer->height,
                  0, 0, buffer->width, buffer->height,
                  buffer->memory, &buffer->info,
                  DIB_RGB_COLORS, SRCCOPY);
}

inline u32
SafeTruncateUInt64(u64 Value)
{
    assert(Value <= 0XFFFFFFFF);
    return (u32)Value;
}

inline void
win32FreeFileMemory(void *memory)
{
    if (memory)
        VirtualFree(memory, 0, MEM_RELEASE);
}

inline ReadFileResult
win32ReadEntireFile(const char *file_name)
{
    ReadFileResult result = {};

    HANDLE fileHandle = CreateFileA(file_name, GENERIC_READ, FILE_SHARE_READ, 0, OPEN_EXISTING, 0, 0);
    if (fileHandle != INVALID_HANDLE_VALUE)
    {
        LARGE_INTEGER fileSize;
        if (GetFileSizeEx(fileHandle, &fileSize))
        {
            u32 fileSize32 = SafeTruncateUInt64((u64)fileSize.QuadPart);
            result.content = (char *)VirtualAlloc(0, fileSize32, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
            if (result.content)
            {
                DWORD bytesRead;
                if (ReadFile(fileHandle, result.content, fileSize32, &bytesRead, 0)
                    && (fileSize32 == bytesRead))
                {
                    // File read successfully
                    result.content_size = fileSize32;
                }
                else
                    win32FreeFileMemory(result.content);
            }
            else
            {
                todoErrorReport;
            }
        }
        CloseHandle(fileHandle);
    }
    else
    {
        // TODO: Report error
    }

    return result;
}

internal LRESULT CALLBACK
win32MainWindowCallback(HWND   window,
                        UINT   message,
                        WPARAM w_param,
                        LPARAM l_param)
{
    LRESULT result = 0;
    switch (message)
    {
        case WM_CLOSE:
        {
            globalRunning = false;
        } break;

        case WM_PAINT:
        {
            PAINTSTRUCT paint;
            HDC dc = BeginPaint(window, &paint);

            win32_window_dimension win_dim = win32GetWindowDimension(window);
            win32DisplayBufferInWindow(&globalBackBuffer,
                                       dc,
                                       win_dim.width,
                                       win_dim.height);
            EndPaint(window, &paint);
        } break;

        default:
        {
            result = DefWindowProcA(window, message, w_param, l_param);
        } break;
    }
    return result;
}

internal void
win32ProcessPendingMessages()
{
    MSG message;
    while (PeekMessageA(&message, 0, 0, 0, PM_REMOVE))
    {
        switch (message.message)
        {
            case WM_QUIT:
            {
                globalRunning = false;
            } break;

            default:
            {
                TranslateMessage(&message);
                DispatchMessage(&message);
            }
        }
    }
}

inline LARGE_INTEGER
win32GetWallClock(void)
{
    LARGE_INTEGER result;
    QueryPerformanceCounter(&result);
    return result;
}

inline void *
platformGetWallClock(MemoryArena *arena)
{
    auto out = pushStruct(arena, LARGE_INTEGER);
    *out = win32GetWallClock();
    return (void *)out;
}

// The two inputs come from "QueryPerformanceCounter"
inline r32
win32GetSecondsElapsed(LARGE_INTEGER start, LARGE_INTEGER end)
{
    r32 result = ((r32)(end.QuadPart - start.QuadPart)
                  / (r32)globalPerfCountFrequency);
    return result;
}

inline r32
platformGetSecondsElapsed(void *start_, void *end_)
{
    auto start = (LARGE_INTEGER *)start_;
    auto end   = (LARGE_INTEGER *)end_;
    return win32GetSecondsElapsed(*start, *end);
}

internal void
testDraw(win32_offscreen_buffer *buffer)
{
    u8 *row = (u8 *)buffer->memory;
    u32 color = 0x00555555;
    for (s32 y = 0;
         y < buffer->height;
         y++)
    {
        u32 *pixel = (u32 *)row;
        for (s32 x = 0;
             x < buffer->width;
             x++)
        {
            *pixel++ = color;
        }
        row += buffer->pitch;
    }
}

// NOTE: Initialize the buffer to a resize.
internal void
win32ResizeDIBSection(win32_offscreen_buffer *buffer, int width, int height)
{
    if(buffer->memory)
        VirtualFree(buffer->memory, 0, MEM_RELEASE);

    buffer->width = width;
    buffer->height = height;
    buffer->info.bmiHeader.biSize = sizeof(buffer->info.bmiHeader);
    buffer->info.bmiHeader.biWidth = width;
    // NOTE: When height is negative, it prompts Windows to treat this bitmap
    // as top-down, not botton-up.
    buffer->info.bmiHeader.biHeight = height;
    buffer->info.bmiHeader.biPlanes = 1;
    buffer->info.bmiHeader.biBitCount = 32;
    buffer->info.bmiHeader.biCompression = BI_RGB;

    buffer->bytes_per_pixel = 4;
    int bitmapMemorySize = (width*height)*buffer->bytes_per_pixel;
    buffer->memory = VirtualAlloc(0, (u32)bitmapMemorySize, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);

    buffer->pitch = width*buffer->bytes_per_pixel;
}

#if 0
s32 CALLBACK
WinMain(HINSTANCE instance,
        HINSTANCE prev_instance,
        LPSTR     cmd_line,
        int       show_code)
{
    (void)prev_instance; (void)cmd_line; (void)show_code;
    WNDCLASSA window_class = {};
    window_class.style = CS_HREDRAW|CS_VREDRAW;
    window_class.lpfnWndProc = win32MainWindowCallback;
    window_class.hInstance = instance;
    window_class.hCursor = LoadCursor(0, IDC_ARROW);
    window_class.lpszClassName = "ReasoningEngineWindowClass";

    LARGE_INTEGER perfCountFrequencyResult;
    QueryPerformanceFrequency(&perfCountFrequencyResult);
    globalPerfCountFrequency = perfCountFrequencyResult.QuadPart;

    win32ResizeDIBSection(&globalBackBuffer, 1920, 1080);

    if (RegisterClassA(&window_class))
    {
        HWND window = CreateWindowExA(
            0, window_class.lpszClassName,
            "Reasoning Engine",
            WS_OVERLAPPEDWINDOW | WS_VISIBLE,
            CW_USEDEFAULT, CW_USEDEFAULT,
            CW_USEDEFAULT, CW_USEDEFAULT,
            0, 0, instance, 0);
        if (window)
        {
            globalRunning = true;
            LARGE_INTEGER last_counter = win32GetWallClock();
            r32 editor_update_hz = 4.0f;
            r32 target_seconds_per_frame = 1.0f / editor_update_hz;
            while (globalRunning)
            {
                win32ProcessPendingMessages();

                testDraw(&globalBackBuffer);

                LARGE_INTEGER work_counter = win32GetWallClock();
                r32 seconds_elapsed_for_frame = win32GetSecondsElapsed(last_counter, work_counter);
                if (seconds_elapsed_for_frame < target_seconds_per_frame)
                {
                    DWORD sleep_ms = (DWORD)1000*(target_seconds_per_frame - seconds_elapsed_for_frame);
                    Sleep(sleep_ms);
                }
                HDC window_dc = GetDC(window);
                win32_window_dimension win_dim = win32GetWindowDimension(window);
                HDC device_context = GetDC(window);
                win32DisplayBufferInWindow(&globalBackBuffer,
                                           window_dc,
                                           win_dim.width,
                                           win_dim.height);
                ReleaseDC(window, window_dc);
                last_counter = win32GetWallClock();
            }
        }
    }
    else
    {
        // TODO: error handling.
    }
    return 0;
}
#endif

#include <stdio.h>
int main()
{
    int code = 0;

    LARGE_INTEGER perfCountFrequencyResult;
    QueryPerformanceFrequency(&perfCountFrequencyResult);
    globalPerfCountFrequency = perfCountFrequencyResult.QuadPart;

    EngineMemory engine_memory;
    engine_memory.platformPrint = &OutputDebugStringA;
    engine_memory.platformReadEntireFile = &win32ReadEntireFile;
    engine_memory.platformFreeFileMemory = &win32FreeFileMemory;
    engine_memory.platformGetWallClock      = &platformGetWallClock;
    engine_memory.platformGetSecondsElapsed = &platformGetSecondsElapsed;
    engine_memory.storage_size = megaBytes(256);
    LPVOID base_address = (LPVOID)teraBytes(2);
    engine_memory.storage = VirtualAlloc(base_address, engine_memory.storage_size,
                                         MEM_RESERVE|MEM_COMMIT,
                                         PAGE_READWRITE);

    if (!engineMain(&engine_memory))
        code = 1;

    return code;
}

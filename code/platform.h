#if !defined(PLATFORM_H)

#include "utils.h"
#include "memory.h"

struct ReadFileResult
{
    u32 content_size;
    char *content;
};

typedef void PlatformPrint(const char *string);
typedef ReadFileResult PlatformReadEntireFile(const char *file_name);
typedef void PlatformFreeFileMemory(void *memory);
typedef void *PlatformGetWallClock(MemoryArena *arena);
typedef r32 PlatformGetSecondsElapsed(void *start, void *end);

struct EngineMemory
{
    PlatformPrint             *platformPrint;
    PlatformReadEntireFile    *platformReadEntireFile;
    PlatformFreeFileMemory    *platformFreeFileMemory;
    PlatformGetWallClock      *platformGetWallClock;
    PlatformGetSecondsElapsed *platformGetSecondsElapsed;

    void* storage;
    size_t storage_size;
};

int
engineMain(EngineMemory *memory);

#define PLATFORM_H
#endif

#if !defined(PLATFORM_H)

#include "utils.h"

struct ReadFileResult
{
    u32 contentsSize;
    void *contents;
};

typedef ReadFileResult PlatformReadEntireFile(const char *file_name);
typedef void PlatformFreeFileMemory(void *memory);
typedef void PlatformPrint(const char *string);

struct EngineMemory
{
    b32 initialized;
    PlatformReadEntireFile *platformReadEntireFile;
    PlatformFreeFileMemory *platformFreeFileMemory;
    PlatformPrint *platformPrint;
    void* storage;
    memory_index storage_size;
};

#define PLATFORM_H
#endif

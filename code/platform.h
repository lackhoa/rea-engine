#if !defined(PLATFORM_H)

#include "utils.h"

struct ReadFileResult
{
    u32 content_size;
    void *content;
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
    size_t storage_size;
};

#define PLATFORM_H
#endif

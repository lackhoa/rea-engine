#if !defined(PLATFORM_H)

#include "utils.h"

struct ReadFileResult
{
    u32 content_size;
    char *content;
};

typedef ReadFileResult PlatformReadEntireFile(const char *file_name);
typedef void PlatformFreeFileMemory(void *memory);
typedef void PlatformPrint(const char *string);

struct EngineMemory
{
    PlatformReadEntireFile *platformReadEntireFile;
    PlatformFreeFileMemory *platformFreeFileMemory;
    PlatformPrint *platformPrint;
    void* storage;
    size_t storage_size;
};

int
engineMain(EngineMemory *memory);

#define PLATFORM_H
#endif

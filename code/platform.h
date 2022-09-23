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
    PlatformReadEntireFile *platformReadEntireFile;
    PlatformFreeFileMemory *platformFreeFileMemory;
    PlatformPrint *platformPrint;
    void* storage;  // IMPORTANT: Required to be cleared to zero at startup.
    size_t storage_size;
};

#define PLATFORM_H
#endif

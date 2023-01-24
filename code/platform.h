#pragma once
#include "utils.h"
#include "memory.h"

//
// Platform -> Engine
//

struct ReadFileResult
{
    u32 content_size;
    char *content;
};
ReadFileResult platformReadEntireFile(const char *file_name);

void platformPrint(const char *string);
void platformFreeFileMemory(void *memory);
void *platformGetWallClock(Arena *arena);
r32 platformGetSecondsElapsed(void *start, void *end);

struct FilePath
{
    char   *path;
    String  directory;
    char   *file;
};
FilePath platformGetFileFullPath(Arena* arena, char *file);

#if 0
struct EngineMemory
{
    void* storage;
    size_t storage_size;
};
#endif

void *platformVirtualAlloc(void *base_address, size_t size);

//
// Engine -> Platform
//
int
engineMain();

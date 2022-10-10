#if !defined(PLATFORM_H)

#include "utils.h"
#include "memory.h"

struct ReadFileResult
{
    u32 content_size;
    char *content;
};
ReadFileResult platformReadEntireFile(const char *file_name);

void platformPrint(const char *string);
void platformFreeFileMemory(void *memory);
void *platformGetWallClock(MemoryArena *arena);
r32 platformGetSecondsElapsed(void *start, void *end);

struct FilePath
{
    char   *path;
    String  directory;
    char   *file;
};
FilePath platformGetFileFullPath(MemoryArena* arena, char *file);

struct EngineMemory
{
    void* storage;
    size_t storage_size;
};

int
engineMain(EngineMemory *memory);

#define PLATFORM_H
#endif

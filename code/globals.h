#if !defined(GLOBALS_H)

#include "platform.h"
#include "memory.h"

PlatformPrint *platformPrint;
MemoryArena *global_arena;
PlatformReadEntireFile *platformReadEntireFile;
PlatformFreeFileMemory *platformFreeFileMemory;

#define GLOBALS_H
#endif

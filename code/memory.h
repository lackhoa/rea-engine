#if !defined(MEMORY_H)

#include "utils.h"

inline void
zeroSize(void *base, memory_index size)
{
    u8 *ptr = (u8 *) base;
    while(size--)
        *ptr++ = 0;
}

#define zeroStruct(base, type) zeroSize(base, sizeof(type));
#define zeroOut(base) zeroSize(base, sizeof(base))

struct Memory_arena
{
    memory_index cap;
    u8 *base;
    memory_index used;
};

inline void *
pushSize(Memory_arena *arena, memory_index size)
{
    assert((arena->used + size) <= arena->cap);
    void *result = arena->base + arena->used;
    arena->used += size;
    return(result);
}

#define pushStruct(arena, type) (type *) pushSize(arena, sizeof(type))
#define pushArray(arena, count, type) (type *) pushSize(arena, count*sizeof(type))

inline Memory_arena
newArena(memory_index size, void *base)
{
    Memory_arena arena;
    arena.cap = size;
    arena.base = (u8 *)base;
    arena.used = 0;
    return arena;
}

#define MEMORY_H
#endif

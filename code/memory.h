#if !defined(MEMORY_H)

#include "utils.h"

inline void
zeroSize(void *base, size_t size)
{
    u8 *ptr = (u8 *) base;
    while(size--)
        *ptr++ = 0;
}

#define zeroStruct(base, type) zeroSize(base, sizeof(type));
#define zeroOut(base) zeroSize(base, sizeof(base))

struct MemoryArena
{
    size_t cap;
    u8 *base;
    size_t used;
};

inline void *
pushSize(MemoryArena *arena, size_t size, b32 zero = false)
{
    assert((arena->used + size) <= arena->cap);
    void *result = arena->base + arena->used;
    arena->used += size;
    if (zero)
        zeroSize(result, size);
    return(result);
}

#define pushStruct(arena, type) (type *) pushSize(arena, sizeof(type))
#define pushStructZero(arena, type) (type *) pushSize(arena, sizeof(type), true)
#define pushArray(arena, count, type) (type *) pushSize(arena, count*sizeof(type))

inline MemoryArena
newArena(size_t size, void *base)
{
    MemoryArena arena;
    arena.cap = size;
    arena.base = (u8 *)base;
    arena.used = 0;
    return arena;
}

#define MEMORY_H
#endif

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

inline MemoryArena
subArena(MemoryArena *parent, size_t size)
{
    MemoryArena result;
    result.base = (u8 *)pushSize(parent, size);
    result.cap = size;
    result.used = 0;
    return result;
}

inline void
endTemporaryArena(MemoryArena *parent, MemoryArena *child)
{
    parent->used -= child->cap;
}

#define allocate(arena, x) x = (__typeof__(x)) pushSize(arena, sizeof(*x))

#define MEMORY_H
#endif

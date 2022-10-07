#if !defined(MEMORY_H)

#include "utils.h"
#include "intrinsics.h"

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
    u8     *base;
    size_t  used;
    size_t  cap;

    MemoryArena *parent;
};

inline MemoryArena
newArena(size_t cap, void *base)
{
    MemoryArena arena = {};
    arena.cap = cap;
    arena.base = (u8 *)base;
    return arena;
}

inline void *
pushSize(MemoryArena *arena, size_t size, b32 zero = false)
{
    void *out = (arena->base + arena->used);
    arena->used += size;
    assert(arena->used <= arena->cap);
    if (zero)
        zeroSize(out, size);
    return(out);
}

#define pushStruct(arena, type) (type *) pushSize(arena, sizeof(type))
#define pushStructZero(arena, type) (type *) pushSize(arena, sizeof(type), true)
#define pushArray(arena, count, type) (type *) pushSize(arena, count*sizeof(type))

inline MemoryArena
subArena(MemoryArena *parent, size_t size)
{
    MemoryArena result = {};
    result.base = (u8 *)pushSize(parent, size);
    result.cap = size;
    result.parent = parent;
    return result;
}

struct TemporaryMemory
{
    MemoryArena *arena;
    size_t       original_used;
};

inline MemoryArena 
beginTemporaryArena(MemoryArena *parent)
{
    MemoryArena out = subArena(parent, parent->cap - parent->used);
    assert(parent->used == parent->cap);
    return out;
}

inline void
zeroArena(MemoryArena *arena)
{
    zeroMemory(arena->base, arena->used);
}

inline void
endTemporaryArena(MemoryArena *child, b32 zero = false)
{
    if (zero)
        zeroMemory(child->base, child->used);

    auto parent = child->parent;
    assert(parent->used == parent->cap);
    assert(child->cap <= parent->cap);
    parent->used -= child->cap;
}

#define allocate(arena, x) x = (__typeof__(x)) pushSize(arena, sizeof(*x))
#define allocateArray(arena, count, x) x = (__typeof__(x)) pushSize(arena, count*sizeof(*x))

#define MEMORY_H
#endif

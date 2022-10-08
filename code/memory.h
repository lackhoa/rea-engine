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

    s32 temp_count;
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
    result.cap  = size;
    return result;
}

struct TemporaryMemory
{
    MemoryArena *arena;
    size_t       original_used;
};

inline TemporaryMemory
beginTemporaryMemory(MemoryArena *arena)
{
    TemporaryMemory out = {};
    out.arena         = arena;
    out.original_used = arena->used;
    arena->temp_count++;
    return out;
}

inline void
endTemporaryMemory(TemporaryMemory temp)
{
    temp.arena->temp_count--;
    assert(temp.arena->used >= temp.original_used);
    temp.arena->used = temp.original_used;
}

inline void
checkArena(MemoryArena *arena)
{
    assert(arena->temp_count == 0);
}

inline void
resetZeroArena(MemoryArena *arena)
{
    arena->used = 0;
    zeroMemory(arena->base, arena->cap);
}

#if COMPILER_MSVC
#    define mytypeof decltype
#else
#    define mytypeof __typeof__
#endif

#define allocate(arena, x) x = (mytypeof(x)) pushSize(arena, sizeof(*x))
#define allocateArray(arena, count, x) x = (mytypeof(x)) pushSize(arena, count*sizeof(*x))

#define MEMORY_H
#endif

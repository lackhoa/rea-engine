#pragma once

#include <cstdint>
#include <ctype.h>
#include <stdio.h>

//
// Compilers
//

#if __llvm__
#    undef COMPILER_LLVM
#    define COMPILER_LLVM 1
#else
#    undef COMPILER_MSVC
#    define COMPILER_MSVC 1
#endif


#define internal static
#define global_variable static

typedef uint8_t  u8;
typedef uint16_t u16;
typedef int32_t  s32;
typedef int32_t  b32;
typedef uint32_t u32;
typedef uint64_t u64;

typedef float    r32;
typedef long     s64;

#define kiloBytes(value) ((value)*1024LL)
#define megaBytes(value) (kiloBytes(value)*1024LL)
#define gigaBytes(value) (megaBytes(value)*1024LL)
#define teraBytes(value) (gigaBytes(value)*1024LL)

#define arrayCount(array) (sizeof(array) / sizeof((array)[0]))

#if REA_INTERNAL
#  if COMPILER_MSVC
#    define assert(claim) if (!(claim)) { fflush(stdout); __debugbreak(); }
#  else
#    define assert(claim) if (!(claim)) { fflush(stdout); __builtin_trap(); }
#  endif
#else
#  define assert(claim)
#endif

#define invalidCodePath assert(false)
#define todoErrorReport assert(false)
#define todoIncomplete  assert(false)
#define invalidDefaultCase default: { assert(false) };
#define breakhere  { int x = 5; (void)x; }

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

inline u8 *
getNext(MemoryArena *arena)
{
    u8 *out = arena->base + arena->used;
    return out;
}

inline size_t
getArenaFree(MemoryArena *arena)
{
    size_t out = arena->cap - arena->used;
    return out;
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

#define pushStruct(arena, type, ...) (type *) pushSize(arena, sizeof(type), __VA_ARGS__)
#define pushArray(arena, count, type, ...) (type *) pushSize(arena, count*sizeof(type), __VA_ARGS__)
#define allocate(arena, x, ...) x = (mytypeof(x)) pushSize(arena, sizeof(*x), __VA_ARGS__)
#define allocateArray(arena, count, x, ...) x = (mytypeof(x)) pushSize(arena, count*sizeof(*x), __VA_ARGS__)

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

inline void *
copySize(MemoryArena *arena, void *src, size_t size)
{
  void *dst = pushSize(arena, size);
  copyMemory(dst, src, size);
  return dst;
}

#if COMPILER_MSVC
#    define mytypeof decltype
#else
#    define mytypeof __typeof__
#endif

#define copyStruct(arena, src) (mytypeof(src)) copySize(arena, src, sizeof(*(src)))
#define copyStructNoCast(arena, src) copySize(arena, src, sizeof(*(src)))
#define copyArray(arena, count, src) (mytypeof(src)) copySize(arena, src, count*sizeof(*(src)))

inline b32
inRange(s32 min, s32 val, s32 max)
{
    return (min <= val) && (val <= max);
}

struct String
{
    char *chars;
    s32   length;               // note: does not include the nil terminator
};

inline s32
stringLength(char *string)
{
    s32 out = 0;
    char *c = string;
    while (*c)
    {
        out++;
        c++;
    }
    return out;
}

inline b32
equal(String s, const char *cstring)
{
    if (!s.chars)
    {
        return false;
    }
    else
    {
        s32 at = 0;
        for (;
             (at < s.length);
             at++)
        {
            if ((cstring[at] == 0) || (s.chars[at] != cstring[at]))
            {
                return false;
            }
        }
        return (cstring[at] == 0);
    }
}

inline b32
equal(String a, String b)
{
    b32 out = true;
    if (a.length != b.length)
        out = false;
    else
    {
        for (int i = 0; i < a.length; i++)
        {
            if (a.chars[i] != b.chars[i])
            {
                out = false;
                break;
            }
        }
    }
    return out;
}

inline String
toString(const char *c)
{
    String out;
    out.chars  = (char*)c;
    out.length = 0;
    while (*c)
    {
        out.length++;
        c++;
    }
    return out;
}

inline b32
equal(char *s1, char *s2)
{
    b32 out = true;
    char *c1 = s1;
    char *c2 = s2;
    b32 stop = false;
    while (!stop)
    {
        if (*c1 != *c2)
        {
            out = false;
            stop = true;
        }
        else
        {
            if (*c1 == 0)
                stop = true;
            else
            {
                c1++;
                c2++;
            }
        }
    }
    return out;
}

internal void
printToBufferVA(MemoryArena *buffer, char *format, va_list arg_list)
{
    char *at = (char *)getNext(buffer);
    auto printed = vsprintf_s(at, (buffer->cap - buffer->used), format, arg_list);
    buffer->used += printed;
}

internal char *
printToBuffer(MemoryArena *buffer, char *format, ...)
{
  char *out = 0;

   va_list arg_list;
  __crt_va_start(arg_list, format);

  if (buffer)
  {
    out = (char *)getNext(buffer);
    char *at = out;
    auto printed = vsprintf_s(at, (buffer->cap-1 - buffer->used), format, arg_list);
    buffer->used += printed;
    buffer->base[buffer->used] = 0; // nil-termination
  }
  else
    vprintf_s(format, arg_list);

  __crt_va_end(arg_list);

  return out;
}

inline char *
printToBuffer(MemoryArena *buffer, String s)
{
  char *out = 0;
  if (buffer)
  {
    out = (char *)getNext(buffer);
    char *at = out;
    const char *c = s.chars;
    for (s32 index = 0; index < s.length; index++)
      *at++ = *c++;
    *at = 0;
    buffer->used = at - (char *)buffer->base;
    assert(buffer->used <= buffer->cap);
  }
  else
    printf("%.*s", s.length, s.chars);

  return out;
}

#if 0
inline char *
printToBuffer(MemoryArena *buffer, char *s)
{
  char *out = 0;
  if (buffer)
  {
    out = (char *)getNext(buffer);
    char *at = out;
    const char *c = s;
    for (s32 index = 0; *c; index++)
      *at++ = *c++;
    *at = 0;
    buffer->used = at - (char *)buffer->base;
    assert(buffer->used <= buffer->cap);
  }
  else
    printf("%s", s);

  return out;
}
#endif

inline b32
belongsToArena(MemoryArena *arena, u8 *memory)
{
  return ((memory >= arena->base) && (memory < arena->base + arena->cap));
}

#define maximum(a, b) ((a < b) ? b : a)
#define minimum(a, b) ((a < b) ? a : b)

#define forward_declare

inline b32
isSubstring(char *full, char* sub, b32 case_sensitive=true)
{
  b32 out = true;
  if (sub && full)
  {
    for (char *f = full, *s = sub; *s && *f; s++, f++)
    {
      b32 equal = case_sensitive ? (*s != *f) : (tolower(*s) != tolower(*f));
      if (equal)
      {
        if (*s)
          out = false;
        break;
      }
    }
  }
  return out;
}

inline void
myprint()
{
  printToBuffer(0, "\n");
}

inline void
myprint(int d)
{
  printf("%d", d);
}

inline void
myprint(char *c)
{
  printf("%s", c);
}

inline b32
inArena(MemoryArena *arena, void *p)
{
  return ((u64)p >= (u64)arena->base && (u64)p < (u64)arena->base+arena->cap);
}

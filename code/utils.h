#pragma once

#include <cstdint>
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

#define UNUSED_VAR __attribute__((unused))
#define unused_variable __attribute__((unused))

#define internal        static
#define global_variable unused_variable static
#define local_persist   static

typedef uint8_t  u8;
typedef uint16_t u16;
typedef int32_t  s32;
typedef int32_t  i32;
typedef int8_t   b8;
typedef int32_t  b32;
typedef uint32_t u32;
typedef uint64_t u64;

typedef float    r32;
typedef long     s64;
typedef long     i64;

#define kiloBytes(value) ((value)*1024LL)
#define megaBytes(value) (kiloBytes(value)*1024LL)
#define gigaBytes(value) (megaBytes(value)*1024LL)
#define teraBytes(value) (gigaBytes(value)*1024LL)

#define arrayCount(array) (sizeof(array) / sizeof((array)[0]))

#if COMPILER_MSVC
#  define crash_the_program __debugbreak()
#else
#  define crash_the_program __builtin_trap()
#endif

#if REA_INTERNAL
#  define assert(claim) if (!(claim)) { printf("assertion fired at line %d in file %s!", __LINE__, __FILE__); fflush(stdout); crash_the_program; }
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
resetArena(MemoryArena *arena, b32 zero=false)
{
  arena->used = 0;
  if (zero)
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
/* #define copyStructNoCast(arena, src) copySize(arena, src, sizeof(*(src))) */
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
         at < s.length;
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
equal(const char *cstring, String s)
{
  return equal(s, cstring);
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
  while (true)
  {
    if (*c1 != *c2)
    {
      out = false;
      break;
    }
    else
    {
      if (*c1 == 0)
        break;
      else
      {
        c1++;
        c2++;
      }
    }
  }
  return out;
}

internal String
printVA(MemoryArena *buffer, char *format, va_list arg_list)
{
  char *at = (char *)getNext(buffer);
  int printed = vsprintf_s(at, (buffer->cap - buffer->used), format, arg_list);
  buffer->used += printed;
  return String{at, printed};
}

internal String
print(MemoryArena *buffer, char *format, ...)
{
  String out = {};

   va_list arg_list;
  __crt_va_start(arg_list, format);

  if (buffer)
  {
    out.chars = (char *)getNext(buffer);
    auto printed = vsprintf_s(out.chars, (buffer->cap-1 - buffer->used), format, arg_list);
    buffer->used += printed;
    out.length    = printed;
    buffer->base[buffer->used] = 0; // nil-termination
  }
  else
    vprintf_s(format, arg_list);

  __crt_va_end(arg_list);

  return out;
}

inline String
print(MemoryArena *buffer, String s)
{
  String out = {};
  if (buffer)
  {
    out.chars = (char *)getNext(buffer);
    char *at = out.chars;
    const char *c = s.chars;
    for (s32 index = 0; index < s.length; index++)
      *at++ = *c++;
    *at = 0;
    out.length = (s32)(at - out.chars);
    buffer->used += out.length;
    assert(buffer->used <= buffer->cap);
  }
  else
    printf("%.*s", s.length, s.chars);

  return out;
}

#if 0
inline char *
print(MemoryArena *buffer, char *s)
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

// bunch of metaprogramming tags
#define forward_declare
#define embed_struct
#define check_switch(tag)

inline char
toLowerCase(char c)
{
  if (('a' <= c) && (c <= 'z'))
    return c - 32;
  return c;
}

inline b32
isSubstring(String full, String sub, b32 case_sensitive=true)
{
  b32 out = true;
  if (sub.length > full.length)
  {
    out = false;
  }
  else
  {
    for (s32 id = 0;
         id < sub.length;
         id++)
    {
      char s = sub.chars[id];
      char f = full.chars[id];
      b32 mismatch = case_sensitive ? (s != f) : (toLowerCase(s) != toLowerCase(f));
      if (mismatch)
      {
        out = false;
        break;
      }
    }
  }
  return out;
}

inline void dump() {printf("\n");}
inline void dump(int d) {printf("%d", d);}
inline void dump(char *c) {printf("%s", c);}

inline b32
inArena(MemoryArena *arena, void *p)
{
  return ((u64)p >= (u64)arena->base && (u64)p < (u64)arena->base+arena->cap);
}

inline String
copyString(MemoryArena *buffer, String src)
{
  String out;
  out.chars  = copyArray(buffer, src.length, src.chars);
  out.length = src.length;
  return out;
}

inline void
concat(String *a, String b)
{
  a->length += b.length;
}

// source: https://groups.google.com/g/comp.std.c/c/d-6Mj5Lko_s
#define PP_NARG(...) PP_NARG_(__VA_ARGS__,PP_RSEQ_N())
#define PP_NARG_(...) PP_ARG_N(__VA_ARGS__)
#define PP_ARG_N(_1,_2,_3,_4,_5,_6,_7,_8,_9,N,...) N
#define PP_RSEQ_N() 9,8,7,6,5,4,3,2,1,0

#define CONCATENATE(arg1, arg2)   CONCATENATE1(arg1, arg2)
#define CONCATENATE1(arg1, arg2)  CONCATENATE2(arg1, arg2)
#define CONCATENATE2(arg1, arg2)  arg1##arg2

#define DUMP_1(x) dump(x)
#define DUMP_2(x, ...) dump(x); DUMP_1(__VA_ARGS__)
#define DUMP_3(x, ...) dump(x); DUMP_2(__VA_ARGS__)
#define DUMP_4(x, ...) dump(x); DUMP_3(__VA_ARGS__)
#define DUMP_5(x, ...) dump(x); DUMP_4(__VA_ARGS__)
#define DUMP_6(x, ...) dump(x); DUMP_5(__VA_ARGS__)
#define DUMP_7(x, ...) dump(x); DUMP_6(__VA_ARGS__)
#define DUMP_8(x, ...) dump(x); DUMP_7(__VA_ARGS__)
#define DUMP_9(x, ...) dump(x); DUMP_8(__VA_ARGS__)
#define DUMP_N(N, ...) CONCATENATE(DUMP_, N)
#define DUMP(...) DUMP_N(PP_NARG(__VA_ARGS__), __VA_ARGS__)(__VA_ARGS__)

#if !defined(UTILS_H)
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

#define UTILS_H
#endif

#if !defined(UTILS_H)
#include <cstdint>

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

global_variable b32 global_engine_failed = false;
#if COMPILER_MSVC
#    define assert(claim) { if (!(claim)) { __debugbreak(); } }
#else
#    define assert(claim) { if (!(claim)) { __builtin_trap(); } }
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

#define UTILS_H
#endif

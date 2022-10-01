#if !defined(UTILS_H)
#include <cstdint>

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

global_variable b32 globalRunning;
global_variable s64 globalPerfCountFrequency;

#define assert(claim) if (!(claim)) { __debugbreak(); }
#define invalidCodePath __debugbreak()
#define todoErrorReport __debugbreak()
#define todoIncomplete __debugbreak()
#define invalidDefaultCase default: { assert(false) };
#define breakhere { int x = 5; (void)x; }
#define generate(whatever...)

inline b32
inRange(s32 min, s32 val, s32 max)
{
    return (min <= val) && (val <= max);
}

#define UTILS_H
#endif

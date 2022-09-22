#if !defined(UTILS_H)

#define internal static
#define global_variable static

typedef int s32;
typedef int b32;
typedef long s64;
typedef unsigned long u64;
typedef float r32;
typedef char u8;
typedef unsigned int u32;

#define kiloBytes(value) ((value)*1024LL)
#define megaBytes(value) (kiloBytes(value)*1024LL)
#define gigaBytes(value) (megaBytes(value)*1024LL)
#define teraBytes(value) (gigaBytes(value)*1024LL)

#define arrayCount(array) (sizeof(array) / sizeof((array)[0]))

global_variable b32 globalRunning;
global_variable s64 globalPerfCountFrequency;

#define assert(claim) if (!(claim)) { __debugbreak(); }
#define invalidCodePath { __debugbreak(); }
#define invalidDefaultCase default: { assert(false) };

#define UTILS_H
#endif

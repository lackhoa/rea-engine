#if !defined(INTRINSICS_H)

#include "utils.h"
#include <string.h>

inline void
zeroMemory(void *destination, size_t length)
{
    memset(destination, 0, length);
}

inline void
copyMemory(void *dst, void *src, size_t size)
{
    memcpy(dst, src, size);
}

inline i32
absoluteValue(i32 in)
{
    return ((in >= 0) ? in : -in);
}

#define INTRINSICS_H
#endif

#if !defined(INTRINSICS_H)

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

#define INTRINSICS_H
#endif

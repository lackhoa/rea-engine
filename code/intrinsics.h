#if !defined(INTRINSICS_H)

#include <string.h>

inline void
zeroMemory(void *destination, size_t length)
{
    memset(destination, 0, length);
}

#define INTRINSICS_H
#endif

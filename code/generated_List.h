#include "utils.h" 
#include "memory.h" 
#include "intrinsics.h" 
struct StringListContent;
struct StringList
{
    StringListContent *c;
};
struct StringListContent
{
    String     car;
    StringList cdr;
};

inline s32
length(StringList ls)
{
    s32 result = 0;
    for (StringList l = ls ;
         l.c;
         l = l.c->cdr)
    {
        result++;
    }
    return result;
}

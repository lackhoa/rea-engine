struct ...ListContent;
struct ...List
{
    ...ListContent *c;
};
struct ...ListContent
{
    ...     car;
    ...List cdr;
};

inline s32
length(...List ls)
{
    s32 result = 0;
    for (...List l = ls ;
         l.c;
         l = l.c->cdr)
    {
        result++;
    }
    return result;
}

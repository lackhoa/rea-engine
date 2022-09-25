#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"

struct <<<Name>>>Vector
{
    s32 count;
    s32 capacity;
    <<<Name>>> *items;
};

inline <<<Name>>> *
addItem(MemoryArena *arena, <<<Name>>>Vector *vector, <<<Name>>> *added)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        <<<Name>>> *new_items = pushArray(arena, capacity, <<<Name>>>);
        copyMemory(new_items, vector->items, sizeof(<<<Name>>>)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    <<<Name>>> *result = vector->items + vector->count++;
    *result = *added;
    return added;
}

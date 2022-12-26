struct ...Vector
{
    MemoryArena *arena;
    i32 count;
    i32 capacity;
    ... *items;
};

internal ... *
pushItem(...Vector *vector)
{
    i32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        ... *new_items = pushArray(vector->arena, capacity, ...);
        copyMemory(new_items, vector->items, sizeof(...)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    ... *result = vector->items + vector->count++;
    return result;
}

inline ...Vector
new...Vector(MemoryArena *arena, i32 capacity)
{
    ...Vector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, ...);
    result.arena = arena;
    return result;
}

// TODO: Implement resize, pushItemNoResize

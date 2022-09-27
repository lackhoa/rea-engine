struct OperatorVector
{
    MemoryArena *arena;
    s32 count;
    s32 capacity;
    Operator *items;
};

internal Operator *
pushItem(OperatorVector *vector)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        Operator *new_items = pushArray(vector->arena, capacity, Operator);
        copyMemory(new_items, vector->items, sizeof(Operator)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    Operator *result = vector->items + vector->count++;
    return result;
}

inline OperatorVector
newOperatorVector(MemoryArena *arena, s32 capacity)
{
    OperatorVector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, Operator);
    result.arena = arena;
    return result;
}

// TODO: Implement resize, pushItemNoResize

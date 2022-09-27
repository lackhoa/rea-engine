struct TypeVector
{
    MemoryArena *arena;
    s32 count;
    s32 capacity;
    Type *items;
};

internal Type *
pushItem(TypeVector *vector)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        Type *new_items = pushArray(vector->arena, capacity, Type);
        copyMemory(new_items, vector->items, sizeof(Type)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    Type *result = vector->items + vector->count++;
    return result;
}

inline TypeVector
newTypeVector(MemoryArena *arena, s32 capacity)
{
    TypeVector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, Type);
    result.arena = arena;
    return result;
}

// TODO: Implement resize, pushItemNoResize

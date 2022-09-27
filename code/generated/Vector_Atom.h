struct AtomVector
{
    MemoryArena *arena;
    s32 count;
    s32 capacity;
    Atom *items;
};

internal Atom *
pushItem(AtomVector *vector)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        Atom *new_items = pushArray(vector->arena, capacity, Atom);
        copyMemory(new_items, vector->items, sizeof(Atom)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    Atom *result = vector->items + vector->count++;
    return result;
}

inline AtomVector
newAtomVector(MemoryArena *arena, s32 capacity)
{
    AtomVector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, Atom);
    result.arena = arena;
    return result;
}

// TODO: Implement resize, pushItemNoResize

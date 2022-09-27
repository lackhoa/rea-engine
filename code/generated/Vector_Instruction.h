struct InstructionVector
{
    MemoryArena *arena;
    s32 count;
    s32 capacity;
    Instruction *items;
};

internal Instruction *
pushItem(InstructionVector *vector)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        Instruction *new_items = pushArray(vector->arena, capacity, Instruction);
        copyMemory(new_items, vector->items, sizeof(Instruction)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    Instruction *result = vector->items + vector->count++;
    return result;
}

inline InstructionVector
newInstructionVector(MemoryArena *arena, s32 capacity)
{
    InstructionVector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, Instruction);
    result.arena = arena;
    return result;
}

// TODO: Implement resize, pushItemNoResize

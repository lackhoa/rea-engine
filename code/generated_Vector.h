#include "utils.h" 
#include "memory.h" 
#include "intrinsics.h" 
struct AxiomVector
{
    MemoryArena *arena;
    s32 count;
    s32 capacity;
    Axiom *items;
};

internal Axiom *
pushItem(AxiomVector *vector)
{
    s32 capacity = vector->capacity;
    if (vector->count >= capacity)
    {
        Axiom *new_items = pushArray(vector->arena, capacity, Axiom);
        copyMemory(new_items, vector->items, sizeof(Axiom)*capacity);
        vector->items = new_items;
        vector->capacity = 2*capacity;
    }
    Axiom *result = vector->items + vector->count++;
    return result;
}

inline AxiomVector
newAxiomVector(MemoryArena *arena, s32 capacity)
{
    AxiomVector result;
    result.count = 0;
    result.capacity = capacity;
    result.items = pushArray(arena, capacity, Axiom);
    result.arena = arena;
    return result;
}
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

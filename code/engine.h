#if !defined(ENGINE_H)

#include "utils.h"
#include "memory.h"

struct Expression;

struct Binding
{
    String      key;
    Expression *value;
    Binding    *next;
};

struct Bindings
{
    MemoryArena *arena;
    Binding      first[128];  // NOTE: this is hash table
    Bindings    *next;
};

internal Expression *
parseExpression(MemoryArena *arena, Bindings *bindings, s32 min_precedence = -9999);

enum Trinary
{
  Trinary_Unknown, Trinary_False, Trinary_True,
};

internal Trinary
compareExpressions(Expression *lhs, Expression *rhs);

#define ENGINE_H
#endif

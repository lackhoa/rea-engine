#pragma once

#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "tokenization.h"

struct Arrow;
struct Value;
struct LocalBindings;

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena *temp_arena;
 
// Contains both ast and values because the print functions need to operate on
// them both.
enum AstCategory
{
  AC_Null = 0,

  AC_DummyHole,                 // hole left in for type-checking

  // result after initial parsing
  AC_Identifier,
  AC_IncompleteFork,

  // result after building
  AC_Variable,
  AC_Constant,

  AC_Fork,
  AC_Sequence,
  AC_Composite,
  AC_Arrow,
  AC_Function,
  AC_Let,
  AC_Rewrite,
  AC_Accessor,

  // values subset
  AC_CompositeV   = 0x80,
  AC_ArrowV       = 0x81,
  AC_Union  = 0x82,
  AC_FunctionV    = 0x83,
  AC_StackRef     = 0x84,
  AC_AstWithStack = 0x85,
  AC_AccessorV    = 0x86,
};

struct Ast
{
  AstCategory cat;
  Token       token;
};

inline b32
isValue(AstCategory cat)
{
  b32 out = (cat >> 7);
  return out;
}

inline b32
isValue(Ast *in0)
{
  return isValue(in0->cat);
}

inline Value *
toValue(Ast *ast)
{
  if (ast)
    assert(isValue(ast));
  return (Value*) ast;
}

inline Value **
toValues(Ast **asts, s32 count)
{
  for (s32 id = 0; id < count; id++)
    assert(isValue(asts[id]));
  return (Value **) asts;
}

inline Ast **
toAsts(Value **values)
{
  return (Ast **) values;
}

inline void
initAst(Ast *in, AstCategory cat, Token *token)
{
  in->cat   = cat;
  in->token = *token;
}

inline Ast *
newAst_(MemoryArena *arena, AstCategory cat, Token *token, size_t size)
{
  Ast *out = (Ast *)pushSize(arena, size, true);
  initAst(out, cat, token);
  return out;
}

#define newAst(arena, cat, token)        \
  ((cat *) newAst_(arena, AC_##cat, token, sizeof(cat)))

#define castAst(exp, Cat) ((exp)->cat == AC_##Cat ? (Cat*)(exp) : 0)

struct Identifier
{
  Ast a;
};

struct Variable
{
  Ast  a;

  s32  id;
  s32  stack_delta;
};

inline void
initVariable(Variable *var, u32 id)
{
  var->stack_delta = 0;
  var->id          = id;
}

struct Constant
{
  Ast    a;
  Value *value;
};

inline void
initConstant(Constant *in, Value *value)
{
  in->value = value;
}

struct ForkParameters
{
  s32    count;
  Token *names;
};

struct ForkParsing
{
  Identifier      *ctors;
  ForkParameters  *params;
  Ast            **bodies;
};

struct Union;

struct Fork
{
  Ast a;

  Union     *constructor;
  Ast             *subject;
  s32              case_count;
  ForkParameters  *params;
  Ast            **bodies;

  // temporary parsing data
  ForkParsing *parsing;
};
typedef Fork IncompleteFork;

struct ParseExpressionOptions
{
  s32 min_precedence = -9999;
};

// NOTE: bool can be converted directly to this this
enum Trinary
{
  Trinary_False   = 0,
  Trinary_True    = 1,
  Trinary_Unknown = 2, 
};

internal Trinary
identicalTrinary(Value *lhs, Value *rhs);

struct RewriteRule
{
  Value *lhs;
  Value *rhs;
  RewriteRule *next;
};

struct Stack
{
  Stack *outer;
  s32    depth;
  s32    arg_count;
  Value *args[32];              // todo: compute this cap
};

// just jam everything in here!
// used in normalization, typechecking, etc.
struct Environment
{
  MemoryArena *arena;
  LocalBindings *bindings;

  Stack *stack;

  RewriteRule *rewrite;
};

#define getStackDepth(stack) (stack ? stack->depth : 0)

inline RewriteRule *
newRewrite(Environment *env, Value *lhs, Value *rhs)
{
  RewriteRule *out = pushStruct(temp_arena, RewriteRule);
  out->lhs  = lhs;
  out->rhs  = rhs;
  out->next = env->rewrite;
  return out;
}

inline Environment
newEnvironment(MemoryArena *arena)
{
  Environment out = {};
  out.arena = arena;
  return out;
}

struct AstList
{
  Ast     *first;
  AstList *next;
};

struct LocalBinding
{
  s32           hash;
  String        key;
  s32           value;
  LocalBinding *next;
};

struct LocalBindings
{
  MemoryArena   *arena;
  LocalBinding   table[128];
  LocalBindings *next;
  s32 count;
};

inline LocalBindings *
extendBindings(MemoryArena *arena, LocalBindings *outer)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->next  = outer;
  out->arena = arena;
  out->count = 0;
  return out;
}

struct Value
{
  AstCategory cat;
  Value *type;
};

inline void
initValue(Value *in, AstCategory cat, Value *type)
{
  assert(isValue(cat));
  in->cat  = cat;
  in->type = type;
}

inline Value *
newValue_(MemoryArena *arena, AstCategory cat, Value *type, size_t size)
{
  Value *out = (Value *)pushSize(arena, size, true);
  initValue(out, cat, type);
  return out;
}

#define newValue(arena, cat, type)                        \
  ((cat *) newValue_(arena, AC_##cat, type, sizeof(cat)))

struct Union
{
  Value v;
  Token token;

  u64 set_id;

  s32    set_count;
  Union *sets;
};

struct Function
{
  Ast   a;

  Ast   *body;
  Arrow *signature;
};

struct FunctionV
{
  Value v;

  Token     token;
  Function *a;
  Stack    *stack;
};

struct Let
{
  Ast a;

  Identifier  lhs;
  Ast        *rhs;
};

struct RecursiveLet
{
  Ast a;

  Identifier  lhs;
  Function   *rhs;
};

struct StackRef
{
  Value v;

  String name;
  s32    id;
  s32    stack_depth;
};

struct Composite
{
  Ast   a;

  Ast  *op;
  s32   arg_count;
  Ast **args;
};

struct CompositeV
{
  Value v;

  Value  *op;
  s32     arg_count;
  Value **args;
};

struct Sequence
{
  Ast a;

  Ast **items;
  s32   count;
};

inline void
initComposite(Composite *app, Ast *op, s32 arg_count, Ast **args)
{
  app->op        = op;
  app->arg_count = arg_count;
  app->args      = args;
}

struct Arrow
{
  Ast   a;

  Ast *out_type;
  s32     param_count;
  Token  *param_names;
  Ast   **param_types;
  b32    *param_implied;
};

struct ArrowV
{
  Value v;
  Arrow *a;      // since we already hold pointer to the stack, which is
                 // transient, we might as well pointer to the ast.
  Stack *stack;  // value only
};

struct GlobalBinding
{
    String         key;
    Value         *value;
    GlobalBinding *next;
};

struct GlobalBindings
{
    MemoryArena    *arena;
    GlobalBinding   table[1024];
    GlobalBindings *next;
};

inline Union *
getFormOf(Value *in0)
{
  Union *out = 0;
  switch (in0->cat)
  {
    case AC_CompositeV:
    {
      CompositeV *in = castAst(in0, CompositeV);
      out = castAst(in->op, Union);
    } break;

    case AC_Union:
    {
      out = castAst(in0, Union);
    } break;
  }
  return out;
}

inline Union *
getFormOf(Ast *in0)
{
  Union *out = 0;
  switch (in0->cat)
  {
    case AC_Composite:
    {
      if (Composite *in = castAst(in0, Composite))
        if (Constant *op = castAst(in->op, Constant))
          out = castAst(op->value, Union);
    } break;

    case AC_Constant:
    {
      if (Constant *in = castAst(in0, Constant))
        out = castAst(in->value, Union);
    } break;

    invalidDefaultCase;
  }
  return out;
}

struct Expression
{
  Ast   *ast;
  Value *type;
  operator bool() { return (bool)ast; }
};

struct Rewrite
{
  Ast  a;
  Ast *proof;
  b32  right_to_left;
};

struct Record
{
  Value v;
  s32    member_count;
  Token *member_names;
  Ast   *member_types;
};

struct Accessor
{
  Ast    a;
  Ast   *record;
  Token  member;                // parsing information only
  s32    param_id;              // after build phase
};

struct AccessorV
{
  Value  v;
  Value *record;
  s32    param_id;
};

struct FileList
{
  char     *first_path;
  char     *first_content;
  FileList *next;
};

struct EngineState
{
  MemoryArena *arena;
  FileList    *file_list;
};

struct PrintOptions{b32 detailed; b32 print_type; void *parent;};

struct Builtins
{
  Union *refl;
  Union *equal;
  Union *True;
  Union *truth;
  Union *False;
  Union *Set;
  Union *Type;
};

#include "generated/engine_forward.h"

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
global_variable MemoryArena __attribute__((unused)) *permanent_arena;

// Contains both ast and values because the print functions need to operate on
// them both.
enum AstCategory  // nocheckin: maybe don't prepend the name
{
  AC_Null = 0,
  // hole left in for type-checking
  AC_Hole,
  // result after initial parsing
  AC_Identifier,

  // Expression
  AC_Variable,
  AC_Constant,
  AC_Composite,
  AC_Arrow,
  AC_Accessor,

  // in "sequence" context only, not general expressions.
  AC_Sequence,
  AC_Fork,
  AC_Rewrite,
  AC_FunctionDecl,
  AC_Let,
};

enum ValueCategory
{
  VC_Null,
  VC_Hole,
  VC_BuiltinSet   ,
  VC_BuiltinType  ,
  VC_BuiltinEqual ,
  VC_CompositeV   ,
  VC_ArrowV       ,
  VC_FunctionV    ,
  VC_StackValue   ,
  VC_HeapValue    ,
  VC_Union        ,
  VC_Constructor  ,
};

typedef Value BuiltinType;
typedef Value BuiltinSet;
typedef Value BuiltinEqual;

struct Ast
#define EMBED_AST_                              \
{                                               \
  AstCategory cat;                              \
  Token       token;                            \
};
EMBED_AST_

#define EMBED_AST                               \
union                                           \
{                                               \
  Ast a;                                        \
  struct EMBED_AST_                             \
};

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
#define polyAst(exp, Cat, Cat2) (((exp)->cat == AC_##Cat || (exp)->cat == AC_##Cat2) ? (Cat*)(exp) : 0)

#define castValue(exp, Cat) ((exp)->cat == VC_##Cat ? (Cat*)(exp) : 0)

struct Identifier
{
  EMBED_AST
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
  b32    is_synthetic;
};

struct Sequence
{
  Ast a;

  Ast **items;
  s32   count;
};

inline Constant *
newSyntheticConstant(MemoryArena *arena, Value *value)
{
  Token token = newToken("<synthetic>");
  Constant *out = newAst(arena, Constant, &token);
  out->is_synthetic = true;
  out->value        = value;
  return out;
}

struct ForkParsing
{
  Identifier *ctors;
};

struct Union;

struct Fork
{
  Ast a;

  Union     *uni;
  Ast       *subject;
  s32        case_count;
  Sequence **bodies;

  // temporary parsing data
  ForkParsing *parsing;
};

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
  s32    count;
  Value *args[32];              // todo: compute this cap
};

// used in normalization, build/typecheck, etc.
struct Environment
{
  LocalBindings *bindings;
  Stack         *stack;
  RewriteRule   *rewrite;
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
extendBindings(MemoryArena *arena, Environment *env)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->next  = env->bindings;
  out->arena = arena;
  out->count = 0;
  env->bindings = out;
  return out;
}

struct Value
{
  ValueCategory  cat;
  Value         *type;
};

inline void
initValue(Value *in, ValueCategory cat, Value *type)
{
  in->cat  = cat;
  in->type = type;
}

inline Value *
newValue_(MemoryArena *arena, ValueCategory cat, Value *type, size_t size)
{
  Value *out = (Value *)pushSize(arena, size, true);
  initValue(out, cat, type);
  return out;
}

#define newValue(arena, cat, type)                        \
  ((cat *) newValue_(arena, VC_##cat, type, sizeof(cat)))

struct Constructor
{
  Value  v;
  /* embed(Value, v) */
  Union *uni;
  Token  name;
  s32    id;
};

struct Union
{
  Value v;
  Token name;

  s32          ctor_count;
  Constructor *ctors;
};

struct FunctionDecl
#define EMBED_FUNCTION                          \
{                                               \
  Ast       a;                                  \
  Sequence *body;                               \
  Arrow    *signature;                          \
};
EMBED_FUNCTION

struct FunctionV
{
  Value v;
  union
  {
    FunctionDecl function;
    struct   EMBED_FUNCTION;
  };
  Stack *stack;
};

struct Let
{
  Ast a;

  Token  lhs;
  Ast   *rhs;
};

struct StackValue
{
  Value v;

  Token name;
  s32   id;
  s32   stack_depth;
};

struct HeapValue
{
  Value v;

  String name;
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

inline void
initComposite(Composite *app, Ast *op, s32 arg_count, Ast **args)
{
  app->op        = op;
  app->arg_count = arg_count;
  app->args      = args;
}

struct Arrow
#define EMBED_ARROW                             \
  {                                             \
    Ast     a;                                  \
    Ast    *out_type;                           \
    s32     param_count;                        \
    Token  *param_names;                        \
    Ast   **param_types;                        \
  };
EMBED_ARROW

struct ArrowV
{
  Value v;
  union
  {
    Arrow arrow;
    struct EMBED_ARROW
  };
  s32 stack_depth;
};

inline Arrow *
toArrow(Value *value)
{
  return &castValue(value, ArrowV)->arrow;
}

struct GlobalBinding
{
  String         key;
  s32            count;
  Value *(values[8]);           // todo: #grow
  GlobalBinding *next_hash_slot;
};

struct GlobalBindings  // :global-bindings-zero-at-startup
{
    GlobalBinding table[1024];
};

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
          out = castValue(op->value, Union);
    } break;

    case AC_Constant:
    {
      if (Constant *in = castAst(in0, Constant))
        out = castValue(in->value, Union);
    } break;

    invalidDefaultCase;
  }
  return out;
}

struct Expression
{
  Ast   *ast;
  Value *value;
  operator bool() { return (bool)ast; }
};

struct Rewrite
{
  Ast  a;

  Ast *proof;
  b32  right_to_left;
};

struct Accessor
{
  Ast    a;

  Ast   *record;                // in parse phase we can't tell if the op is a constructor
  Token  member;                // parsing info
  s32    param_id;              // after build phase
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
  Union *True;
  Constructor *truth;
  Union *False;
  Value *equal;
  Value *Set;
  Value *Type;
};

enum MatcherCategory
{
  MC_Unknown,
  MC_Exact,
  MC_OutType,
};

struct Matcher
{
  MatcherCategory cat;
  union
  {
    Value *Exact;
    Value *OutType;
  };
  operator bool() { return (cat == MC_Exact) && (Exact == 0); }
};

inline Matcher exactMatch(Value *value)
{
  return Matcher{.cat=MC_Exact, .Exact=value};
}

struct ValueArray
{
  s32    count;
  Value *items;
};

struct AstArray
{
  s32    count;
  Value *items;
};

#include "generated/engine_forward.h"

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
global_variable MemoryArena *permanent_arena;

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

  // value subset
  AC_BuiltinSet,
  AC_BuiltinType,
  AC_BuiltinEqual,
  AC_CompositeV,
  AC_ArrowV,
  AC_FunctionV,
  AC_StackRef,
  AC_HeapValue,
  AC_AccessorV,

  // set subset (inherit from value)
  AC_Union,
  AC_Constructor,
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

inline Constant *
newSyntheticConstant(MemoryArena *arena, Value *value)
{
  Token token = newToken("<synthetic>");
  Constant *out = newAst(arena, Constant, &token);
  out->is_synthetic = true;
  out->value        = value;
  return out;
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

  Union           *uni;
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
equalTrinary(Value *lhs, Value *rhs);

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
  AstCategory  cat;
  Value       *type;
};

inline void
initValue(Value *in, AstCategory cat, Value *type)
{
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

struct Constructor
{
  Value  v;
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

struct Function
#define EMBED_FUNCTION                          \
{                                               \
  Ast    a;                                     \
  Ast   *body;                                  \
  Arrow *signature;                             \
};
EMBED_FUNCTION

struct FunctionV
{
  Value v;

  union
  {
    Function function;
    struct   EMBED_FUNCTION;
  };
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

  union embed
  {
    Arrow arrow;
    struct EMBED_ARROW
  };
  s32 stack_depth;
};

inline Arrow *
toArrow(Value *value)
{
  return &castAst(value, ArrowV)->arrow;
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

#if 0
inline Union *
getUnionOf(Value *in0)
{
  switch (in0->cat)
  {
    case AC_CompositeV:
    {
      CompositeV *in = castAst(in0, CompositeV);
      return castAst(in->op, Union);
    } break;

    case AC_Union:
    {
      return castAst(in0, Union);
    } break;

    default:
      return 0;
  }
}
#endif

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

struct AccessorV
{
  Value  v;

  CompositeV *record;
  s32         param_id;
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

#include "generated/engine_forward.h"

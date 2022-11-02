#pragma once

#include "utils.h"
#include "memory.h"
#include "tokenization.h"
#include "rea_builtins.h"

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena *temp_arena;
 
enum AstCategory
{
  AC_Null = 0,

  AC_Composite = 1,

  // result after parsing
  AC_Identifier,
  AC_AbstractFork,

  // built expressions
  AC_Variable,
  AC_Constant,

  AC_Fork,                      // switch statement
  AC_ArrowType,                 // type of procedure and built-in objects

  // dummy values for denoting only
  AC_DummyHole,                 // hole left in for type-checking
  AC_DummySequence,             // like scheme's "begin" keyword
  AC_DummyRewrite,

  // tunnelling values into ast
  AC_CompositeV = 101,
  AC_Form       = 102,
  AC_Function   = 103,          // holds actual computation (ie body that can be executed)
  AC_StackRef   = 104,
};

struct Ast
{
  AstCategory cat;
  Token       token;
};

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

b32 identicalB32(Ast *lhs, Ast *rhs);

#define castAst(exp, Cat) (((exp)->cat == AC_##Cat || (exp)->cat == AC_##Cat + 100) ? (Cat*)(exp) : 0)

struct Identifier
{
  Ast h;
};

struct Variable
{
  Ast  h;

  s32  id;
  s32  stack_delta;
  Ast *type;
};

inline void
initVariable(Variable *var, u32 id, Ast *type)
{
  var->stack_delta = 0;
  var->id          = id;
  var->type        = type;
}

struct AbstractFork
{
  Ast   h;
  Ast  *subject;
  s32   case_count;
  Ast **patterns;
  Ast **bodies;
};

struct Constant
{
  Ast  h;
  Ast *value;
};

inline void
initIdentifier(Constant *in, Ast *value)
{
  in->value = value;
}

struct ForkCase
{
  Ast  *body;
  Variable   **params;
};
inline void
initForkCase(ForkCase *fork_case, Ast *body, Variable **params, s32 param_count)
{
  if (param_count)
    assert(params);
  fork_case->body   = body;
  fork_case->params = params;
}

struct ArrowType
{
  Ast        h;

  s32        param_count;
  Variable **params;
  Ast       *return_type;
};

inline void
initArrowType(ArrowType *in, s32 param_count, Variable **params, Ast *return_type)
{
  in->param_count = param_count;
  in->params      = params;
  in->return_type = return_type;
}

struct Fork
{
  Ast h;

  Form       *form;
  Ast *subject;
  s32         case_count;
  ForkCase   *cases;
};

inline void
initFork(Fork *out, Form *form, Ast *subject, s32 case_count, ForkCase *cases)
{
  out->form       = form;
  out->subject    = subject;
  out->case_count = case_count;
  out->cases      = cases;

  for (s32 case_id = 0; case_id < case_count; case_id++)
    assert(out->cases[case_id].body);
}

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
identicalTrinary(Ast *lhs, Ast *rhs);

struct Rewrite
{
  Ast     *lhs;
  Ast     *rhs;
  Rewrite *next;
};

struct Stack
{
  Stack  *outer;
  s32     arg_count;
  Ast   **args;
};

// used in normalization, typechecking, etc.
struct Environment
{
  MemoryArena *arena;
  MemoryArena *temp_arena;

  Stack *stack;
  s32 stack_depth;              // 0 is reserved
  s32 stack_offset;             // todo #speed pass this separately

  Rewrite *rewrite;
};

inline void
extendStack(Environment *env, s32 arg_count, Ast **args)
{
  Stack *stack = pushStruct(env->temp_arena, Stack);
  stack->outer     = env->stack;
  stack->arg_count = arg_count;
  stack->args      = args;

  env->stack = stack;
  env->stack_depth++;
}

inline Rewrite *
newRewrite(Environment *env, Ast *lhs, Ast *rhs)
{
  Rewrite *out = pushStruct(env->temp_arena, Rewrite);
  out->lhs  = lhs;
  out->rhs  = rhs;
  out->next = env->rewrite;
  return out;
}

inline Environment
newEnvironment(MemoryArena *arena)
{
  Environment out = {};
  out.arena       = arena;
  out.temp_arena  = temp_arena;
  return out;
}

inline Ast *
parseExpressionToExpression(MemoryArena *arena);

struct AstList
{
  Ast     *first;
  AstList *next;
};

struct Binding
{
    String   key;
    Ast     *value;
    Binding *next;
};

struct Bindings
{
    MemoryArena *arena;
    Binding      table[128];    // NOTE: this is a hash table
    Bindings    *next;
};

struct ValueBindings
{
  Bindings *v;
};

inline Bindings *
extendBindings(MemoryArena *arena, Bindings *outer)
{
  Bindings *out = pushStruct(arena, Bindings, true);
  out->next  = outer;
  out->arena = arena;
  return out;
}

inline ValueBindings
toValueBindings(Bindings *bindings)
{
  return ValueBindings{bindings};
}

enum ValueCategory
{
  VC_CompositeV = 101,
  VC_Form       = 102,
  VC_Function   = 103,
  VC_StackRef   = 104,
};

struct Value
{
  union
  {
    struct
    {
      ValueCategory  cat;
      Token          token;
    };
    Ast a;         // tunnelling for now
  };
  Ast *type;
};

inline void
initValue(Value *in, ValueCategory cat, Token *token, Ast *type)
{
  in->cat     = cat;
  in->a.token = *token;
  in->type    = type;
}

inline Value *
newValue_(MemoryArena *arena, ValueCategory cat, Token *token, Ast *type, size_t size)
{
  Value *out = (Value *)pushSize(arena, size, true);
  initValue(out, cat, token, type);
  return out;
}

#define newValue(arena, cat, token, type)                        \
  ((cat *) newValue_(arena, VC_##cat, token, type, sizeof(cat)))

#define castValue(value, Cat) (((value)->cat == VC_##Cat) ? (Cat*)(value) : 0)

struct Form
{
  Value h;

  s32  ctor_id;

  s32   ctor_count;
  Form *ctors;
};

inline void
initForm(Form *in, s32 ctor_count, Form *ctors, s32 ctor_id)
{
  in->h.a.cat    = AC_Form;
  in->ctor_count = ctor_count;
  in->ctors      = ctors;
  in->ctor_id    = ctor_id;
}

inline void
initForm(Form *in, s32 ctor_id)
{
  in->h.a.cat    = AC_Form;
  in->ctor_id    = ctor_id;
  in->ctor_count = 0;
  in->ctors      = 0;
}

struct Function
{
  Value  h;

  Ast   *body;
};

struct StackRef
{
  Value h;

  String name;
  s32 id;
  s32 stack_depth;
};

struct Composite
{
  union
  {
    Ast   h;
    Value v;
  };

  Ast  *op;
  s32   arg_count;
  Ast **args;
};

typedef Composite CompositeV;

inline void
initComposite(Composite *app, Ast *op, s32 arg_count, Ast **args)
{
  app->op        = op;
  app->arg_count = arg_count;
  app->args      = args;
}

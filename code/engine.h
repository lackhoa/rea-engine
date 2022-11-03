#pragma once

#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena *temp_arena;
 
enum AstCategory
{
  AC_Null = 0,

  AC_DummyHole,                 // hole left in for type-checking
  AC_DummySequence,             // like scheme's "begin" keyword
  AC_DummyRewrite,

  // result after initial parsing
  AC_Identifier,
  AC_AbstractFork,

  // result after building (ie everything after that)
  AC_Variable,
  AC_Constant,

  AC_Fork,

  AC_Composite,
  AC_Arrow,
  AC_Function,
  AC_Let,

  // values subset
  AC_CompositeV = 0x80,
  AC_ArrowV     = 0x81,
  AC_Form       = 0x82,
  AC_FunctionV  = 0x83,
  AC_StackRef   = 0x84,
};

struct Ast
{
  AstCategory cat;
  Token       token;
};

struct Value;

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
  assert(isValue(ast));
  return (Value*) ast;
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

b32 identicalB32(Ast *lhs, Ast *rhs);

#define castAst(exp, Cat) ((exp)->cat == AC_##Cat ? (Cat*)(exp) : 0)
#define castValue(exp, Cat) ((isValue(AC_##Cat) && (exp)->a.cat == AC_##Cat) ? (Cat*)(exp) : 0)
#define polyAst(exp, Cat, Cat2) (((exp)->cat == AC_##Cat || (exp)->cat == AC_##Cat2) ? (Cat*)(exp) : 0)

struct Identifier
{
  Ast a;
};

struct Variable
{
  Ast  a;

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

struct ForkCase
{
  Ast        *body;

  Token  *param_names;
  Ast   **param_types;
};

struct Form;

struct Fork
{
  Ast a;

  Form     *form;
  Ast      *subject;
  s32       case_count;
  ForkCase *cases;
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

// NOTE: I plan have the fork mutated in-place from parsing to typechecking,
// let's see how it goes...
struct AbstractFork
{
  Ast a;

  Fork f;

  Ast **patterns;
  Ast **bodies;
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
  Stack *outer;
  s32    arg_count;
  Ast   *args[32];  // todo: compute this cap
};

// used in normalization, typechecking, etc.
struct Environment
{
  MemoryArena *arena;

  Stack *stack;
  s32 stack_depth;              // 0 is reserved
  s32 stack_offset;             // todo #speed pass this separately

  Rewrite *rewrite;
};

// todo: #speed copying values around
inline void
extendStack(Environment *env, s32 arg_count, Ast **args)
{
  Stack *stack = pushStruct(temp_arena, Stack);
  stack->outer     = env->stack;
  assert(arg_count <= arrayCount(stack->args));
  stack->arg_count = arg_count;
  if (args)
  {
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {
      stack->args[arg_id] = args[arg_id];
    }
  }

  env->stack = stack;
  env->stack_depth++;
}

inline Rewrite *
newRewrite(Environment *env, Ast *lhs, Ast *rhs)
{
  Rewrite *out = pushStruct(temp_arena, Rewrite);
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

inline Ast *
parseExpressionToAst(MemoryArena *arena);

struct AstList
{
  Ast     *first;
  AstList *next;
};

// nocheckin: don't need the type
struct LocalBindingValue
{
  s32  id;
  Ast *type;
};

struct LocalBinding
{
  s32                hash;
  String             key;
  LocalBindingValue  value;
  LocalBinding      *next;
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
  Ast a;
  Ast *type;
};

inline void
initValue(Value *in, AstCategory cat, Token *token, Ast *type)
{
  assert(isValue(cat));
  in->a.cat   = cat;
  in->a.token = *token;
  in->type    = type;
}

inline Value *
newValue_(MemoryArena *arena, AstCategory cat, Token *token, Ast *type, size_t size)
{
  Value *out = (Value *)pushSize(arena, size, true);
  initValue(out, cat, token, type);
  return out;
}

#define newValue(arena, cat, token, type)                        \
  ((cat *) newValue_(arena, AC_##cat, token, type, sizeof(cat)))

struct Form
{
  Value v;

  s32  ctor_id;

  s32   ctor_count;
  Form *ctors;
};

inline void
initForm(Form *in, s32 ctor_count, Form *ctors, s32 ctor_id)
{
  in->v.a.cat    = AC_Form;
  in->ctor_count = ctor_count;
  in->ctors      = ctors;
  in->ctor_id    = ctor_id;
}

inline void
initForm(Form *in, s32 ctor_id)
{
  in->v.a.cat    = AC_Form;
  in->ctor_id    = ctor_id;
  in->ctor_count = 0;
  in->ctors      = 0;
}

struct Function
{
  union
  {
    Ast   a;
    Value v;
  };

  Ast   *body;
};
typedef Function FunctionV;

struct Let
{
  Ast a;

  Identifier  lhs;
  Ast        *rhs;
};

struct StackRef
{
  Value h;

  String name;
  s32    id;
  s32    stack_depth;
};

struct Composite
{
  union
  {
    Ast   a;
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

struct Arrow
{
  union
  {
    Ast   a;
    Value v;
  };

  s32  param_count;
  Ast *return_type;

  Token  *param_names;
  Ast   **param_types;
};

typedef Arrow ArrowV;

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


#pragma once

#include "utils.h"
#include "memory.h"

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena  global_temp_arena_;
global_variable MemoryArena *global_temp_arena = &global_temp_arena_;

enum ExpressionCategory
{
  // might be free or bound
  EC_Variable,                // reference to some unknown on "the stack"

  // ground values
  EC_Application,             // operator application
  EC_Fork,                  // switch statement
  EC_Form,                    // like Coq inductive types
  EC_Constructor,             // canonical members of forms
  EC_Procedure,               // holds actual computation (ie body that can be executed)
  EC_ArrowType,               // type of procedure and built-in objects

  // strictly non-values
  EC_Hole,                    // hole left in for type-checking

  EC_Builtin_identical,
  EC_Builtin_Set,
  EC_Builtin_Prop,
  EC_Builtin_Proc,
  EC_Builtin_Type,
};

// IMPORTANT: All expressions are well-typed (except in parsing phase, wherein
// an expression will have two states: a. it has type and has been typechecked,
// b. its type is null).
struct Expression
{
  ExpressionCategory  cat;
  Expression         *type;     // IMPORTANT: always in normal form
};

inline void
initExpression(Expression *in, ExpressionCategory cat, Expression *type)
{
  in->cat  = cat;
  in->type = type;
}

inline Expression *
newExpression_(MemoryArena *arena, ExpressionCategory cat, Expression *type, size_t size)
{
  Expression *out = (Expression *)pushSize(arena, size);
  initExpression(out, cat, type);
  return out;
}

#define newExpressionNoCast(arena, cat, type)                \
  newExpression_(arena, EC_##cat, type, sizeof(cat))

#define newExpression(arena, cat, type)                \
  (cat *) newExpression_(arena, EC_##cat, type, sizeof(cat))

b32 identicalB32(Expression *lhs, Expression *rhs);

#define castExpression(exp, Cat) (((exp)->cat == EC_##Cat) ? (Cat*)(exp) : 0)

struct Binding
{
    String      key;
    Expression *value;
    Binding    *next;
};

struct Bindings
{
    MemoryArena *arena;
    Binding      table[128];    // NOTE: this is hash table
    Bindings    *next;
};

typedef s32 Atom;

struct ArrowType;
struct Variable
{
  Expression h;

  String name;
  s32    id;
  s32    stack_delta;  // relative
  s32    stack_depth;  // absolute

  ArrowType *signature;  // signature of the stack.
};

inline void
initVariable(Variable *var, String name, u32 id, ArrowType *signature)
{
  var->name        = name;
  var->stack_delta = 0;
  var->id          = id;
  var->stack_depth = 0;
  var->signature   = signature;
}

struct Application
{
  Expression  h;
  Expression  *op;
  s32          arg_count;
  Expression **args;
};

inline void
initApplication(Application *app, Expression *op, s32 arg_count, Expression **args)
{
  app->op = op;
  app->arg_count = arg_count;
  app->args = args;
}

struct ForkCase
{
  Expression  *body;
  Variable   **params;
};
inline void
initForkCase(ForkCase *fork_case, Expression *body, Variable **params)
{
  fork_case->body   = body;
  fork_case->params = params;
}

struct Fork
{
  Expression h;

  Expression *subject;
  s32         case_count;
  ForkCase   *cases;
};

inline void
initFork(Fork *out, Expression *subject, s32 case_count, ForkCase *cases)
{
  out->subject    = subject;
  out->case_count = case_count;
  out->cases      = cases;

  for (s32 case_id = 0; case_id < case_count; case_id++)
    assert(out->cases[case_id].body);
}

struct Constructor
{
  Expression h;
  s32        id;
  String     name;
};

struct Form
{
  Expression    h;
  String        name;
  s32           ctor_count;
  Constructor **ctors;          // note: We don't hold arbitrary expressions here, only
  // constructors. But storing full expressions here is
  // more convenient since then you don't need a separate
  // type with constructor id and then jump through hoops
  // to get back the constructor info.
};

// NOTE: most of the information is in the (arrow) type;
struct Procedure
{
  Expression  h;
  String      name;
  Expression *body;
};

inline void
initProcedure(Procedure *proc, String name, Expression *body)
{
  proc->name = name;
  proc->body = body;
}

struct ArrowType
{
  Expression   h;
  s32          param_count;
  Variable   **params;
  Expression  *return_type;
};

inline void
initArrowType(ArrowType *signature, s32 param_count, Variable **params, Expression *return_type)
{
  signature->param_count = param_count;
  signature->params      = params;
  signature->return_type = return_type;
}

struct Ast;

struct ParseExpressionOptions
{
  s32 min_precedence;
};

inline ParseExpressionOptions
parseExpressionOptions()
{
  ParseExpressionOptions out = {};
  out.min_precedence = -9999;
  return out;
}

internal Ast *
parseExpressionAst(MemoryArena *arena,
                   ParseExpressionOptions opt = parseExpressionOptions());

enum Trinary
{
  Trinary_Unknown, Trinary_False, Trinary_True,
};

internal Trinary
identicalTrinary(Expression *lhs, Expression *rhs);

struct Rewrite
{
  Expression *lhs;
  Expression *rhs;
  Rewrite    *next;
};

struct Stack
{
  ArrowType    *signature;
  s32           count;
  Expression  **args;
  Stack        *next;
};

// used in normalization, typechecking, etc.
struct Environment
{
  MemoryArena *arena;
  MemoryArena *temp_arena;

  s32 stack_depth;              // 0 is reserved
  s32 stack_offset;            // todo #speed pass this separately

  Rewrite *rewrite;
};

inline Rewrite *
newRewrite(Environment *env, Expression *lhs, Expression *rhs)
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
  out.temp_arena  = global_temp_arena;
  out.stack_depth = 1;
  return out;
}

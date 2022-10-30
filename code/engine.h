#pragma once

#include "utils.h"
#include "memory.h"
#include "tokenization.h"
#include "rea_builtins.h"

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena  global_temp_arena_;
global_variable MemoryArena *global_temp_arena = &global_temp_arena_;
 
#define unpackGlobals                                               \
  Tokenizer   *tk         = global_tokenizer;  (void) tk;           \
  MemoryArena *temp_arena = global_temp_arena; (void) temp_arena;

enum ExpressionCategory
{
  // right after parsing
  EC_Identifier,
  EC_AbstractFork,

  // built expressions
  EC_Variable,
  EC_Constant,

  EC_Application,               // operator application
  EC_Fork,                      // switch statement
  EC_Form,                      // like Coq inductive types
  EC_Function,                  // holds actual computation (ie body that can be executed)
  EC_ArrowType,                 // type of procedure and built-in objects

  // typechecker commands
  EC_Sequence,                  // like scheme's "begin" keyword
  EC_RewriteCommand,

  // strictly non-values
  EC_Hole,                    // hole left in for type-checking
};

struct Expression
{
  ExpressionCategory cat;
  Token              token;
};

inline void
initExpression(Expression *in, ExpressionCategory cat, Token *token)
{
  in->cat   = cat;
  in->token = *token;
}

inline Expression *
newExpression_(MemoryArena *arena, ExpressionCategory cat, Token *token, size_t size)
{
  Expression *out = (Expression *)pushSize(arena, size);
  initExpression(out, cat, token);
  return out;
}

#define newExpression(arena, cat, token)        \
  (cat *) newExpression_(arena, EC_##cat, token, sizeof(cat))

b32 identicalB32(Expression *lhs, Expression *rhs);

#define castExpression(exp, Cat) (((exp)->cat == EC_##Cat) ? (Cat*)(exp) : 0)
#define caste(exp, Cat) castExpression(exp, Cat)

struct Identifier
{
  Expression h;
};

struct Variable
{
  Expression  h;

  Token  name; // todo this information might be duplicated
  s32    id;
  s32    stack_delta;
  s32    stack_depth;
  Expression *type;
};

inline void
initVariable(Variable *var, Token *name, u32 id, Expression *type)
{
  var->name        = *name;
  var->stack_delta = 0;
  var->id          = id;
  var->stack_depth = 0;
  var->type        = type;
}

struct AbstractFork
{
  Expression   h;
  Expression  *subject;
  s32          case_count;
  Expression **patterns;
  Expression **bodies;
};

struct Constant
{
  Expression  h;
  Expression *value;
};

inline void
initIdentifier(Constant *in, Expression *value)
{
  in->value = value;
}

struct Application
{
  Expression   h;
  Expression  *type; // for caching
  Expression  *op;
  s32          arg_count;
  Expression **args;
};

inline void
initApplication(Application *app, Expression *op, s32 arg_count, Expression **args)
{
  app->type      = 0;
  app->op        = op;
  app->arg_count = arg_count;
  app->args      = args;
}

struct ForkCase
{
  Expression  *body;
  Variable   **params;
};
inline void
initForkCase(ForkCase *fork_case, Expression *body, Variable **params, s32 param_count)
{
  if (param_count)
    assert(params);
  fork_case->body   = body;
  fork_case->params = params;
}

struct ArrowType
{
  Expression   h;
  s32          param_count;
  Variable   **params;
  Expression  *return_type;
};

inline void
initArrowType(ArrowType *in, s32 param_count, Variable **params, Expression *return_type)
{
  in->param_count = param_count;
  in->params      = params;
  in->return_type = return_type;
}

struct Sequence
{
  Expression   h;
  s32          count;
  Expression **items;
};

inline void
initSequence(Sequence *in, s32 count, Expression **items)
{
  assert(count);
  in->count = count;
  in->items = items;
}

struct RewriteCommand
{
  Expression h;

  Expression *lhs;
  Expression *rhs;

  Expression *proof;
};

struct Form
{
  Expression  h;

  Token       name;
  Expression *type;

  s32 ctor_id;

  s32   ctor_count;
  Form *ctors;
};

inline Form *
getFormOf(Expression *in0)
{
  Form *out = 0;
  switch (in0->cat)
  {
    case EC_Application:
    {
      Application *in = castExpression(in0, Application);
      out = castExpression(in->op, Form);
    } break;

    case EC_Form:
    {
      out = castExpression(in0, Form);
    } break;

    invalidDefaultCase;
  }
  return out;
}

inline void
initForm(Form *in, Token *name, Expression *type0, s32 ctor_count, Form *ctors, s32 ctor_id)
{
  *in = {};
  in->h.cat      = EC_Form;
  in->name       = *name;
  in->type       = type0;
  in->ctor_count = ctor_count;
  in->ctors      = ctors;
  in->ctor_id    = ctor_id;
}

inline void
initForm(Form *in, Token *name, Expression *type0, s32 ctor_id)
{
  *in = {};
  in->h.cat = EC_Form;
  in->name  = *name;
  in->type  = type0;
  in->ctor_id = ctor_id;
}

struct Fork
{
  Expression h;

  Form       *form;
  Expression *subject;
  s32         case_count;
  ForkCase   *cases;
};

inline void
initFork(Fork *out, Form *form, Expression *subject, s32 case_count, ForkCase *cases)
{
  out->form       = form;
  out->subject    = subject;
  out->case_count = case_count;
  out->cases      = cases;

  for (s32 case_id = 0; case_id < case_count; case_id++)
    assert(out->cases[case_id].body);
}

struct Function
{
  Expression  h;
  Token       name;
  Expression *body;
  ArrowType  *signature;
};

inline void
initFunction(Function *fun, Token *name, Expression *body)
{
  assert(body);
  fun->name = *name;
  fun->body = body;
}

struct ParseExpressionOptions
{
  s32 min_precedence = -9999;
};

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
  Stack       *outer;
  s32          arg_count;
  Expression **args;
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
extendStack(Environment *env, s32 arg_count, Expression **args)
{
  Stack *stack = pushStruct(env->temp_arena, Stack);
  stack->outer     = env->stack;
  stack->arg_count = arg_count;
  stack->args      = args;

  env->stack = stack;
  env->stack_depth++;
}

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
  return out;
}

enum AstCategory
{
  AC_AstLeaf,
  AC_AstBranch,
  AC_AstFork,
  AC_AstArrowType,
  AC_AstSequence,
  AC_AstRewriteCommand,
};

struct Ast
{
  AstCategory cat;
  // info error reports & debug.  TODO: token is not quite what we want for the
  // ast since one ast might span multiple tokens, but it'll do for now.
  Token token;
};

#define castAst(ast, type) (type*)((ast->cat == AC_##type) ? ast : 0)

inline void
initAst(Ast *out, AstCategory cat, Token *token)
{
  out->cat   = cat;
  out->token = *token;
}

inline Ast *
newAst_(MemoryArena *arena, AstCategory cat, Token *token, size_t size)
{
  Ast *out = (Ast*)pushSize(arena, size);
  initAst(out, cat, token);
  return out;
}
#define newAst(arena, cat, token)                \
  (cat *) newAst_(arena, AC_##cat, token, sizeof(cat))

struct AstLeaf
{
  Ast h;
};

inline AstLeaf *
newAstLeaf(MemoryArena *arena, Token *token)
{
  AstLeaf *out = newAst(arena, AstLeaf, token);
  return out;
}

// todo: we can just store the args inline?
struct AstBranch
{
  Ast   h;
  Ast  *op;
  s32   arg_count;
  Ast **args;
};

struct AstFork
{
  Ast   h;
  Ast  *subject;
  s32   case_count;
  Ast **patterns; // todo omg so many pointers
  Ast **bodies;
};

inline AstFork *
newAstFork(MemoryArena *arena, Token *token,
             Ast *subject, s32 case_count, Ast **patterns, Ast **bodies)
{
  AstFork * out = newAst(arena, AstFork, token);

  out->subject    = subject;
  out->case_count = case_count;
  out->patterns   = patterns;
  out->bodies     = bodies;

  return out;
}

struct AstSequence
{
  Ast   h;
  s32   count;
  Ast **items;
};

inline AstSequence *
newAstSequence(MemoryArena *arena, Token *token, s32 count, Ast **items)
{
  AstSequence *out = newAst(arena, AstSequence, token);
  out->count = count;
  out->items = items;
  return out;
}

struct AstRewriteCommand
{
  Ast  h;

  // note: lean on computation
  Ast *lhs;
  Ast *rhs;
  // note: based on a proof object (mutually exclusive with lhs => rhs)
  Ast *proof;
};

inline void
initAstRewriteCommand(AstRewriteCommand *in, Ast *lhs, Ast *rhs)
{
  in->lhs = lhs;
  in->rhs = rhs;
  in->proof = 0;
}

inline void
initAstRewriteCommand(AstRewriteCommand *in, Ast *expression)
{
  in->lhs = 0;
  in->rhs = 0;
  in->proof = expression;
}

struct Parameter
{
  Token  name;
  Ast   *type;
};

inline Parameter *
initParameter(Parameter *out, Token *token, Ast *type)
{
  out->name = *token;
  out->type = type;
  return out;
}

struct ParameterList{s32 count; Parameter *items;};

struct AstArrowType
{
  Ast        h;
  s32        param_count;
  Parameter *params;
  Ast       *return_type;
};

inline AstArrowType *
initAstArrowType(AstArrowType *out, s32 param_count, Parameter *params, Ast *return_type)
{
  out->param_count = param_count;
  out->params      = params;
  out->return_type = return_type;
  return out;
}

inline Ast *
parseExpressionToAst(MemoryArena *arena);

struct AstList
{
  Ast     *first;
  AstList *next;
};

#define castValue(value, category) ((value->cat == VC_##category) ? (category*)value : 0)

enum ValueCategory
{
  VC_ParameterV,
  VC_StackValue,
  VC_ApplicationV,
  VC_FormV,
  VC_FunctionV,
  VC_ArrowTypeV,
};

struct Value
{
  ValueCategory cat;
};

struct StackValue
{
  Value h;

  String name;
  s32    stack_depth;
};

struct ParameterV
{
  Value h;

  String name;
  Value *type;
};

struct ApplicationV
{
  Value h;

  Value  *op;
  s32     arg_count;
  Value **args;
};

struct FormV
{
  Value h;

  Token  name;
  Value *type;

  s32 ctor_id;

  s32   ctor_count;
  Form *ctors;
};

struct FunctionV
{
  Value h;
  Token name;
  Expression *body;
};

struct ArrowTypeV
{
  Value        h;

  s32          param_count;
  Variable   **params;
  Expression  *return_type;
};

struct Binding
{
    String      key;
    Expression *value;
    Binding    *next;
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
  Bindings *out = pushStructZero(arena, Bindings);
  out->next  = outer;
  out->arena = arena;
  return out;
}

struct ValueBinding
{
  String        key;
  Value        *value;
  ValueBinding *next;
};

inline ValueBindings
toValueBindings(Bindings *bindings)
{
  return ValueBindings{bindings};
}

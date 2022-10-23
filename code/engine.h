#pragma once

#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena  global_temp_arena_;
global_variable MemoryArena *global_temp_arena = &global_temp_arena_;

#define unpackGlobals                                               \
  Tokenizer   *tk         = global_tokenizer;  (void) tk;           \
  MemoryArena *temp_arena = global_temp_arena; (void) temp_arena;

enum ExpressionCategory
{
  // might be free or bound
  EC_Variable,                // reference to some unknown on "the stack"

  // ground values
  EC_Application,             // operator application
  EC_Fork,                  // switch statement
  EC_Form,                    // like Coq inductive types
  EC_Constructor,             // canonical members of forms
  EC_Function,               // holds actual computation (ie body that can be executed)
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

global_variable Expression *builtin_identical;
global_variable Expression *builtin_identical_macro;
global_variable Expression *builtin_True;
global_variable Expression *builtin_truth;
global_variable Expression *builtin_False;
global_variable Expression *builtin_Set;
global_variable Expression *builtin_Prop;
global_variable Expression *builtin_Fun;
global_variable Expression *builtin_Type;
global_variable Expression *hole_expression;

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
initForkCase(ForkCase *fork_case, Expression *body, Variable **params, s32 param_count)
{
  if (param_count)
    assert(params);
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
struct Function
{
  Expression  h;
  String      name;
  Expression *body;
};

inline void
initFunction(Function *fun, String name, Expression *body)
{
  assert(body);
  fun->name = name;
  fun->body = body;
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

struct TypeDebt
{
  Function *first;
  TypeDebt *next;
};

// used in normalization, typechecking, etc.
struct Environment
{
  MemoryArena *arena;
  MemoryArena *temp_arena;

  TypeDebt *debt;
  s32 stack_depth;              // 0 is reserved
  s32 stack_offset;             // todo #speed pass this separately

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
  return out;
}

enum AstCategory
{
  AC_AstLeaf,
  AC_AstBranch,
  AC_AstFork,
  AC_AstArrowType,
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
  Ast **patterns;
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

struct Parameter
{
  String  name;
  Ast    *type;
};

inline Parameter *
initParameter(Parameter *out, Token *token, Ast *type)
{
  out->name = token->text;
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

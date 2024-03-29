#if !defined(PARSER_H)

#include "lexer.h"

global_variable i32 DEBUG_SERIAL;

struct ArrowAst;
enum AstKind {
  Ast_Hole = 1,
  Ast_QuestionMark,
  Ast_NormalizeMeAst,
  Ast_SyntheticAst,
  Ast_Identifier,

  // Expressions
  Ast_TypedExpression,
  Ast_CompositeAst,
  Ast_ArrowAst,
  Ast_AccessorAst,
  Ast_FunctionAst,
  Ast_OverloadAst,
  Ast_CtorAst,
  Ast_SeekAst,
  Ast_ReductioAst,
  Ast_ListAst,
  Ast_SubstAst,
  Ast_AlgebraNormAst,
  // Ast_NewLetAst,
  Ast_LetEqAst,

  // Sequence
  Ast_ForkAst,
  Ast_RewriteAst,
  Ast_FunctionDecl,
  Ast_LetAst,
  Ast_UnionAst,
  Ast_GoalTransform,
  Ast_Invert,
  Ast_AliasAst,
};

const u32 AstFlag_Generated = 1 << 0;
const u32 AstFlag_IsBuiltin = 1 << 1;

struct Ast {
  AstKind kind;
  Token token;
  u32   flags;
  u32   serial;
};

inline void
initAst(Ast *in, AstKind cat, Token *token)
{
  in->kind   = cat;
  in->token  = *token;
  in->serial = DEBUG_SERIAL++;
  if (in->serial == 3129)
    breakhere;
}

inline Ast *
newAst_(Arena *arena, AstKind cat, Token *token, size_t size)
{
  Ast *out = (Ast *)pushSize(arena, size, true);
  initAst(out, cat, token);
  return out;
}

#define newAst(arena, cat, token)        \
  ((cat *) newAst_(arena, Ast_##cat, token, sizeof(cat)))

#define castAst(exp, Cat) ((exp)->kind == Ast_##Cat ? (Cat*)(exp) : 0)
#define castTerm(exp, Cat) (((exp) && (exp)->kind == Term_##Cat) ? (Cat*)(exp) : 0)

struct Identifier : Ast {
  // NOTE: Since the ast has a token, which already has the identifier in it, we
  // don't need to put it in the identifier struct.

  // An exception would be when you need to generate an Identifier for whatever
  // messed up reason, then you can just make a fake token.
};

typedef Ast Hole;
typedef Ast QuestionMark;
typedef Ast AlgebraicManipulation;

struct ForkAst : Ast {
  Ast    *subject;
  i32     case_count;
  Ast   **cases;
  Token  *ctors;
};

struct AstList
{
  Ast     *head;
  AstList *tail;
};

struct LetAst : Ast {
  String  lhs;
  Ast    *rhs;
  Ast    *type;
  Ast    *body;
};

struct NewLetAst : Ast {
  String  lhs;
  Ast    *rhs;
  Ast    *type;
  Ast    *body;
};

struct CompositeAst : Ast {
  Ast  *op;
  i32   arg_count;
  Ast **args;

  String *keywords;
  b32     partial_args;

  Ast *reduce_proof;
};

struct ArrowAst : Ast {
  i32     param_count;
  String *param_names;
  Ast   **param_types;
  u32    *param_flags;
  Ast    *output_type;
};

struct RewriteAst : Ast {
  Ast *eq_or_proof;

  Ast *new_goal;
  Ast *body;
  b32  right_to_left;
  Ast *in_expression;
};

struct GoalTransform : Ast {
  Ast *hint;
  Ast *new_goal;
  b32  print_proof;
  Ast *body;
};

struct Invert : Ast {
  Ast *pointer;
  Ast *body;
};

struct AliasAst : Ast {
  String  name;
  Ast    *value;
  Ast    *body;
};

struct AccessorAst : Ast {
  Ast   *record;
  Token  field_name;           // parsing info
};

struct FunctionAst : Ast {
  ArrowAst *signature;
  Ast      *body;
  u32       function_flags;

  String builtin_name;

  String *tags;

  FunctionAst *measure_function;
  Ast         *well_founded_proof;
};

struct UnionAst : Ast {
  i32        ctor_count;
  Token     *ctor_names;
  ArrowAst **ctor_signatures;
  ArrowAst  *signature;

  String builtin_name;
};

struct OverloadAst : Ast {
  String function_name;
  String distinguisher;
};

struct CtorAst : Ast {
  i32  ctor_i;
};

struct SeekAst : Ast {
  Ast *proposition;
};

struct ReductioAst : Ast {};

struct TypedExpression : Ast {
  Ast *type;
  Ast *expression;
};

struct ListAst : Ast {
  i32   count;
  Ast **items;
  Ast  *tail;
};

struct SubstAst : Ast {
  i32   count;
  Ast **to_rewrite;
  Ast  *body;
};

struct AlgebraNormAst : Ast {
  Ast *expression;
  Ast *body;
};

struct LetEqAst : Ast {
  Token  let_pointer;
  Ast   *body;
  String name;
};

#define PARSER_H
#endif

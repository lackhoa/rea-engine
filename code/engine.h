#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable MemoryArena __attribute__((unused)) *temp_arena;
global_variable b32 __attribute__((unused)) global_debug_mode;
global_variable MemoryArena __attribute__((unused))*permanent_arena;

struct Term;
struct ArrowAst;
struct LocalBindings;

enum AstCategory {
  AC_Null = 0,
  // hole left in for type-checking
  AC_Hole,
  // result after initial parsing
  AC_Identifier,

  // Expressions
  AC_Constant,
  AC_Variable,
  AC_CompositeAst,
  AC_ArrowAst,
  AC_AccessorAst,
  AC_ComputationAst,
  AC_Lambda,

  // Stuff in "sequence" context only, not general expressions.
  AC_Sequence,
  AC_Fork,
  AC_RewriteAst,
  AC_FunctionDecl,
  AC_Let,
};

enum TermCategory {
  Term_Null = 0,
  Term_Hole,
  Term_Builtin,

  // todo maybe we can carve out "Value" from here
  Term_Union,
  Term_Constructor,
  Term_Function,

  Term_Computation,
  Term_StackValue,
  Term_Accessor,
  Term_Composite,
  Term_Arrow,
  Term_Rewrite,
};

embed_struct struct Ast
{
  AstCategory cat;
  Token       token;
};

inline Ast **
toAsts(Term **values)
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

#define castTerm(exp, Cat) ((exp)->cat == Term_##Cat ? (Cat*)(exp) : 0)

struct Hole       {embed_Ast(a)};
struct Identifier {embed_Ast(a)};

struct Variable
{
  embed_Ast(a);

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
  Term *value;
  b32    is_synthetic;
};

struct Sequence
{
  Ast a;

  Ast **items;
  s32   count;
};

inline Constant *
newSyntheticConstant(MemoryArena *arena, Term *value)
{
  Token token = newToken("<synthetic>");
  Constant *out = newAst(arena, Constant, &token);
  out->is_synthetic = true;
  out->value        = value;
  return out;
}

inline Constant *
newSyntheticConstant(MemoryArena *arena, Term *value, Token *token)
{
  Constant *out = newAst(arena, Constant, token);
  out->is_synthetic = true;
  out->value        = value;
  return out;
}

struct ForkParsing
{
  Identifier *ctors;
};

struct Union;

struct Fork {
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

struct OverwriteRules
{
  Term *lhs;
  Term *rhs;
  OverwriteRules *next;
};

struct Stack
{
  Stack *outer;
  s32    depth;
  s32    count;
  Term *items[32];              // todo: compute this cap
};

// used in normalization, build/typecheck, etc.
struct Environment
{
  LocalBindings  *bindings;
  Stack          *stack;
  OverwriteRules *overwrite;
};

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

embed_struct struct Term
{
  TermCategory  cat;
  Term         *type;
};

typedef Term Builtin;

inline void
initValue(Term *in, TermCategory cat, Term *type)
{
  in->cat  = cat;
  in->type = type;
}

inline Term *
newTerm_(MemoryArena *arena, TermCategory cat, Term *type, size_t size)
{
  Term *out = (Term *)pushSize(arena, size, true);
  initValue(out, cat, type);
  return out;
}

#define newTerm(arena, cat, type)              \
  ((cat *) newTerm_(arena, Term_##cat, type, sizeof(cat)))

struct Constructor
{
  embed_Term(v);
  Union *uni;
  Token  name;
  s32    id;
};

struct Union
{
  embed_Term(v);
  Token name;

  s32          ctor_count;
  Constructor *ctors;
};

struct FunctionDecl {
  Ast       a;
  ArrowAst   *signature;
  Sequence *body;
};

struct Function
{
  embed_Term(v);
  Token     name;
  Sequence *body;
  Stack    *stack;  // nocheckin wtf does this do?
};

Ast LET_TYPE_NORMALIZE_;
Ast *LET_TYPE_NORMALIZE = &LET_TYPE_NORMALIZE_;
struct Let
{
  embed_Ast(a);
  Token  lhs;
  Ast   *rhs;
  Ast   *type;
};

struct StackValue
{
  Term v;

  Token name;
  s32   id;
  s32   stack_depth;
};

struct TreePath
{
  s32       first;  // -1 for op
  TreePath *next;
};

struct Accessor
{
  embed_Term(v);
  Term *record;
  s32    field_id;
  String field_name;            // #todo #debug_only
};

struct CompositeAst
{
  embed_Ast(a);
  Ast  *op;
  s32   arg_count;
  Ast **args;
};

struct Composite
{
  embed_Term(v);
  Term  *op;
  s32     arg_count;
  Term **args;
};

inline void
initComposite(CompositeAst *app, Ast *op, s32 arg_count, Ast **args)
{
  app->op        = op;
  app->arg_count = arg_count;
  app->args      = args;
}

struct ArrowAst
{
  embed_Ast(a);
  i32     param_count;
  Token  *param_names;
  Ast   **param_types;
  Ast    *output_type;
};

struct Arrow
{
  Term v;
  s32     param_count;
  Token  *param_names;
  Term **param_types;
  Term  *output_type;
  s32     stack_depth;
};

struct GlobalBinding
{
  String key;
  s32    count;
  Term *(items[8]);           // todo: #grow
  GlobalBinding *next_hash_slot;
};

struct GlobalBindings  // :global-bindings-zero-at-startup
{
    GlobalBinding table[1024];
};

inline Union *
getConstructorOf(Term *in0)
{
  Union *out = 0;
  switch (in0->cat)
  {
    case Term_Composite:
    {
      if (Composite *in = castTerm(in0, Composite))
        out = castTerm(in->op, Union);
    } break;

    case Term_Union:
    {
      out = castTerm(in0, Union);
    } break;

    invalidDefaultCase;
  }
  return out;
}

struct Expression
{
  Ast   *ast;
  Term *value;
  operator bool() { return ast && value; }
};

struct RewriteAst
{
  embed_Ast(a);
  TreePath *path;
  Ast      *eq_proof;
  Ast      *to_expression;
  b32       right_to_left;
};

struct AccessorAst
{
  Ast    a;

  Ast   *record;                // in parse phase we can't tell if the op is a constructor
  Token  field_name;           // parsing info
  s32    field_id;              // after build phase
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

struct PrintOptions{b32 detailed; b32 print_type; s32 indentation; int no_paren_precedence;};

struct Builtins
{
  Union       *True;
  Constructor *truth;
  Union       *False;
  Builtin     *equal;
  Builtin     *Set;
  Builtin     *Type;
  Constructor *refl;
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
    Term *Exact;
    Term *OutType;
  };
  operator bool() { return (cat == MC_Exact) && (Exact == 0); }
};

inline Matcher exactMatch(Term *value)
{
  return Matcher{.cat=MC_Exact, .Exact=value};
}

struct ValueArray
{
  s32     count;
  Term **items;
};

struct AstArray
{
  s32    count;
  Term *items;
};

struct Rewrite
{
  embed_Term(v);
  TreePath  *path;
  Term     *eq_proof;
  b32        right_to_left;
  Term     *body;
};

struct ComputationAst {
  embed_Ast(a);
  Ast *lhs;
  Ast *rhs;
};

struct Computation {
  embed_Term(v);
  Term *lhs;
  Term *rhs;
};

struct SearchOutput {b32 found; TreePath *path;};

struct CompareExpressions {Trinary result; TreePath *diff_path;};

struct Lambda {
  embed_Ast(a);
  ArrowAst   *signature;
  Sequence *body;
};

#include "generated/engine_forward.h"

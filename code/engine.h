#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable MemoryArena *temp_arena;
global_variable b32          global_debug_mode;
global_variable MemoryArena *global_arena;
global_variable i32          global_debug_serial;

struct Constructor;
struct Term;
struct ArrowAst;
struct LocalBindings;

enum AstCategory {
  AC_Hole = 1,  // hole left in for type-checking
  AC_SyntheticAst,
  AC_Identifier, // result after initial parsing

  // Expressions
  AC_CompositeAst,
  AC_ArrowAst,
  AC_AccessorAst,
  AC_ComputationAst,
  AC_Lambda,

  AC_ForkAst,
  AC_RewriteAst,
  AC_FunctionDecl,  // todo: #cleanup probably don't need this anymore
  AC_Let,
};

enum TermCategory {
  Term_Hole        = 1,
  Term_Builtin     = 2,
  /* Term_Constant    = 3, */
  Term_Union       = 4,
  Term_Constructor = 5,
  Term_Function    = 6,
  Term_Fork        = 7,
  Term_Variable    = 8,
  Term_Computation = 9,
  Term_Accessor    = 10,
  Term_Composite   = 11,
  Term_Arrow       = 12,
  Term_Rewrite     = 13,
};

embed_struct struct Ast {
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

struct Hole       {embed_Ast(a);};
struct Identifier {embed_Ast(a);};

struct Union;

struct ForkAst {
  embed_Ast(a);

  Ast    *subject;
  i32     case_count;
  Ast   **bodies;
  Token  *ctors;
};

struct ParseExpressionOptions
{
  s32 min_precedence = -9999;
};


struct Trinary {i32 v;};
Trinary Trinary_False   = Trinary{0};
Trinary Trinary_True    = Trinary{1};
Trinary Trinary_Unknown = Trinary{2};
Trinary toTrinary(b32 v)
{
  if (v == 0) return Trinary_False;
  else return Trinary_True;
}

b32 operator==(Trinary a, Trinary b)
{
  return a.v == b.v;
}

b32 operator!=(Trinary a, Trinary b)
{
  return a.v != b.v;
}

struct ConstructorMap {
  Term           *term;
  i32             depth;
  Constructor    *ctor;
  ConstructorMap *next;
};

struct Stack
{
  Stack  *outer;
  i32     depth;
  i32     cap;
  i32     count;
  Term **items;
  i32     last_function_id;
};

struct Typer
{
  LocalBindings  *bindings;
  Stack          *type_stack;
  ConstructorMap *map;
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

embed_struct struct Term {
  TermCategory  cat;
  Term         *type;
  Token        *global_name;
  i32           serial;
};

struct Builtin {embed_Term(t);};

inline void
initTerm(Term *in, TermCategory cat, Term *type)
{
  in->cat  = cat;
  in->type = type;
}

inline Term *
_newTerm(MemoryArena *arena, TermCategory cat, Term *type, size_t size)
{
  Term *out = (Term *)pushSize(arena, size, true);
  initTerm(out, cat, type);
  out->serial = global_debug_serial++;
  return out;
}

#define newTerm(arena, cat, type)              \
  ((cat *) _newTerm(arena, Term_##cat, type, sizeof(cat)))

struct Constructor {
  embed_Term(t);
  Token  name;
  Union *uni;
  i32    id;
};

struct Union {
  embed_Term(t);
  i32          ctor_count;
  Constructor *ctors;
};

struct FunctionDecl {
  Ast       a;
  ArrowAst *signature;
  Ast      *body;
};

/* struct GlobalId {i32 v;}; */
struct Function {
  embed_Term(t);
  Term  *body;
};

Ast LET_TYPE_NORMALIZE_;
Ast *LET_TYPE_NORMALIZE = &LET_TYPE_NORMALIZE_;
struct Let {
  embed_Ast(a);
  Token  lhs;
  Ast   *rhs;
  Ast   *type;
  Ast   *body;
};

struct Variable {
  embed_Term(t);
  Token name;
  i32   id;
  i32   stack_delta;
  /* b32   is_absolute;  // #debug-only */
};

struct TreePath {
  i32       first;  // -1 for op
  TreePath *next;
};

struct Accessor {
  embed_Term(t);
  Term   *record;
  i32     field_id;
  String  field_name;           // #todo #debug_only
};

struct CompositeAst {
  embed_Ast(a);
  Ast  *op;
  i32   arg_count;
  Ast **args;
};

struct Composite {
  embed_Term(t);
  Term  *op;
  i32    arg_count;
  Term **args;
};

struct ArrowAst {
  embed_Ast(a);
  i32     param_count;
  Token  *param_names;
  Ast   **param_types;
  Ast    *output_type;
};

struct Arrow {
  embed_Term(t);
  s32     param_count;
  Token  *param_names;
  Term  **param_types;
  Term   *output_type;
};

struct GlobalBinding {
  String key;
  s32    count;
  Term *(items[8]);           // todo: #grow
  GlobalBinding *next_hash_slot;
};

struct GlobalBindings  // :global-bindings-zero-at-startup
{
    GlobalBinding table[1024];
};

struct BuildTerm
{
  Term *term;
  operator bool() { return term; }
};

struct RewriteAst
{
  embed_Ast(a);
  TreePath *path;
  Ast      *eq_proof_hint;
  Ast      *new_goal;
  Ast      *body;
  b32       right_to_left;
};

struct AccessorAst
{
  Ast    a;

  Ast   *record;                // in parse phase we can't tell if the op is a constructor
  Token  field_name;           // parsing info
  s32    field_id;              // after build phase
};

struct FileList {
  char     *first_path;
  char     *first_content;
  FileList *next;
};

struct EngineState {
  MemoryArena *arena;
  FileList    *file_list;
};

u32 PrintFlag_Detailed     = 1 << 1;
u32 PrintFlag_LockDetailed = 1 << 2;
u32 PrintFlag_PrintType    = 1 << 3;

struct PrintOptions{
  u32 flags;
  u16 indentation;
  u16 no_paren_precedence;
};

struct Builtins {
  Union       *True;
  Constructor *truth;
  Union       *False;
  Builtin     *equal;
  Builtin     *Set;
  Builtin     *Type;
};

enum MatcherCategory {
  MC_Unknown,
  MC_Exact,
  MC_OutputType,
};

struct Matcher {
  MatcherCategory cat;
  union
  {
    Term *Exact;
    Term *Output;
  };
  operator bool() { return (cat == MC_Exact) && (Exact == 0); }
};

inline Matcher exactMatcher(Term *value)
{
  return Matcher{.cat=MC_Exact, .Exact=value};
}

inline Matcher outputMatcher(Term *value)
{
  return Matcher{.cat=MC_Exact, .Output=value};
}

struct TermArray {
  i32    count;
  Term **items;
};

struct AstArray {
  i32   count;
  Term *items;
};

struct Rewrite {
  embed_Term(t);
  TreePath *path;
  b32       right_to_left;
  Term     *eq_proof;
  Term     *body;
};

struct ComputationAst {
  embed_Ast(a);
  Ast *lhs;
  Ast *rhs;
};

struct Computation {
  embed_Term(t);
  Term *lhs;
  Term *rhs;
};

struct SearchOutput {b32 found; TreePath *path;};

struct CompareTerms {Trinary result; TreePath *diff_path;};

struct Lambda {
  embed_Ast(a);
  Ast *signature;
  Ast *body;
};

struct TermPair
{
  Term *lhs;
  Term *rhs;
  operator bool() {return lhs && rhs;};
};

struct Fork {
  embed_Term(t);
  Union  *uni;
  Term   *subject;
  i32     case_count;
  Term  **bodies;
  Stack   stack;
};

struct SyntheticAst {
  embed_Ast(a);
  Term *term;
};

struct EvaluationContext {
  MemoryArena  *arena;
  Typer        *env;
  Term        **args;
  b32           normalize;
  i32           offset;
};

#include "generated/engine_forward.h"

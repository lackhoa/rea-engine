#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable Arena  temp_arena_;
global_variable Arena *temp_arena = &temp_arena_;
global_variable StringBuffer  error_buffer_;
global_variable StringBuffer *error_buffer = &error_buffer_;

global_variable b32 DEBUG_MODE;
global_variable i32 DEBUG_SERIAL;

struct Function;
struct Union;
struct Arrow;
struct Composite;
struct Constructor;
struct Term;
struct ArrowAst;
struct LocalBindings;
struct DataMap;

enum AstCategory {
  Ast_Hole = 1,                 // hole left in for type-checking
  Ast_NormalizeMeAst,
  Ast_Ellipsis,
  Ast_SyntheticAst,
  Ast_Identifier,               // result after initial parsing

  // Expressions
  Ast_CompositeAst,
  Ast_ArrowAst,
  Ast_AccessorAst,
  Ast_FunctionAst,
  Ast_OverloadAst,
  Ast_CtorAst,
  Ast_SeekAst,
  Ast_ReductioAst,

  // Sequence
  Ast_ForkAst,
  Ast_RewriteAst,
  Ast_FunctionDecl,
  Ast_Let,
  Ast_UnionAst,
  Ast_GoalTransform,
};

enum TermCategory {
  Term_Hole = 1,
  Term_PolyConstructor,

  Term_Primitive,
  Term_Union,
  Term_Constructor,
  // Term_PolyUnion,
  Term_Function,
  Term_Fork,
  Term_Variable,
  Term_Computation,
  Term_Accessor,
  Term_Composite,
  Term_Arrow,
  Term_Rewrite,
};

const u32 AstFlag_Generated = 1 << 0;

embed_struct struct Ast {
  AstCategory cat;
  Token       token;
  u32         flags;
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
newAst_(Arena *arena, AstCategory cat, Token *token, size_t size)
{
  Ast *out = (Ast *)pushSize(arena, size, true);
  initAst(out, cat, token);
  return out;
}

#define newAst(arena, cat, token)        \
  ((cat *) newAst_(arena, Ast_##cat, token, sizeof(cat)))

#define castAst(exp, Cat) ((exp)->cat == Ast_##Cat ? (Cat*)(exp) : 0)
#define polyAst(exp, Cat, Cat2) (((exp)->cat == Ast_##Cat || (exp)->cat == Ast_##Cat2) ? (Cat*)(exp) : 0)

#define castTerm(exp, Cat) ((exp)->cat == Term_##Cat ? (Cat*)(exp) : 0)

struct Identifier {
  embed_Ast(a);
  // NOTE: Since the ast has a token, which already has the identifier in it, we
  // don't need to put it in the identifier struct. But that might change.
};

typedef Ast Hole;
typedef Ast Ellipsis;
typedef Ast AlgebraicManipulation;

struct NormalizeMeAst {
  embed_Ast(a);
  String name_to_unfold;
};

struct ForkAst {
  embed_Ast(a);

  Ast    *subject;
  i32     case_count;
  Ast   **bodies;
  Token  *ctors;
};

struct ParseExpressionOptions
{
  i32 min_precedence = -9999;
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

struct DataTree {
  i32        ctor_i;
  i32        member_count;
  DataTree **members;
  String    *ctor_names;        // debug only
};

struct DataMapAddHistory {
  // option A: root 
  DataMap      *previous_map;
  // option B: branch
  DataTree     *parent;
  i32           field_index;

  DataMapAddHistory *previous;
};

struct DataMap {
  i32       depth;
  i32       index;
  DataTree  tree;
  DataMap  *tail;
};

struct Stack {
  i32     count;
  Term  **items;
  Stack  *outer;
  Arena *unification_arena;
};

struct Scope {
  Arrow *head;
  Scope *outer;
  i32    depth;
};

struct Typer
{
  Arena *build_arena;
  LocalBindings *bindings;
  Scope         *scope;
  Arrow         *poly_params;
  DataMap           *map;
  DataMapAddHistory *add_history;
  b32 try_reductio;
};

struct AstList
{
  Ast     *head;
  AstList *tail;
};

struct TermList
{
  Term     *head;
  TermList *tail;
};

embed_struct struct Term {
  TermCategory  cat;
  i32           serial;
  Term         *type;
  Token        *global_name;
};

struct Primitive {embed_Term(t);};

inline void
initTerm(Term *in, TermCategory cat, Term *type)
{
  in->cat  = cat;
  in->type = type;
}

struct Constructor {
  embed_Term(t);
  Term *uni;  // can be thought of as "output_type", minus the stupid rebase
  i32   index;
};

// NOTE: does not appear in expression.
struct PolyConstructor {
  embed_Term(t);
  Union *uni;                   // poly union
  i32    index;
};

struct Union {
  embed_Term(t);
  i32     ctor_count;
  String *ctor_names;
  Arrow **structs;
};

struct Function {
  embed_Term(t);
  Term *body;
  u32   function_flags;
};

struct Let {
  embed_Ast(a);
  String  lhs;
  Ast    *rhs;
  Ast    *type;
  Ast    *body;
};

struct LocalBinding
{
  i32           hash;
  String        key;
  i32           var_id;
  LocalBinding *tail;
};

struct LookupLocalName {
  b32   found;
  i32   stack_delta;
  i32   var_index;
  operator bool() {return found;}
};

struct LocalBindings
{
  Arena   *arena;
  LocalBinding   table[128];
  LocalBindings *tail;
};

struct Variable {
  embed_Term(t);
  String name;
  i32    delta;
  i32    index;
};

struct TreePath {
  i32       head;  // -1 for op
  TreePath *tail;
};

struct Accessor {
  embed_Term(t);
  Term   *record;
  i32     field_index;
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

u32 ParameterFlag_Inferred = 1 << 0;
u32 ParameterFlag_Unused   = 1 << 1;
u32 ParameterFlag_Poly     = 1 << 2;

struct ArrowAst {
  embed_Ast(a);
  i32     param_count;
  String *param_names;
  Ast   **param_types;
  u32    *param_flags;
  Ast    *output_type;
};

struct Arrow {
  embed_Term(t);
  i32     param_count;
  String *param_names;
  Term  **param_types;
  u32    *param_flags;
  Term   *output_type;
};

struct GlobalBinding {
  String key;
  i32    count;
  Term *(items[8]);             // todo: #grow
  GlobalBinding *hash_tail;
};

struct GlobalBindings  // :global-bindings-zero-at-startup
{
    GlobalBinding table[1024];
};

struct BuildTerm
{
  Term *term;
  operator bool() { return term; }
  operator Term*() { return term; }
};

struct RewriteAst
{
  embed_Ast(a);
  Ast      *eq_proof;
  Ast      *new_goal;
  Ast      *body;
  b32       right_to_left;
};

struct GoalTransform
{
  embed_Ast(a);
  Ast *hint;
  Ast *new_goal;
  Ast *body;
  b32  print_proof;
};

struct AccessorAst
{
  Ast    a;

  Ast   *record;                // in parse phase we can't tell if the op is a constructor
  Token  field_name;           // parsing info
};

struct FileList {
  char     *head_path;
  char     *head_content;
  FileList *tail;
};

// todo better hint lookup
struct HintDatabase {
  // wip: we probably only want functions in here, but let's store term to make
  // it play nice with the rest.
  Term         *head;
  HintDatabase *tail;
};

u32 PrintFlag_Detailed     = 1 << 0;
u32 PrintFlag_LockDetailed = 1 << 1;

struct PrintOptions {
  u32 flags;
  u16 indentation;
  u16 no_paren_precedence;
  i32 print_type_depth;
};

inline PrintOptions
printOptionPrintType(PrintOptions options={})
{
  options.print_type_depth = 1;
  return options;
}

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

// NOTE: rewrite is done from "type" to "body".
struct Rewrite {
  embed_Term(t);
  TreePath *path;
  b32       right_to_left;
  Term     *eq_proof;
  Term     *body;
};

typedef Term Computation;

struct SearchOutput {b32 found; TreePath *path;};

struct CompareTerms {Trinary result; TreePath *diff_path;};

const u32 FunctionFlag_is_global_hint         = 1 << 0;
const u32 FunctionFlag_no_apply               = 1 << 1;
const u32 FunctionFlag_no_print_as_binop      = 1 << 2;
const u32 FunctionFlag_expand                 = 1 << 3;

struct FunctionAst {
  embed_Ast(a);
  ArrowAst *signature;
  Ast      *body;
  u32       function_flags;
};

struct TermPair
{
  Term *lhs;
  Term *rhs;
  operator bool() {return lhs && rhs;};
};

struct Fork {
  embed_Term(t);
  Term   *subject;
  i32     case_count;
  Term  **bodies;
};

struct SyntheticAst {
  embed_Ast(a);
  Term *term;
};

const u32 EvaluationFlag_AlwaysApply = 1 << 0;

struct EvaluationContext {
  Arena  *arena;
  Term        **args;
  Term        **poly_args;
  i32           offset;
  u32           flags;
};

struct UnionAst {
  embed_Ast(a);
  i32        ctor_count;
  Token     *ctor_names;
  ArrowAst **structs;
  ArrowAst  *params;
};

struct OverloadAst {
  embed_Ast(a);
  Token  function_name;
  Ast   *distinguisher;
};

struct CtorAst {
  embed_Ast(a);
  i32  ctor_i;
};

struct AddDataTree {
  DataTree *tree;
  b32       added;
};

struct SeekAst {
  embed_Ast(a);
  Ast *proposition;
};

struct ReductioAst {
  embed_Ast(a);
};

struct SolveArgs {i32 arg_count; Term **args;};

#define MAX_SOLVE_DEPTH 3
struct Solver {
  Arena  *arena;
  Typer        *typer;
  b32           use_global_hints;
  b32           try_reductio;
  HintDatabase *local_hints;
  i32           depth;
  operator Solver*() {return this;}
};

struct Algebra {
  Term *type;

  Term *add;
  Term *addCommutative;
  Term *addAssociative;

  Term *mul;
  Term *mulCommutative;
  Term *mulAssociative;

  Term *mulDistributive;
};

struct AlgebraDatabase {
  Algebra          head;
  AlgebraDatabase *tail;
};

// :global_state_cleared_at_startup
struct EngineState {
  Arena     *top_level_arena;
  FileList        *file_list;
  GlobalBindings  *bindings;
  HintDatabase    *hints;
  AlgebraDatabase *algebras;
};

struct TreePathList {
  TreePath     *head;
  TreePathList *tail;
};

struct NormalizeContext {
  Arena *arena;
  DataMap     *map;
  i32          depth;
  String       name_to_unfold;
};

struct LookupPolyParameter {
  b32 found;
  i32 index;
  operator bool() { return found; }
};

#define DEFAULT_MAX_LIST_LENGTH 64

internal BuildTerm
buildTerm(Arena *arena, Typer *typer, Ast *in0, Term *goal, b32 expect_error=false);

#include "generated/engine_forward.h"

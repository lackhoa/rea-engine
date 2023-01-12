#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "tokenization.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable MemoryArena  temp_arena_;
global_variable MemoryArena *temp_arena = &temp_arena_;
global_variable StringBuffer  error_buffer_;
global_variable StringBuffer *error_buffer = &error_buffer_;

global_variable b32 DEBUG_MODE;
global_variable i32 DEBUG_SERIAL;

struct Union;
struct Arrow;
struct Composite;
struct Constructor;
struct Term;
struct ArrowAst;
struct LocalBindings;
struct DataMap;

enum AstCategory {
  Ast_Hole         = 1,         // hole left in for type-checking
  Ast_Ellipsis     = 2,
  Ast_SyntheticAst = 3,
  Ast_Identifier   = 4,         // result after initial parsing

  // Expressions
  Ast_CompositeAst   = 5,
  Ast_ArrowAst       = 6,
  Ast_AccessorAst    = 7,
  Ast_ComputationAst = 8,
  Ast_Lambda         = 9,
  // Ast_DestructAst    = 10,
  Ast_CtorAst        = 11,
  Ast_SeekAst        = 12,
  Ast_Auto           = 13,

  // Sequence
  Ast_ForkAst       = 14,
  Ast_RewriteAst    = 15,
  Ast_FunctionDecl  = 16,
  Ast_Let           = 17,
  Ast_UnionAst      = 18,
  Ast_GoalTransform = 19,
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
newAst_(MemoryArena *arena, AstCategory cat, Token *token, size_t size)
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
typedef Ast Auto;

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
  Union     *uni;
  i32        ctor_id;
  i32        member_count;
  DataTree **members;
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
  DataMap  *next;
};

struct Stack {
  i32     count;
  Term  **items;
  Stack  *outer;
};

struct Scope {
  Arrow *first;
  Scope *outer;
  i32    depth;
};

struct Typer
{
  LocalBindings *bindings;
  Scope         *scope;
  DataMap       *map;
  DataMapAddHistory *add_history;
};

struct AstList
{
  Ast     *first;
  AstList *next;
};

struct TermList
{
  Term     *first;
  TermList *next;
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
  out->serial = DEBUG_SERIAL++;
  return out;
}

#define newTerm(arena, cat, type)              \
  ((cat *) _newTerm(arena, Term_##cat, type, sizeof(cat)))

struct Constructor {
  embed_Term(t);
  Union  *uni;
  i32     id;
};

struct Union {
  embed_Term(t);
  i32      ctor_count;
  String  *ctor_names;
  Arrow  **structs;
};

// NOTE: For now, this FunctionDecl ast only holds global function only so it's
// redundant. But we might allow local function definitions later.
struct FunctionDecl {
  embed_Ast(a);
  ArrowAst *signature;
  Ast      *body;
  b32       add_to_global_hints;
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
  LocalBinding *next;
};

struct LookupLocalName {
  b32   found;
  i32   stack_delta;
  i32   var_id;
  operator bool() {return found;}
};

struct LocalBindings
{
  MemoryArena   *arena;
  LocalBinding   table[128];
  LocalBindings *next;
};

struct Variable {
  embed_Term(t);
  String name;
  i32    delta;
  i32    id;
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

u32 ParameterFlag_Hidden = 1 << 0;

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
  Ast *new_goal;  // NOTE: 0 means "the normalized version of the current goal"
  Ast *body;
};

struct AccessorAst
{
  Ast    a;

  Ast   *record;                // in parse phase we can't tell if the op is a constructor
  Token  field_name;           // parsing info
  i32    field_id;              // after build phase
};

struct FileList {
  char     *first_path;
  char     *first_content;
  FileList *next;
};

// todo better hint lookup
struct HintDatabase {
  // wip: we probably only want functions in here, but let's store term to make
  // it play nice with the rest.
  Term         *first;
  HintDatabase *next;
};

// :global_state_cleared_at_startup
struct EngineState {
  MemoryArena    *top_level_arena;
  FileList       *file_list;
  GlobalBindings *bindings;
  HintDatabase   *hints;
};

u32 PrintFlag_Detailed     = 1 << 0;
u32 PrintFlag_LockDetailed = 1 << 1;
u32 PrintFlag_PrintType    = 1 << 2;

struct PrintOptions {
  u32 flags;
  u16 indentation;
  u16 no_paren_precedence;
};

inline PrintOptions
printOptionPrintType(PrintOptions options={})
{
  setFlag(&options.flags, PrintFlag_PrintType);
  return options;
}

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

// NOTE: rewrite is done from "type" to "body", which is arguably backward (todo change it).
struct Rewrite {
  embed_Term(t);
  TreePath *path;
  b32       right_to_left;
  Term     *eq_proof;
  Term     *body;
};

struct ComputationAst {
  embed_Ast(a);
  // todo #cleanup we won't need lhs and rhs anymore since types are there.
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
};

struct SyntheticAst {
  embed_Ast(a);
  Term *term;
};

// todo Doesn't seem like we need both these flags, since "apply" is the only
// place to sets both of those flags.
const u32 UNUSED_VAR EvaluationFlag_ApplyMode = 1 << 0;

struct EvaluationContext {
  MemoryArena  *arena;
  Term        **args;
  i32           offset;
  u32           flags;
};

struct UnionAst {
  embed_Ast(a);
  i32        ctor_count;
  Token     *ctor_names;
  ArrowAst **ctor_signatures;
};

struct DestructAst {
  embed_Ast(a);
  i32  arg_id;
  Ast *eqp;
};

struct CtorAst {
  embed_Ast(a);
  i32  ctor_id;
  Ast *uni;  // todo implement
};

struct AddDataTree {
  DataTree *tree;
  b32       added;
};

struct SeekAst {
  embed_Ast(a);
  Ast *proposition;
};

struct SolveArgs {b32 matches; i32 arg_count; Term **args;};

#define MAX_SOLVE_DEPTH 3
struct Solver {
  MemoryArena  *arena;
  Typer        *env;
  HintDatabase *local_hints;
  i32           depth;
  b32           use_global_hints;
};

#include "generated/engine_forward.h"

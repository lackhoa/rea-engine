#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "lexer.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable Arena  temp_arena_;
global_variable Arena *temp_arena = &temp_arena_;
global_variable StringBuffer  error_buffer_;
global_variable StringBuffer *error_buffer = &error_buffer_;

global_variable i32 DEBUG_SERIAL;

struct Function;
struct Union;
struct Arrow;
struct Composite;
// NOTE: I almost think records are different cases from composites, just a
// coincidence that they are represented the same way.
typedef Composite Record;
struct Constructor;
struct Term;
struct ArrowAst;
struct LocalBindings;
struct DataMap;

enum AstKind {
  Ast_Hole = 1,                 // hole left in for type-checking
  Ast_NormalizeMeAst,
  Ast_Ellipsis,
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

  // Sequence
  Ast_ForkAst,
  Ast_RewriteAst,
  Ast_FunctionDecl,
  Ast_Let,
  Ast_UnionAst,
  Ast_GoalTransform,
};

enum TermKind {
  Term_Hole = 1,

  Term_Primitive,
  Term_Union,
  Term_Constructor,
  Term_Function,
  Term_Fork,
  Term_Variable,
  Term_Computation,
  Term_Accessor,
  Term_Composite,
  Term_Arrow,
  Term_Rewrite,

  Term_Pointer,
};

const u32 AstFlag_Generated = 1 << 0;

embed_struct struct Ast {
  AstKind kind;
  Token token;
  u32   flags;
};

inline Ast **
toAsts(Term **values)
{
  return (Ast **) values;
}

inline void
initAst(Ast *in, AstKind cat, Token *token)
{
  in->kind   = cat;
  in->token = *token;
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
#define castTerm(exp, Cat) ((exp)->kind == Term_##Cat ? (Cat*)(exp) : 0)

struct Identifier : Ast {
  // NOTE: Since the ast has a token, which already has the identifier in it, we
  // don't need to put it in the identifier struct.
};

typedef Ast Hole;
typedef Ast Ellipsis;
typedef Ast AlgebraicManipulation;

struct NormalizeMeAst : Ast {
  String name_to_unfold;
};

struct ForkAst : Ast {
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

struct UnifyContext {
  Term         **values;
  Arrow         *signature;
  i32            depth;
  UnifyContext  *outer;
};

struct Scope {
  Scope  *outer;
  i32     depth;
  i32     param_count;
  Term  **values;
};

const u32 ExpectError_Ambiguous = 1 << 0;
const u32 ExpectError_WrongType = 1 << 1;

struct Typer
{
  LocalBindings *bindings;
  Scope         *scope;
  b32            try_reductio;
  u32            expected_errors;  // ExpectError
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

struct Term {
  TermKind  kind;
  i32           serial;
  Term         *type;
  Token        *global_name;
};

struct Primitive : Term {};

struct Constructor : Term {
  String name;  // :atomic-constructors-dont-have-global-names
  i32    index;
};

struct Union : Term {
  i32           ctor_count;
  Constructor **constructors;
};

struct Function : Term {
  Term *body;
  u32   function_flags;
};

struct Let : Ast {
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

struct Variable : Term {
  String name;
  i32    delta;
  i32    index;
};

struct TreePath {
  i32       head;  // -1 for op (TODO: change to u8 so we can hack this on the stack)
  TreePath *tail;
};

struct Accessor : Term {
  Term   *record;
  i32     index;
  String  debug_field_name;
};

struct Pointer;

struct StackPointer {
  String name;
  i32    depth;
  i32    index;
};

struct HeapPointer {
  Pointer *record;
  i32      index;
  String   debug_field_name;
};

struct Pointer : Term {
  Record *ref;
  b32     is_stack_pointer;
  union {
    StackPointer stack;
    HeapPointer  heap;
  };
};

struct CompositeAst : Ast {
  Ast  *op;
  i32   arg_count;
  Ast **args;
};

struct Composite : Term {
  union {
    struct {
      Term  *op;
      i32    arg_count;
      Term **args;
    };
    struct {
      Constructor  *ctor;
      i32           member_count;
      Term        **members;
    };
  };
};

u32 ParameterFlag_Inferred = 1 << 0;
u32 ParameterFlag_Unused   = 1 << 1;
u32 ParameterFlag_Poly     = 1 << 2;

struct ArrowAst : Ast {
  i32     param_count;
  String *param_names;
  Ast   **param_types;
  u32    *param_flags;
  Ast    *output_type;
};

struct Arrow : Term {
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
  Term *value;
  operator bool()   { return value; }
  operator Term*() { return value; }
};

struct RewriteAst : Ast {
  Ast *eq_proof;
  Ast *new_goal;
  Ast *body;
  b32  right_to_left;
  Ast *in_expression;
};

struct GoalTransform : Ast {
  Ast *hint;
  Ast *new_goal;
  Ast *body;
  b32  print_proof;
};

struct AccessorAst
{
  Ast    a;

  Ast   *record;
  Token  field_name;           // parsing info
};

struct FileList {
  char     *head_path;
  char     *head_content;
  FileList *tail;
};

// todo better hint lookup
struct HintDatabase {
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

struct TermArray {
  i32    count;
  Term **items;
};

struct AstArray {
  i32   count;
  Term *items;
};

// NOTE: Rewrite is done on the type of the whole expression, resulting in the type of the body.
struct Rewrite : Term {
  TreePath *path;
  b32       right_to_left;
  Term     *eq_proof;
  Term     *body;
};

typedef Term Computation;

struct SearchOutput {b32 found; TreePath *path; operator bool() {return found;}};

struct CompareTerms {Trinary result; TreePath *diff_path;};

const u32 FunctionFlag_is_global_hint         = 1 << 0;
const u32 FunctionFlag_no_apply               = 1 << 1;
const u32 FunctionFlag_no_print_as_binop      = 1 << 2;
const u32 FunctionFlag_expand                 = 1 << 3;

struct FunctionAst : Ast {
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

struct Fork : Term {
  Term   *subject;
  i32     case_count;
  Term  **bodies;
};

struct SyntheticAst : Ast {
  Term *term;
};

struct UnionAst : Ast {
  i32        ctor_count;
  Token     *ctor_names;
  ArrowAst **ctor_signatures;
  ArrowAst  *signature;
};

struct OverloadAst : Ast {
  Token  function_name;
  Ast   *distinguisher;
};

struct CtorAst : Ast {
  i32  ctor_i;
};

struct SeekAst : Ast {
  Ast *proposition;
};

struct ReductioAst : Ast {};

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
  Arena           *top_level_arena;
  FileList        *file_list;
  GlobalBindings  *bindings;
  HintDatabase    *hints;
  AlgebraDatabase *algebras;
  b32              top_level_debug_mode;
};

struct TreePathList {
  TreePath     *head;
  TreePathList *tail;
};

struct LookupPolyParameter {
  b32 found;
  i32 index;
  operator bool() { return found; }
};

struct TypedExpression : Ast {
  Ast *type;
  Ast *expression;
};

#define DEFAULT_MAX_LIST_LENGTH 64

String number_to_string[] = {
  toString("0"), toString("1"), toString("2"), toString("3"),
  toString("4"), toString("5"), toString("6"), toString("7"),
  toString("8"), toString("9"), toString("10"), toString("11"),
  toString("12"), toString("13"), toString("14"), toString("15"),
};

#include "generated/engine_forward.h"

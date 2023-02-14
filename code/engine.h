#pragma once

#include "generated/engine_embed.h"
#include "platform.h"
#include "utils.h"
#include "memory.h"
#include "lexer.h"
#include "parser.h"

// NOTE: This should work like the function stack, we'll clean it after every top-level form.
global_variable Arena  temp_arena_;
global_variable Arena *temp_arena = &temp_arena_;
global_variable Arena *parse_arena = &temp_arena_;
global_variable StringBuffer  error_buffer_;
global_variable StringBuffer *error_buffer = &error_buffer_;

struct Function;
struct Union;
struct Arrow;
struct Composite;
// NOTE: I almost think records are different cases from composites, just a
// coincidence that they are represented the same way.
typedef Composite Record;
struct Constructor;
struct Term;
struct LocalBindings;
struct DataMap;

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

struct Pointer;

struct Scope {
  Scope    *outer;
  i32       depth;
  i32       param_count;
  Pointer **pointers;
  b32      *ignored;
};

const u32 Error_Ambiguous = 1 << 0;  // NOTE: Maybe a better name would be "missing type info".
const u32 Error_WrongType = 1 << 1;

struct Typer
{
  LocalBindings *bindings;
  Scope         *scope;
  b32            try_reductio;
  u32            expected_errors;  // ExpectError
};

struct TermList
{
  Term     *head;
  TermList *tail;
};

struct Term {
  TermKind  kind;
  i32       serial;
  Term     *type;
  Token    *global_name;
};

struct SyntheticAst : Ast {
  Term *term;
};

struct TermArray {
  i32    count;
  Term **items;
};

enum PrimitiveKind {
  Primitive_Unique = 0,         // f.ex =, Set, Type, etc. they have no data attached
  Primitive_U32    = 1,
  Primitive_Array  = 2,
};

struct Primitive : Term {
  PrimitiveKind prim_kind;
  union {
    u32       u32;
    TermArray array;
  };
};

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

const u32 FunctionFlag_is_global_hint    = 1 << 0;
const u32 FunctionFlag_no_apply          = 1 << 1;
const u32 FunctionFlag_no_print_as_binop = 1 << 2;
const u32 FunctionFlag_expand            = 1 << 3;
// const u32 FunctionFlag_is_builtin        = 1 << 4;  // moved to ast

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

struct SolveArgs {i32 arg_count; Term **args;};

#define MAX_SOLVE_DEPTH 3
struct Solver {
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

String number_to_string[] = {
  toString("0"), toString("1"), toString("2"), toString("3"),
  toString("4"), toString("5"), toString("6"), toString("7"),
  toString("8"), toString("9"), toString("10"), toString("11"),
  toString("12"), toString("13"), toString("14"), toString("15"),
};

struct AbstractContext {
  Arena *arena;
  i32    env_depth;
  i32    zero_depth;
};

struct EvalContext {
  Term **args;
  i32    arg_count;
  i32    offset;
  b32    substitute_only;
  operator EvalContext*() {return this;};
};

struct NormContext {
  i32    depth;
  String name_to_unfold;
};

struct Transformation {
  Term           *term;
  Term           *eq_proof;
  TreePath       *path;  // NOTE: path relative to the upper frame
  Transformation *up;
};

#include "generated/engine_forward.h"

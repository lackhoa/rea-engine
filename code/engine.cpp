/*
  General Todos: 
  - #speed string interning.
  - #tool something that cleans up when it goes out of scope
  - #speed evaluating functions by substituting the body is really bad in case of "let"
  - clean up the data tree containing constructors
  - we're printing terms every time we encounter an error, but the error might be recoverable so it's just wasted work. Either pass the intention down, or abandon the recoveriy route.
  - Get stretchy buffer in here
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"
#include "lexer.cpp"
#include "debug_config.h"

global_variable Function  *current_global_function       = 0;
global_variable Pointer  **current_global_function_args = 0;

Term  holev_ = {.kind = Term_Hole};
Term *holev = &holev_;

global_variable EngineState global_state;

struct BuiltinEntry {
  char  *name;
  Term **term;
};

struct ReaBuiltins {
  Term *Type;
  Term *equal;
  Term *False;
  Term *eqChain;
  Term *U32;
  Term *Array;
  Term *length;
  Term *slice;
  Term *swap;
  Term *toNat;
  Term *get;

  Term *List;
  Term *nil;
  Term *single;
  Term *cons;
  Term *fold;
  Term *concat;
  Term *Permute;
  Term *permuteNil;
  Term *permuteSkip;
  Term *permuteSwap;
  Term *permuteChain;
  Term *foldConcat;
  Term *foldPermute;
  Term *permuteSame;
  Term *permute;
  Term *permuteFirst;
  Term *permuteLast;
  Term *falseImpliesAll;
};
global_variable ReaBuiltins rea_builtins;
ReaBuiltins &rea = rea_builtins;  // global_variable, but adding it breaks the debugger
#include "generated/rea_builtin.cpp"

inline void
maybeDeref(Term **in0)
{
  // NOTE: so how is this different from "castRecord"? A fact is that we don't try
  // to infer constructor... maybe we should, I don't know atm.
  //
  // #dicey-pointer-handling
  if (Pointer *pointer = castTerm(*in0, Pointer))
  {
    if (pointer->ref)
    {
      *in0 = pointer->ref;
    }
  }
}

inline void
initTerm(Term *in, TermKind cat, Term *type)
{
  in->kind  = cat;
  in->type = type;
}

inline Term *
_newTerm(Arena *arena, TermKind cat, Term *type, size_t size)
{
  Term *out = (Term *)pushSize(arena, size, true);
  initTerm(out, cat, type);
  out->serial = DEBUG_SERIAL++;
  return out;
}

#define newTerm(arena, cat, type)              \
  ((cat *) _newTerm(arena, Term_##cat, type, sizeof(cat)))

inline Term *
_copyTerm(Arena *arena, void *src, size_t size)
{
  Term *out = (Term *)copySize(arena, src, size);
  out->serial = DEBUG_SERIAL++;
  return out;
}

#define copyTerm(arena, src) \
  (mytypeof(src)) _copyTerm(arena, (src), sizeof(*(src)))

inline Term *
getArg(Term *in0, i32 index)
{
  Composite *in = castTerm(in0, Composite);
  assert(index < in->arg_count);
  return in->args[index];
}

inline Union *
getUnionOrPolyUnion(Term *in0)
{
  if (Union *uni = castTerm(in0, Union))
  {
    return uni;
  }
  if (Composite *in = castTerm(in0, Composite))
  {
    return castTerm(in->op, Union);
  }
  return 0;
}

inline b32
isGlobalValue(Term *in0)
{
  // :atomic-constructors-dont-have-global-names
  return (b32)in0->global_name || in0->kind == Term_Constructor;
}

inline b32
isPolyUnion(Union *in)
{
  return getType(in)->kind == Term_Arrow;
}

inline void
attach(char *key, String value, Tokenizer *tk=global_tokenizer)
{
  InterpError *error = tk->error;
  assert(error->attachment_count < arrayCount(error->attachments));
  error->attachments[error->attachment_count++] = {key, value};
}

inline void
attach(char *key, i32 count, Term **terms, PrintOptions print_options={})
{
  StartString start = startString(error_buffer);
  for (i32 id=0; id < count; id++)
  {
    print(error_buffer, "\n");
    print(error_buffer, terms[id], print_options);
  }
  attach(key, endString(start));
}

inline void attach(char *key, Token *token, Tokenizer *tk=global_tokenizer)
{
  attach(key, token->string, tk);
}

inline void
attach(char *key, Ast *ast, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, ast);
  attach(key, endString(start), tk);
}

inline void
attach(char *key, Term *value, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, value);
  attach(key, endString(start), tk);
}

inline void
attach(char *key, i32 n, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, "%d", n);
  attach(key, endString(start), tk);
}

inline String
globalNameOf(Term *term)
{
  if (term->global_name)
    return term->global_name->string;
  else
    return {};
}

inline Term *
lookupStack(Typer *typer, i32 delta, i32 index)
{
  Scope *scope = typer->scope;
  for (i32 i=0; i < delta; i++)
  {
    scope=scope->outer;
  }
  assert(scope->depth == typer->scope->depth - delta);
  assert(index < scope->param_count);
  return scope->values[index];
}

inline Arrow *
getSignature(Term *op)
{
  return castTerm(op->type, Arrow);
}

inline Arrow *
getConstructorSignature(Union *uni, i32 ctor_index)
{
  assert(ctor_index < uni->ctor_count);
  return getSignature(uni->constructors[ctor_index]);
}

inline i32
getParameterCount(Term *in)
{
  Arrow *signature = castTerm(getType(in), Arrow);
  return signature->param_count;
}

#if REA_INTERNAL
inline void
assertEqual(Term *l, Term *r)
{
  if (!equal(l, r))
  {
    print_var_delta = true;
    DUMP("l: ", l, "\n");
    DUMP("r: ", r, "\n");
    invalidCodePath;
  }
}
#else
inline void assertEqual(Term *l, Term *r) {}
#endif

inline Term *
newArrow(Arena *arena,
         i32 param_count, String *param_names, Term **param_types, u32 *param_flags,
         Term *output_type)
{
  if (!param_flags)
  {
    param_flags = pushArray(arena, param_count, u32, true);
  }
  Arrow *out = newTerm(arena, Arrow, rea.Type);
  out->param_count = param_count;
  out->param_names = param_names;
  out->param_types = param_types;
  out->param_flags = param_flags;
  out->output_type = output_type;
  return out;
}

inline Term *
reaListType(Term *l)
{
  return getArg(l, 0);
}

inline b32
isEquality(Term *eq0)
{
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == rea.equal)
      return true;
  }
  return false;
}

inline TermPair
getEqualitySides(Term *eq0, b32 must_succeed=true)
{
  TermPair out = {};
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == rea.equal)
      out = TermPair{eq->args[1], eq->args[2]};
  }
  assert(!must_succeed || out)
  return out;
}

inline b32
isSequenced(Ast *ast)
{
  b32 out = false;
  switch (ast->kind)
  {
    case Ast_RewriteAst:
    case Ast_Let:
    case Ast_ForkAst:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

inline b32
isSequenced(Term *term)
{
  b32 out = false;
  switch (term->kind)
  {
    case Term_Rewrite:
    case Term_Fork:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

inline UnifyContext *
extendUnifyContext(Arrow *signature, UnifyContext *outer)
{
  // :two-ways-to-make-contexts
  UnifyContext *ctx = pushStruct(temp_arena, UnifyContext, true);
  ctx->values       = pushArray(temp_arena, signature->param_count, Term*, true);
  ctx->signature    = signature;
  ctx->depth        = outer->depth+1;
  ctx->outer        = outer;
  return ctx;
}

inline UnifyContext *
newUnifyContext(Arrow *signature, i32 depth)
{
  // :two-ways-to-make-contexts
  UnifyContext *ctx = pushStruct(temp_arena, UnifyContext, true);
  ctx->values       = pushArray(temp_arena, signature->param_count, Term*, true);
  ctx->signature    = signature;
  ctx->depth        = depth;
  ctx->outer        = 0;
  return ctx;
}

struct UnionAndArgs {
  Union *uni;
  Term **args;
  operator bool() {return uni;}
};
inline UnionAndArgs
castUnion(Term *in0)
{
  if (Union *in = castTerm(in0, Union))
  {
    return {.uni=in};
  }
  else if (Composite *in = castTerm(in0, Composite))
  {
    if (Union *uni = castTerm(in->op, Union))
    {
      return {.uni=uni, .args=in->args};
    }
  }
  return {};
}

inline i32
getPolyParamCount(Arrow *params)
{
  i32 param_count = 0;
  for (i32 param_i=0; param_i < params->param_count; param_i++)
  {
    if (checkFlag(params->param_flags[param_i], ParameterFlag_Poly))
    {
      param_count++;
    }
    else
      break;
  }
  return param_count;
}

inline i32
getPolyParamCount(ArrowAst *params)
{
  i32 param_count = 0;
  for (i32 param_i=0; param_i < params->param_count; param_i++)
  {
    if (checkFlag(params->param_flags[param_i], ParameterFlag_Poly))
    {
      param_count++;
    }
    else
      break;
  }
  return param_count;
}

inline String
getConstructorName(Union *uni, i32 ctor_index)
{
  assert(ctor_index < uni->ctor_count);
  return uni->constructors[ctor_index]->name;
}

inline i32 getScopeDepth(Scope *scope) {return scope ? scope->depth : 0;}
inline i32 getScopeDepth(Typer *env)   {return (env && env->scope) ? env->scope->depth : 0;}

internal Term *
rewriteTerm(Arena *arena, Term *from, Term *to, TreePath *path, Term *in0)
{
  Term *out0 = 0;
  maybeDeref(&in0);
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyTerm(arena, in);
    if (path->head == -1)
    {
      out->op = rewriteTerm(arena, from, to, path->tail, in->op);
    }
    else
    {
      assert((path->head >= 0) && (path->head < out->arg_count));
      allocateArray(arena, out->arg_count, out->args);
      for (i32 arg_i=0; arg_i < out->arg_count; arg_i++)
      {
        if (arg_i == (i32)path->head)
          out->args[arg_i] = rewriteTerm(arena, from, to, path->tail, in->args[arg_i]);
        else
          out->args[arg_i] = in->args[arg_i];
      }
    }
    out0 = out;
  }
  else
  {
    if (!equal(in0, from))
    {
      DUMP("\nin0: ", in0, "\n", "from: ", from, "\n");
      invalidCodePath;
    }
    out0 = to;
  }
  return out0;
}

forward_declare inline Term *
getType(Term *in0)
{
  return in0->type;
}

inline LocalBindings *
extendBindings(Typer *env)
{
  LocalBindings *out = pushStruct(temp_arena, LocalBindings, true);
  out->tail     = env->bindings;
  out->arena    = temp_arena;
  env->bindings = out;
  return out;
}

forward_declare inline void
dump(Trinary trinary)
{
  if (trinary == Trinary_True) dump("True");
  else if (trinary == Trinary_False) dump("False");
  else dump("Unknown");
}

forward_declare inline void unwindScope(Typer *env) {env->scope = env->scope->outer;}

forward_declare inline void
unwindBindingsAndScope(Typer *env)
{
  env->bindings = env->bindings->tail;
  unwindScope(env);
}

forward_declare inline void dump(Term *in0) {print(0, in0, {});}
forward_declare inline void dump(Ast *in0)  {print(0, in0, {});}

i32 global_variable DEBUG_INDENTATION;
forward_declare inline void DEBUG_INDENT()
{
  DEBUG_INDENTATION++;
  for (i32 id = 0; id < DEBUG_INDENTATION; id++)
    dump(" ");
}

forward_declare inline void DEBUG_DEDENT()
{
  for (i32 id = 0; id < DEBUG_INDENTATION; id++)
    dump(" ");
  DEBUG_INDENTATION--;
}

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

inline b32
isInferredParameter(ArrowAst *arrow, i32 param_i)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_i], ParameterFlag_Inferred);
  return false;
}

inline b32
isInferredParameter(Arrow *arrow, i32 param_i)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_i], ParameterFlag_Inferred);
  return false;
}

inline i32
precedenceOf(String op)
{
  int out = 0;
  const i32 eq_precedence = 50;

  // TODO: implement for real
  if (equal(op, "->"))
  {
    out = eq_precedence - 20;
  }
  else if (equal(op, "/\\"))
  {
    out = eq_precedence - 10;
  }
  else if (equal(op, "=") || equal(op, "!="))
  {
    out = eq_precedence;
  }
  else if (equal(op, "<") || equal(op, ">") || equal(op, "=?") || equal(op, "=="))
  {
    out = eq_precedence + 5;
  }
  else if (equal(op, "+") || equal(op, "-"))
  {
    out = eq_precedence + 10;
  }
  else if (equal(op, "|"))
  {
    out = eq_precedence + 15;
  }
  else if (equal(op, "&") || equal(op, "*"))
  {
    out = eq_precedence + 20;
  }
  else
  {
    out = eq_precedence + 2;
  }

  return out;
}

inline Term *
reaHead(Term *in)
{
  return getArg(in, 1);
}

inline Term *
reaTail(Term *in)
{
  return getArg(in, 2);
}

inline char *
printComposite(Arena *buffer, Composite *in, PrintOptions opt)
{
  char *out = buffer ? (char *)getNext(buffer) : 0;
  int    precedence = 0;        // todo: no idea what the default should be
  Term  *op         = in->op;
  i32    arg_count  = 0;

  Arrow *op_signature = 0;
  b32 print_as_list     = false;
  b32 no_print_as_binop = false;
  op_signature = 0;
  arg_count    = in->arg_count;
  Term *type0 = getType(in);

  Constructor *ctor = castTerm(in->op, Constructor);

  if (Composite *type = castTerm(type0, Composite))
  {
    if (type->op == rea.List && ctor)
    {
      print_as_list = true;
    }
  }

  if (Function *fun = castTerm(in->op, Function))
  {
    no_print_as_binop = checkFlag(fun->function_flags, FunctionFlag_no_print_as_binop);
  }

  op_signature = castTerm(getType(in->op), Arrow);

  String op_name = {};
  if (Token *global_name = in->op->global_name)
  {
    op_name = global_name->string;
  }
  else if (Variable *var = castTerm(in->op, Variable))
  {
    op_name = var->name;
  }
  precedence = precedenceOf(op_name);

  Term **printed_args = in->args;
  i32 printed_arg_count = arg_count;
  if (op_signature)
  {// print out explicit args only
    if (!print_all_args)
    {
      printed_args = pushArray(temp_arena, op_signature->param_count, Term*);
      printed_arg_count = 0;
      for (i32 param_i = 0; param_i < op_signature->param_count; param_i++)
      {
        if (!isInferredParameter(op_signature, param_i))
        {
          printed_args[printed_arg_count++] = in->args[param_i];
        }
      }
    }
  }

  if (print_as_list)
  {// list path
    print(buffer, "[");
    if (ctor != rea.nil)
    {
      for (Record *iter = in; iter; )
      {
        print(buffer, reaHead(iter));
        Term *tail0 = reaTail(iter);
        iter = 0;
        if (Record *tail = castRecord(tail0))
        {
          if (tail->ctor != rea.nil)
          {
            iter = tail;
            print(buffer, ", ");
          }
        }
        else
        {
          print(buffer, " .. ");
          print(buffer, tail0);
        }
      }
    }
    print(buffer, "]");
  }
  else if (printed_arg_count == 2 && !no_print_as_binop)
  {// special path for infix binary operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    // #hack to force printing parentheses when the precedence is the same (a+b)+c.
    arg_opt.no_paren_precedence = precedence+1;
    print(buffer, printed_args[0], arg_opt);

    print(buffer, " ");
    print(buffer, op, opt);
    print(buffer, " ");

    arg_opt.no_paren_precedence = precedence;
    print(buffer, printed_args[1], arg_opt);
    if (precedence < opt.no_paren_precedence)
      print(buffer, ")");
  }
  else
  {// normal prefix path
    print(buffer, op, opt);
    if (!(ctor && printed_arg_count == 0))
    {
      print(buffer, "(");
      PrintOptions arg_opt        = opt;
      arg_opt.no_paren_precedence = 0;
      for (i32 arg_i = 0; arg_i < printed_arg_count; arg_i++)
      {
        print(buffer, printed_args[arg_i], arg_opt);
        if (arg_i < printed_arg_count-1)
          print(buffer, ", ");
      }
      print(buffer, ")");
    }
  }
  return out;
}

inline char *
printComposite(Arena *buffer, CompositeAst *in, PrintOptions opt)
{
  char *out = buffer ? (char *)getNext(buffer) : 0;
  int    precedence = 0;        // todo: no idea what the default should be
  Ast   *op         = 0;
  i32    arg_count  = 0;

  Arrow *op_signature = 0;
  Constructor *op_ctor = 0;
  b32 no_print_as_binop = false;
  op       = in->op;
  arg_count = in->arg_count;

  precedence = precedenceOf(in->op->token.string);

  Ast **printed_args = in->args;
  i32 printed_arg_count = arg_count;
  if (op_signature)
  {// print out explicit args only
    if (!print_all_args)
    {
      printed_args = pushArray(temp_arena, op_signature->param_count, Ast *);
      printed_arg_count = 0;
      for (i32 param_i = 0; param_i < op_signature->param_count; param_i++)
      {
        if (!isInferredParameter(op_signature, param_i))
        {
          printed_args[printed_arg_count++] = in->args[param_i];
        }
      }
    }
  }

  if (printed_arg_count == 2 && !no_print_as_binop)
  {// special path for infix binary operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    // #hack to force printing parentheses when the precedence is the same (a+b)+c.
    arg_opt.no_paren_precedence = precedence+1;
    print(buffer, printed_args[0], arg_opt);

    print(buffer, " ");
    print(buffer, op, opt);
    print(buffer, " ");

    arg_opt.no_paren_precedence = precedence;
    print(buffer, printed_args[1], arg_opt);
    if (precedence < opt.no_paren_precedence)
      print(buffer, ")");
  }
  else
  {// normal prefix path
    print(buffer, op, opt);
    if (!(op_ctor && printed_arg_count == 0))
    {
      print(buffer, "(");
      PrintOptions arg_opt        = opt;
      arg_opt.no_paren_precedence = 0;
      for (i32 arg_i = 0; arg_i < printed_arg_count; arg_i++)
      {
        print(buffer, printed_args[arg_i], arg_opt);
        if (arg_i < printed_arg_count-1)
          print(buffer, ", ");
      }
      print(buffer, ")");
    }
  }
  return out;
}

inline void
print(Arena *buffer, TreePath *tree_path)
{
  print(buffer, "[");
  for (TreePath *path=tree_path; path; path=path->tail)
  {
    print(buffer, "%d", path->head);
    if (path->tail)
    {
      print(buffer, ", ");
    }
  }
  print(buffer, "]");
}

inline void
dump(TreePath *tree_path)
{
  print(0, tree_path);
}

inline void indent(Arena *buffer, i32 indentation)
{
  for (int id=0; id < indentation; id++)
    print(buffer, " ");
}

inline void newlineAndIndent(Arena *buffer, i32 indentation)
{
  print(buffer, "\n");
  indent(buffer, indentation);
}

forward_declare internal void
print(Arena *buffer, Ast *in0, PrintOptions opt)
{// printAst
  if (in0)
  {
    PrintOptions new_opt = opt;
    unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    new_opt.indentation += 1;

    switch (in0->kind)
    {
      case Ast_Hole:
      {print(buffer, "_");} break;

      case Ast_SyntheticAst:
      {
        SyntheticAst *in = castAst(in0, SyntheticAst);
        print(buffer, in->term);
      } break;

      case Ast_Identifier:
      {print(buffer, in0->token.string);} break;

      case Ast_RewriteAst:
      {
        RewriteAst *in = castAst(in0, RewriteAst);
        print(buffer, "rewrite");
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof, new_opt);
      } break;

      case Ast_CompositeAst:
      {
        auto *in = castAst(in0, CompositeAst);
        printComposite(buffer, in, new_opt);
      } break;

      case Ast_ForkAst:
      {
        ForkAst *in = castAst(in0, ForkAst);
        print(buffer, "fork ");
        print(buffer, in->subject, new_opt);
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, "{");
        i32 case_count = in->case_count;
        for (i32 ctor_id = 0;
             ctor_id < case_count;
             ctor_id++)
        {
          Token *ctor = in->ctors + ctor_id;
          print(buffer, ctor->string);
          print(buffer, ": ");
          print(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != case_count)
          {
            print(buffer, ", ");
            newlineAndIndent(buffer, opt.indentation+1);
          }
        }
        print(buffer, "}");
      } break;

      case Ast_ArrowAst:
      {
        ArrowAst *in = castAst(in0, ArrowAst);
        print(buffer, "(");
        for (int param_i = 0;
             param_i < in->param_count;
             param_i++)
        {
          print(buffer, in->param_names[param_i]);
          print(buffer, ": ");
          print(buffer, in->param_types[param_i], new_opt);
          if (param_i < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ") -> ");

        print(buffer, in->output_type, new_opt);
      } break;

      case Ast_AccessorAst:
      {
        AccessorAst *in = castAst(in0, AccessorAst);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name.string);
      } break;

      case Ast_FunctionDecl: {print(buffer, "function decl");} break;

      case Ast_FunctionAst: {print(buffer, "lambda");} break;

      case Ast_Let:
      {
        Let *in = castAst(in0, Let);
        print(buffer, in->lhs);
        if (in->type)
        {
          print(buffer, " : ");
          print(buffer, in->type, new_opt);
        }
        print(buffer, " := ");
        print(buffer, in->rhs, new_opt);
        print(buffer, "; ");
        print(buffer, in->body, new_opt);
      } break;

      case Ast_UnionAst:
      {
        print(buffer, "<some union>");
      } break;

      case Ast_CtorAst:
      {
        print(buffer, "<some ctor>");
      } break;

      case Ast_SeekAst:
      {
        print(buffer, "<some seek>");
      } break;
    }
  }
  else
    print(buffer, "<NULL>");
}

forward_declare internal void
print(Arena *buffer, Ast *in0)
{
  return print(buffer, in0, {});
}

internal void
printTermsInParentheses(Arena *buffer, i32 count, Term **terms, PrintOptions opt={})
{
  print(buffer, "(");
  for (i32 i=0; i < count; i++)
  {
    print(buffer, terms[i]);
    if (i != count-1)
      print(buffer, ", ");
  }
  print(buffer, ")");
}

inline void
printStackPointerName(Arena *buffer, StackPointer *in, PrintOptions opt)
{
  bool has_name = in->name.chars;
  if (has_name)
    print(buffer, in->name);
  else
    print(buffer, "anon");

  if (!has_name || print_var_delta || print_var_index)
  {
    print(buffer, "<");
    if (!has_name || print_var_delta)
    {
      print(buffer, "%d", in->depth);
    }
    if (!has_name || print_var_index)
    {
      print(buffer, ",%d", in->index);
    }
    print(buffer, ">");
  }
}

forward_declare internal void
print(Arena *buffer, Term *in0, PrintOptions opt)
{// mark: printTerm
  if (in0)
  {
    b32 skip_print_type = false;
    PrintOptions new_opt = opt;
    if (in0->global_name &&
        !checkFlag(opt.flags, PrintFlag_Detailed))
    {
      print(buffer, in0->global_name->string);
    }
    else
    {
      if (!checkFlag(opt.flags, PrintFlag_LockDetailed))
      {
        unsetFlag(&new_opt.flags, PrintFlag_Detailed);
      }
      if (new_opt.print_type_depth)
      {
        new_opt.print_type_depth--;
      }
      new_opt.indentation = opt.indentation + 1;

      switch (in0->kind)
      {
        case Term_Variable:
        {
          Variable *in = castTerm(in0, Variable);
          bool has_name = in->name.chars;
          if (has_name)
            print(buffer, in->name);
          else
            print(buffer, "anon");

          if (!has_name || print_var_delta || print_var_index)
          {
            print(buffer, "[");
            if (!has_name || print_var_delta)
            {
              print(buffer, "%d", in->delta);
            }
            if (!has_name || print_var_index)
            {
              print(buffer, ",%d", in->index);
            }
            print(buffer, "]");
          }
        } break;

        case Term_Accessor:
        {
          Accessor *in = castTerm(in0, Accessor);
          print(buffer, in->record, new_opt);
          print(buffer, ".");
          print(buffer, in->debug_field_name);
        } break;

        case Term_Pointer:
        {
          Pointer *in = (Pointer *)(in0);
          if (in->is_stack_pointer)
          {
            if (in->ref)
            {
              print(buffer, in->ref);
            }
            else
            {
              printStackPointerName(buffer, &in->stack, opt);
            }
          }
          else
          {
            if (in->ref)
            {
              print(buffer, in->ref, opt);
            }
            else
            {
              const i32 max_path_length = 32;
              String rev_field_names[max_path_length];
              i32 path_length = 0;
              Pointer *iter = in;
              for (b32 stop = false; !stop;)
              {
                if (iter->is_stack_pointer)
                {
                  printStackPointerName(buffer, &iter->stack, opt);
                  stop = true;
                }
                else
                {
                  HeapPointer *heap = &iter->heap;
                  rev_field_names[path_length++] = heap->debug_field_name;
                  assert(path_length < max_path_length);
                  iter = heap->record;
                }
              }

              for (i32 path_i = path_length-1; path_i >= 0; path_i--)
              {
                print(buffer, ".");
                print(buffer, rev_field_names[path_i]);
              }
            }
          }
        } break;

        case Term_Hole:
        {print(buffer, "_");} break;

        case Term_Composite:
        {
          auto in = (Composite *)(in0);
          printComposite(buffer, in, new_opt);
        } break;

        case Term_Union:
        {
          auto in = (Union *)(in0);
          print(buffer, "union {");
          newlineAndIndent(buffer, opt.indentation+1);
          if (in->ctor_count)
          {
            unsetFlag(&new_opt.flags, PrintFlag_Detailed);
            for (i32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              print(buffer, getConstructorSignature(in, ctor_id), new_opt);
              if (ctor_id != in->ctor_count-1)
              {
                print(buffer, ",");
                newlineAndIndent(buffer, opt.indentation+1);
              }
            }
          }
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "}");
        } break;

        case Term_Function:
        {
          Function *in = castTerm(in0, Function);
          print(buffer, "fn");
          if (in->type)
          {
            print(buffer, in->type, new_opt);
            skip_print_type = true;
          }
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          print(buffer, in->body, new_opt);
          print(buffer, "}");
        } break;

        case Term_Arrow:
        {
          Arrow *in = castTerm(in0, Arrow);
          print(buffer, "(");
          for (int param_i = 0;
               param_i < in->param_count;
               param_i++)
          {
            String param_name = in->param_names[param_i];
            if (param_name.chars)
            {
              print(buffer, param_name);
              print(buffer, ": ");
            }
            print(buffer, in->param_types[param_i], new_opt);
            if (param_i < in->param_count-1)
              print(buffer, ", ");
          }
          print(buffer, ")");
          if (in->output_type)
          {
            print(buffer, " -> ");
            print(buffer, in->output_type, new_opt);
          }
        } break;

        case Term_Primitive:
        {
          Primitive *in = (Primitive*)in0;
          switch (in->prim_kind)
          {
            case Primitive_Unique:
            {
              assert(in->global_name);
              print(buffer, in->global_name->string);
            } break;

            case Primitive_U32:
            {
              print(buffer, "%d", in->u32);
            } break;

            case Primitive_Array:
            {
              todoIncomplete;
            } break;

            invalidDefaultCase;
          }
        } break;

        case Term_Constructor:
        {
          auto in = (Constructor *)in0;
          print(buffer, in->name);
          if (!in->type) skip_print_type = true;
        } break;

        case Term_Rewrite:
        {
          Rewrite *rewrite = castTerm(in0, Rewrite);
          print(buffer, getType(rewrite), new_opt);
          skip_print_type = true;
          print(buffer, " <=>");
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, getType(rewrite->body), new_opt);
          newlineAndIndent(buffer, opt.indentation);

          print(buffer, "rewrite");
          if (rewrite->right_to_left) print(buffer, "<-");
          print(buffer, rewrite->path);
          if (rewrite->eq_proof->kind != Term_Computation)
          {
            print(buffer, " justification: ");
            newlineAndIndent(buffer, new_opt.indentation);
            print(buffer, rewrite->eq_proof, new_opt);
          }
          newlineAndIndent(buffer, opt.indentation);

          print(buffer, "body: ");
          // print(buffer, getTypeNoEnv(temp_arena, rewrite->body), new_opt);
          newlineAndIndent(buffer, new_opt.indentation);
          print(buffer, rewrite->body, new_opt);
        } break;

        case Term_Computation:
        {
          print(buffer, "computation: ");
          print(buffer, getType(in0), new_opt);
          skip_print_type = true;
        } break;

        case Term_Fork:
        {
          Fork *in = castTerm(in0, Fork);
          print(buffer, "fork ");
          print(buffer, in->subject, new_opt);
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          Union *uni = getUnionOrPolyUnion(getType(in->subject));
          for (i32 ctor_id = 0;
               ctor_id < uni->ctor_count;
               ctor_id++)
          {
            print(buffer, getConstructorName(uni, ctor_id));
            print(buffer, ": ");
            print(buffer, in->bodies[ctor_id], new_opt);
            if (ctor_id != uni->ctor_count-1)
            {
              print(buffer, ", ");
              newlineAndIndent(buffer, opt.indentation+1);
            }
          }
          print(buffer, "}");
        } break;

        default:
        {
          todoIncomplete;
        } break;
      }
    }

    if (opt.print_type_depth && !skip_print_type)
    {
      print(buffer, ": ");
      new_opt.print_type_depth = 0;
      print(buffer, getType(in0), new_opt);
    }
  }
  else
    print(buffer, "<NULL>");
}

inline i32
getExplicitParamCount(ArrowAst *in)
{
  i32 out = 0;
  for (i32 param_i = 0; param_i < in->param_count; param_i++)
  {
    if (!isInferredParameter(in, param_i))
      out++;
  }
  return out;
}

inline i32
getExplicitParamCount(Arrow *in)
{
  i32 out = 0;
  for (i32 param_i = 0; param_i < in->param_count; param_i++)
  {
    if (!isInferredParameter(in, param_i))
      out++;
  }
  return out;
}

#if 0
inline b32
shouldHideTerm(Term *in0)
{
  if (in0 == rea.Type) return true;
  if (in0->kind == Term_Union) return true;
  if (Composite *in = castTerm(in0, Composite))
  {
    Arrow *signature = getSignature(in->op);
    if (getExplicitParamCount(signature) == 0)
    {
    }
  }
  return false;
}
#endif

inline void
prettyPrint(Arena *buffer, Scope *scope)
{
  // NOTE: Skip the last scope since we already know
  while (scope)
  {
    Pointer **values = scope->values;
    for (int param_i = 0;
         param_i < scope->param_count;
         param_i++)
    {
      Pointer *pointer = values[param_i];
      if (pointer)  // sometimes we error out, and the scope is hosed
      {
        assert(pointer->is_stack_pointer);
        if (Record *record = castRecord(pointer))
        {
          Arrow *signature = getSignature(record->ctor);
          for (i32 i=0; i < record->member_count; i++)
          {
            // NOTE: print the member types.
            if (!isInferredParameter(signature, i))
            {
              Term *member = record->members[i];
              print(buffer, member, printOptionPrintType());
              if (i != record->member_count-1) print(buffer, "\n");
            }
          }
        }
        else
        {
          if (pointer->stack.name.chars)
          {
            print(buffer, pointer->stack.name);
            print(buffer, ": ");
          }
          print(buffer, pointer->type);
        }
        print(buffer, "\n");
      }
    }
    scope = scope->outer;
  }
}

forward_declare internal void
print(Arena *buffer, Term *in0)
{
  return print(buffer, in0, {});
}

inline Scope *
newScope(Scope *outer, i32 param_count, Pointer **values)
{
  Scope *scope = pushStruct(temp_arena, Scope, true);
  scope->outer       = outer;
  scope->depth       = outer ? outer->depth+1 : 1;
  scope->values      = values;
  scope->param_count = param_count;
  return scope;
}

inline Scope *
newScope(Scope *outer, i32 param_count)
{
  Pointer **values = pushArray(temp_arena, param_count, Pointer *, true);
  return newScope(outer, param_count, values);
}

struct EvalContext {
  Term **args;
  i32    arg_count;
  i32    offset;
  b32    substitute_only;
  operator EvalContext*() {return this;};
};

internal Term *
evaluate_(EvalContext *ctx, Term *in0)
{
  Term *out0 = 0;
  i32 unused_var serial = DEBUG_SERIAL++;
  Arena *arena = temp_arena;
  b32 substitute_only = ctx->offset || ctx->substitute_only;
  if (isGlobalValue(in0))
  {
    out0 = in0;
  }
  else
  {
    switch (in0->kind)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        i32 delta = in->delta - ctx->offset;
        if (delta >= 0)
        {
          assert(in->index < ctx->arg_count);
          out0 = ctx->args[in->index];
        }
        else
        {
          // copy so we can evaluate the type.
          Variable *out = copyTerm(arena, in);
          out->type = evaluate_(ctx, in0->type);
          out0 = out;
        }
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);

        Term *op = evaluate_(ctx, in->op);
        Term **args = pushArray(arena, in->arg_count, Term*);
        for (i32 i=0; i < in->arg_count; i++)
        {
          args[i] = evaluate_(ctx, in->args[i]);
          assert(args[i]);
        }

        if (!substitute_only)
        {
          out0 = apply(op, in->arg_count, args, {});
        }

        if (!out0)
        {
          Composite *out = copyTerm(arena, in);
          out->type = evaluate_(ctx, in0->type);
          out->op   = op;
          out->args = args;
          out0 = out;
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);
        allocateArray(arena, out->param_count, out->param_types);

        EvalContext new_ctx = *ctx;
        new_ctx.offset++;
        for (i32 i=0; i < out->param_count; i++)
        {
          out->param_types[i] = evaluate_(&new_ctx, in->param_types[i]);
        }
        out->output_type = evaluate_(&new_ctx, in->output_type);

        out0 = out;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Term *record0 = evaluate_(ctx, in->record);
        if (Record *record = castRecord(record0))
        {
          out0 = record->members[in->index];
        }
        else
        {
          assert(ctx->offset);
          castRecord(record0);
          Accessor *out = copyTerm(arena, in);
          out->type = evaluate_(ctx, in0->type);
          out->record = record0;
          out0 = out;
        }
      } break;

      case Term_Rewrite:
      {
        Rewrite *in  = castTerm(in0, Rewrite);
        Rewrite *out = copyTerm(arena, in);
        out->type = evaluate_(ctx, in0->type);
        out->eq_proof = evaluate_(ctx, in->eq_proof);
        out->body     = evaluate_(ctx, in->body);
        out0 = out;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyTerm(arena, in);
        out->type = evaluate_(ctx, in0->type);

        EvalContext new_ctx = *ctx;
        new_ctx.offset++;
        out->body = evaluate_(&new_ctx, in->body);
        assert(out->body);

        out0 = out;
      } break;

      case Term_Fork:
      {
        Fork *in = (Fork *)in0;
        Term *subject0 = evaluate_(ctx, in->subject);
        if (substitute_only)
        {
          Fork *out = copyTerm(arena, in);
          out->type = evaluate_(ctx, in0->type);
          out->subject = subject0;
          allocateArray(arena, in->case_count, out->bodies);
          for (i32 i=0; i < in->case_count; i++)
          {
            out->bodies[i] = evaluate_(ctx, in->bodies[i]);
          }
          out0 = out;
        }
        else
        {
          if (Record *subject = castRecord(subject0))
          {
            i32 ctor_index = subject->ctor->index;
            out0 = evaluate_(ctx, in->bodies[ctor_index]);
          }
        }
      } break;

      case Term_Computation:
      {
        Computation *in  = (Computation *)(in0);
        Computation *out = copyTerm(arena, in);
        out->type = evaluate_(ctx, in0->type);
        out0 = out;
      } break;

      case Term_Pointer:
      {
        out0 = in0;
      } break;

      case Term_Constructor:
      {
        invalidCodePath;
      } break;

      default:
        todoIncomplete;
    }
  }

  if (substitute_only) assert(out0);
  return out0;
}

inline Term *
toValue(Scope *scope, Term *in0)
{
  Term **args = (Term **)scope->values;  // NOTE: not gonna write to the scope, so casting is ok
  EvalContext ctx = {.arg_count = scope->param_count,
                     .args=args,
                     .substitute_only=true};
  return evaluate_(&ctx, in0);
}

inline Term *
substitute(Term *in0, i32 arg_count, Term **args)
{
  EvalContext ctx = {.arg_count=arg_count, .args=args, .substitute_only=true};
  return evaluate_(&ctx, in0);
}

inline Term *
evaluate(Term *in0, i32 arg_count, Term **args)
{
  EvalContext ctx = {.arg_count=arg_count, .args=args};
  return evaluate_(&ctx, in0);
}

forward_declare inline b32
equal(Term *lhs, Term *rhs)
{
  return equalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeConstructor(Term *in0)
{
  if (Composite *in = castTerm(in0, Composite))
    return in->op->kind == Term_Constructor;
  else
    return false;
}

inline b32
isGround(Term *in0)
{
  if (isGlobalValue(in0))
    return true;

  switch (in0->kind)
  {
    case Term_Composite:
    {
      Composite *composite = castTerm(in0, Composite);
      if (!isGround(composite->op))
        return false;

      for (int id=0; id < composite->arg_count; id++)
      {
        if (!isGround(composite->args[id]))
          return false;
      }

      return true;
    } break;

    // case Term_PolyConstructor:
    case Term_Primitive:
    {return true;} break;

    case Term_Hole:
    case Term_Variable:
    case Term_Arrow:
    case Term_Function:
    case Term_Fork:
    case Term_Accessor:
    case Term_Rewrite:
    case Term_Computation:
    case Term_Union:
    case Term_Constructor:
    {return false;} break;

    default:
      todoIncomplete;
  }
}

inline b32
isRootedFrom(Term *ap0, Pointer *a)
{
  assert(a->is_stack_pointer);
  if (Pointer *ap = castTerm(ap0, Pointer))
  {
    Pointer *root = ap;
    while (!root->is_stack_pointer)
    {
      root = root->heap.record;
    }
    return root == a;
  }
  return false;
}

inline b32
recursiveCallAccepted(i32 arg_count, Term **args)
{
  b32 rejected        = false;
  b32 component_found = false;
  for (i32 i=0; !rejected && i < arg_count; i++)
  {
    Term *arg = args[i];
    rejected = true;
    // for (i32 j=0; rejected && j < arg_count; j++)
    i32 j = i;
    {
      Pointer *global_arg = current_global_function_args[j];
      if (arg == global_arg)
      {
        rejected = false;
      }
      else if (isRootedFrom(arg, global_arg))
      {
        rejected        = false;
        component_found = true;
      }
    }
  }
  return !rejected && component_found;
}

inline void
checkRecursiveCall(Term *op, i32 arg_count, Term **args)
{
  if (Function *fun = castTerm(op, Function))
  {
    if (fun == current_global_function)
    {
      if (!recursiveCallAccepted(arg_count, args))
      {
        DUMP("RECURSION REJECTED!\n");

        DUMP("scope: ");
        for (i32 i=0; i < arg_count; i++)
        {
          DUMP(current_global_function_args[i], ", ");
        }
        DUMP("\n");

        DUMP("args : ");
        for (i32 i=0; i < arg_count; i++)
        {
          DUMP(args[i], ", ");
        }
        DUMP("\n");

        assert(false);
      }
    }
  }
}

inline Composite *
newComposite(Arena *arena, Term *op, i32 arg_count, Term **args)
{
  checkRecursiveCall(op, arg_count, args);

  Composite *out = 0;
  Arrow *signature = castTerm(getType(op), Arrow);
  assert(signature->param_count == arg_count);
  Term  *type      = substitute(signature->output_type, arg_count, args);

  for (i32 arg_i=0; arg_i < arg_count; arg_i++)
  {
    Term *actual_type   = args[arg_i]->type;
    Term *expected_type = substitute(signature->param_types[arg_i], arg_count, args);
    assertEqual(actual_type, expected_type);
  }

  out = newTerm(arena, Composite, type);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;

  return out;
}

inline Composite *
reaComposite_(Term *op, i32 param_count, ...)
{
  // assert(param_count == getParameterCount(op));
  Arena *arena = temp_arena;
  Term **args = pushArray(arena, param_count, Term*);

  va_list arg_list;
  __crt_va_start(arg_list, param_count);
  for (i32 i=0; i < param_count; i++)
  {
    args[i] = __crt_va_arg(arg_list, Term*);
  }
  __crt_va_end(arg_list);

  return newComposite(arena, op, param_count, args);
}

#define reaComposite(op, ...) reaComposite_(op, PP_NARG(__VA_ARGS__), __VA_ARGS__)

internal b32
instantiate(Term *in0, i32 ctor_i)
{
  b32 success = false;
  Arena *arena = temp_arena;
  if (Pointer *pointer = castTerm(in0, Pointer))
  {
    auto [uni, args] = castUnion(in0->type);
    if (!pointer->ref)
    {
      i32 poly_count = 0;
      if (Arrow *uni_params = castTerm(uni->type, Arrow))
      {
        poly_count = getPolyParamCount(uni_params);
      }

      Constructor *ctor = uni->constructors[ctor_i];
      Arrow *signature = getSignature(ctor);
      i32 member_count = signature->param_count;
      Term **members = pushArray(arena, member_count, Term *);
      for (i32 mem_i = 0; mem_i < poly_count; mem_i++)
      {
        members[mem_i] = args[mem_i];
      }
      for (i32 mem_i=poly_count; mem_i < member_count; mem_i++)
      {
        Term *member_type = signature->param_types[mem_i];
        member_type = substitute(member_type, member_count, members);
        Pointer *member          = newTerm(arena, Pointer, member_type);
        member->heap.record           = pointer;
        member->heap.index            = mem_i;
        member->heap.debug_field_name = signature->param_names[mem_i];
        members[mem_i] = member;
      }
      pointer->ref = newComposite(arena, ctor, member_count, members);
      success = true;
    }
  }
  return success;
}

inline void
uninstantiate(Term *in0)
{
  Pointer *pointer = castTerm(in0, Pointer);
  assert(pointer->ref);
  pointer->ref = 0;
}

forward_declare inline Record *
castRecord(Term *record0)
{
  Record *out = {};
  if (Composite *record = castTerm(record0, Composite))
  {
    if (Constructor *ctor = castTerm(record->op, Constructor))
    {
      out = record;
    }
  }
  else if (Pointer *pointer = castTerm(record0, Pointer))
  {
    if (!pointer->ref)
    {
      if (Union *uni = getUnionOrPolyUnion(pointer->type))
      {
        if (uni->ctor_count == 1)
        {
          // lazy instantiation
          instantiate(pointer, 0);
        }
      }
    }
    out = pointer->ref;
  }
  return out;
}

inline Term *
reaSingle(Term *head)
{
  return reaComposite(rea.single, getType(head), head);
}

inline Term *
reaCons(Term *head, Term *tail)
{
  return reaComposite(rea.cons, getType(head), head, tail);
}

inline Term *
reaConcat(Arena *arena, Term *a, Term *b)
{
  return reaComposite(rea.concat, reaListType(a), a, b);
}

inline Composite *
newEquality(Term *lhs, Term *rhs)
{
  return reaComposite(rea.equal, getType(lhs), lhs, rhs);
}

inline Term *
newIdentity(Term *term)
{
  Term *eq = newEquality(term, term);
  Computation *out = newTerm(temp_arena, Computation, eq);
  return out;
}

forward_declare internal Term *
apply(Term *op, i32 arg_count, Term **args, String name_to_unfold)
{
  Term *out0 = 0;

  if (DEBUG_LOG_apply)
  {
    i32 serial = DEBUG_SERIAL++;
    DEBUG_INDENT(); DUMP("apply(", serial, "): ", op, "(...)\n");
  }

  if (Function *fun = castTerm(op, Function))
  {// Function application
    b32 should_apply_function = true;
    if (fun == current_global_function)
    {
      should_apply_function = false;  // NOTE: not strictly needed
    }
    if (checkFlag(fun->function_flags, FunctionFlag_no_apply))
    {
      should_apply_function = (name_to_unfold.chars && equal(fun->global_name->string, name_to_unfold));
    }

    if (should_apply_function)
    {
      out0 = evaluate(fun->body, arg_count, args);
    }
  }
  else if (op == rea.equal)
  {// special case for equality
    Term *l0 = args[1];
    Term *r0 = args[2];

    b32 can_destruct = false;
    // todo #hack I'm just gonna put the "auto-destruct" here for testing since
    // we rely on that in our scripts, definitely will rethink that.
    if (Record *l = castRecord(l0))
    {
      if (Record *r = castRecord(r0))
      {
        if (l->ctor == r->ctor)
        {
          can_destruct = true;
          assert(l->arg_count == r->arg_count);
          if (l->arg_count == 1)
          {
            Composite *eq = newEquality(l->args[0], r->args[0]);
            out0 = apply(eq->op, eq->arg_count, eq->args, name_to_unfold);
            if (!out0) out0 = eq;
          }
        }
      }
    }

    if (!can_destruct)
    {
      Trinary compare = equalTrinary(l0, r0);
      // #hack to handle inconsistency
      if (compare == Trinary_False)
        out0 = rea.False;
    }
  }

  if(DEBUG_LOG_apply)
  {
    DEBUG_DEDENT(); DUMP("=> ", out0, "\n");
  }

  return out0;
}

// todo #cleanup "same_type" doesn't need to be passed down all the time.
internal CompareTerms
compareTerms(Arena *arena, Term *l0, Term *r0)
{
  CompareTerms out = {.result = Trinary_Unknown};

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_compare)
  {
    DEBUG_INDENT(); DUMP("comparing(", serial, "): ", l0, " and ", r0, "\n");
  }

  if (l0 == r0)
  {
    out.result = {Trinary_True};
  }
  else
  {
    maybeDeref(&l0);
    maybeDeref(&r0);

    if (l0->kind == r0->kind)
    {
      switch (l0->kind)
      {
        case Term_Variable:
        {
          Variable *lhs = castTerm(l0, Variable);
          Variable *rhs = castTerm(r0, Variable);
          if ((lhs->delta == rhs->delta) && (lhs->index == rhs->index))
            out.result = Trinary_True;
        } break;

        case Term_Arrow:
        {
          Arrow* lhs = castTerm(l0, Arrow);
          Arrow* rhs = castTerm(r0, Arrow);
          i32 param_count = lhs->param_count;
          if (rhs->param_count == param_count)
          {
            b32 type_mismatch = false;
            for (i32 id = 0; id < param_count; id++)
            {
              if (!equal(lhs->param_types[id], rhs->param_types[id]))
              {
                type_mismatch = true;
                break;
              }
            }
            if (!type_mismatch)
            {
              out.result = equalTrinary(lhs->output_type, rhs->output_type);
            }
          }
          else
            out.result = Trinary_False;
        } break;

        case Term_Composite:
        {
          Composite *l = castTerm(l0, Composite);
          Composite *r = castTerm(r0, Composite);

          b32 op_equal = equal(l->op, r->op);
          if (op_equal)
          {
            Arrow *arrow = getSignature(l->op);

            i32 count = l->arg_count;
            assert(l->arg_count == r->arg_count);

            i32 mismatch_count = 0;
            i32 false_count = 0;
            int       unique_diff_id   = 0;
            TreePath *unique_diff_path = 0;
            out.result = Trinary_True;
            for (i32 arg_i=0; arg_i < count; arg_i++)
            {
              // todo "ParameterFlag_Unused" is just a hack, it doesn't mean anything yet.
              if (!checkFlag(arrow->param_flags[arg_i], ParameterFlag_Unused))
              {
                CompareTerms recurse = compareTerms(arena, l->args[arg_i], r->args[arg_i]);
                if (recurse.result != Trinary_True)
                {
                  mismatch_count++;
                  if (mismatch_count == 1)
                  {
                    unique_diff_id   = arg_i;
                    unique_diff_path = recurse.diff_path;
                  }
                  if (recurse.result == Trinary_False)
                    false_count++;
                }
              }
            }
            if (mismatch_count > 0)
            {
              out.result = Trinary_Unknown;
              if ((l->op->kind == Term_Constructor) &&
                  (r->op->kind == Term_Constructor) &&
                  (false_count > 0))
              {
                out.result = Trinary_False;
              }
            }
            if ((out.result == Trinary_Unknown) && (mismatch_count == 1) && arena)
            {
              allocate(arena, out.diff_path);
              out.diff_path->head = unique_diff_id;
              out.diff_path->tail = unique_diff_path;
            }
          }
          else
          {
            // #constructor-disjointness
            if (l->op->kind == Term_Constructor &&
                r->op->kind == Term_Constructor)
            {
              out.result = Trinary_False;
            }
          }
        } break;

        case Term_Constructor:
        {
          // #constructor-disjointness
          out.result = Trinary_False;
        } break;

        case Term_Accessor:
        {
          Accessor *lhs = castTerm(l0, Accessor);
          Accessor *rhs = castTerm(r0, Accessor);
          if (lhs->index == rhs->index)
          {
            if (equal(lhs->record, rhs->record))
            {
              out.result = Trinary_True;
            }
          }
        } break;

        case Term_Primitive:
        {
          out.result = toTrinary(l0 == r0);
        } break;

        case Term_Union:
        case Term_Function:
        case Term_Hole:
        case Term_Rewrite:
        case Term_Computation:
        case Term_Fork:
        case Term_Pointer:
        {} break;

        default:
          todoIncomplete;
      }
    }
  }

  if (DEBUG_LOG_compare)
  {
    DEBUG_DEDENT(); DUMP("=>(", serial, ") ", out.result, "\n");
  }

  return out;
}

forward_declare internal Trinary
equalTrinary(Term *lhs0, Term *rhs0)
{
  return compareTerms(0, lhs0, rhs0).result;
}

internal GlobalBinding *
lookupGlobalNameSlot(String key, b32 add_new)
{
  // :global-bindings-zero-at-startup
  GlobalBinding *slot = 0;
  u32 hash = stringHash(key) % arrayCount(global_state.bindings->table);
  slot = global_state.bindings->table + hash;
  b32 first_slot_valid = slot->key.length == 0;
  if (first_slot_valid)
  {
    while (true)
    {
      if (equal(slot->key, key))
        break;
      else if (slot->hash_tail)
        slot = slot->hash_tail;
      else
      {
        if (add_new)
        {
          slot->hash_tail = pushStruct(global_state.top_level_arena, GlobalBinding, true);
          slot = slot->hash_tail;
          slot->key = key;
        }
        else
          slot = 0;
        break;
      }
    }
  }
  else if (add_new)
    slot->key = key;
  else
    slot = 0;

  if (slot && !add_new)
    assert(slot->count != 0);

  return slot;
}

internal GlobalBinding *
lookupGlobalNameSlot(Identifier *ident, b32 add_new)
{
  return lookupGlobalNameSlot(ident->token.string, add_new);
}

struct LookupCurrentFrame { LocalBinding* slot; b32 found; };

internal LookupCurrentFrame
lookupCurrentFrame(LocalBindings *bindings, String key, b32 add_if_missing)
{
  LocalBinding *slot = 0;
  b32 found = false;
  u32 hash = stringHash(key) % arrayCount(bindings->table);
  slot = bindings->table + hash;
  b32 first_slot_valid = slot->key.length;
  if (first_slot_valid)
  {
    b32 stop = false;
    while (!stop)
    {
      if (equal(slot->key, key))
      {
        stop = true;
        found = true;
      }
      else if (slot->tail)
        slot = slot->tail;
      else
      {
        stop = true;
        if (add_if_missing)
        {
          allocate(bindings->arena, slot->tail);
          slot = slot->tail;
          slot->key  = key;
          slot->tail = 0;
        }
      }
    }
  }
  else if (add_if_missing)
  {
    slot->key = key;
  }

  LookupCurrentFrame out = { slot, found };
  return out;
}

struct AbstractContext
{
  Arena *arena;
  i32    env_depth;
  i32    zero_depth;
};

// :persistent-global-function
inline Term *
toAbstractTerm_(AbstractContext *ctx, Term *in0)
{
  assert(ctx->zero_depth >= ctx->env_depth);
  Term *out0 = 0;
  Arena *arena = ctx->arena;

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_toAbstractTerm)
  {
    DEBUG_INDENT(); DUMP("abstract(", serial, "): ", in0, "\n");
  }

  if (isGlobalValue(in0))
  {
    out0 = in0;
  }
  else
  {
    switch (in0->kind)
    {
      case Term_Pointer:
      {
        Pointer *in = castTerm(in0, Pointer);
        if (in->is_stack_pointer)
        {
          if (in->stack.depth > ctx->env_depth)
          {
            Variable *out = newTerm(arena, Variable, 0);
            out->name  = in->stack.name;
            out->delta = ctx->zero_depth - in->stack.depth;
            out->index = in->stack.index;
            assert(out->delta >= 0);
            out0 = out;
          }
          else
          {
            out0 = in0;
          }
        }
        else
        {
          Term *record = toAbstractTerm_(ctx, in->heap.record);
          if (record != in->heap.record)
          {
            Accessor *out = newTerm(arena, Accessor, 0);
            out->record           = record;
            out->index            = in->heap.index;
            out->debug_field_name = in->heap.debug_field_name;
            out0 = out;
          }
          else
          {
            out0 = in0;
          }
        }
      } break;

      case Term_Composite:
      {
        Composite *in  = (Composite *)in0;
        Composite *out = copyTerm(arena, in);
        out->op = toAbstractTerm_(ctx, in->op);
        allocateArray(arena, in->arg_count, out->args);
        for (i32 i=0; i < in->arg_count; i++)
        {
          out->args[i] = toAbstractTerm_(ctx, in->args[i]);
        }
        out0 = out;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);
        ctx->zero_depth++;
        allocateArray(arena, in->param_count, out->param_types);
        for (i32 i=0; i < in->param_count; i++)
        {
          out->param_types[i] = toAbstractTerm_(ctx, in->param_types[i]);
        }
        out->output_type = toAbstractTerm_(ctx, in->output_type);
        ctx->zero_depth--;
        out0 = out;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in  = castTerm(in0, Rewrite);
        Rewrite *out = copyTerm(arena, in);
        out->eq_proof = toAbstractTerm_(ctx, in->eq_proof);
        out->body     = toAbstractTerm_(ctx, in->body);
        out0 = out;
      } break;

      case Term_Fork:
      {
        Fork *in  = castTerm(in0, Fork);
        Fork *out = copyTerm(arena, in);
        out->subject = toAbstractTerm_(ctx, in->subject);
        out->bodies  = pushArray(arena, in->case_count, Term*);
        for (i32 i=0; i < in->case_count; i++)
        {
          out->bodies[i] = toAbstractTerm_(ctx, in->bodies[i]);
        }
        out0 = out;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyTerm(arena, in);
        ctx->zero_depth++;
        out->body = toAbstractTerm_(ctx, in->body);
        ctx->zero_depth--;
        out0 = out;
      } break;

      case Term_Variable:
      {
        out0 = copyTerm(arena, (Variable *)in0);
      } break;

      case Term_Computation:
      {
        out0 = copyTerm(arena, (Computation *)in0);
      } break;

      case Term_Accessor:
      {
        Accessor *in = (Accessor *)in0;
        Accessor *out = copyTerm(arena, in);
        out->record = toAbstractTerm_(ctx, in->record);
        out0 = out;
      } break;

      case Term_Primitive:
      {
        Primitive *in = (Primitive *)in0;
        Primitive *out = copyTerm(arena, in);
        switch (in->prim_kind)
        {
          case Primitive_U32:
          {} break;

          case Primitive_Array:
          {todoIncomplete} break;

          invalidDefaultCase;
        }
        out0 = out;
      } break;

      default:
      {
        DUMP("term is: ", in0, "\n");
        todoIncomplete;
      }
    }
    if (out0 != in0)
    {
      out0->type = toAbstractTerm_(ctx, in0->type);
    }
  }
  assert(out0);

  if (DEBUG_LOG_toAbstractTerm)
  {
    DEBUG_DEDENT(); DUMP("=> ", out0, "\n");
  }

  return out0;
}

inline Term *
toAbstractTerm(Arena *arena, Term *value, b32 env_depth)
{
  AbstractContext ctx = {.arena=arena, .env_depth=env_depth, .zero_depth=env_depth+1};
  return toAbstractTerm_(&ctx, value);
}

inline Pointer *
newStackPointer(String name, i32 depth, i32 index, Term *type)
{
  assert(depth);
  Pointer *out = newTerm(temp_arena, Pointer, type);
  out->is_stack_pointer = true;
  out->stack.name       = name;
  out->stack.depth      = depth;
  out->stack.index      = index;
  return out;
}

struct NormalizeContext {
  i32    depth;
  String name_to_unfold;
};

internal Term *
normalize_(NormalizeContext *ctx, Term *in0) 
{
  Term *out0 = in0;
  Arena *arena = temp_arena;

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_normalize)
  {
    DEBUG_INDENT(); DUMP("normalize(", serial, "): ", in0, "\n");
  }

  if (!isGlobalValue(in0))
  {
    switch (in0->kind)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        b32 progressed = false;

        Term **norm_args = pushArray(arena, in->arg_count, Term*);
        for (auto arg_i = 0;
             arg_i < in->arg_count;
             arg_i++)
        {
          norm_args[arg_i] = normalize_(ctx, in->args[arg_i]);
          progressed = progressed || (norm_args[arg_i] != in->args[arg_i]);
        }

        Term *norm_op = normalize_(ctx, in->op);
        progressed = progressed || (norm_op != in->op);

        out0 = apply(norm_op, in->arg_count, norm_args, ctx->name_to_unfold);

        if (!out0)
        {
          Composite *out = copyTerm(arena, in);
          out->op   = norm_op;
          out->args = norm_args;
          out0 = out;
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);

        i32 param_count = in->param_count;
        Term *output_type = 0;
        Term **param_types = pushArray(arena, param_count, Term *);

        NormalizeContext new_ctx = *ctx;
        {
          NormalizeContext *ctx  = &new_ctx;
          ctx->depth++;
          for (i32 i=0; i < param_count; i++)
          {
            // NOTE: optimization to eval and normalize at the same time, which
            // would save us some allocation if the application succeeds.
            Term *param_type = evaluate(in->param_types[i], param_count, param_types);
            param_type = normalize_(ctx, param_type);
            param_types[i] = newStackPointer(in->param_names[i], ctx->depth, i, param_type);
          }
          output_type = evaluate(in->output_type, param_count, param_types);
          output_type = normalize_(ctx, output_type);
        }

        for (i32 i=0; i < param_count; i++)
        {
          param_types[i] = toAbstractTerm(arena, param_types[i]->type, ctx->depth);
        }
        out->param_types = param_types;
        out->output_type = toAbstractTerm(arena, output_type, ctx->depth);

        out0 = out;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        Term *body     = normalize_(ctx, in->body);
        Term *eq_proof = normalize_(ctx, in->eq_proof);
        if ((body != in->body) || (eq_proof != in->eq_proof))
        {
          Rewrite *out = copyTerm(arena, in);
          out->eq_proof = eq_proof;
          out->body     = body;
          out0 = out;
        }
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Term *record0 = normalize_(ctx, in->record);
        if (Record *record = castRecord(record0))
        {
          out0 = record->args[in->index];
        }
        else if (record0 != in->record)
        {
          Accessor *out = copyTerm(arena, in);
          out->record = record0;
          out0 = out;
        }
      } break;

      case Term_Variable:
      case Term_Fork:
      case Term_Hole:
      {invalidCodePath;} break;

      case Term_Constructor:
      case Term_Primitive:
      case Term_Function:
      case Term_Computation:
      {} break;
    }
  }

  if (DEBUG_LOG_normalize)
  {
    DEBUG_DEDENT(); DUMP("=> ", out0, "\n");
  }

  // assert(isSequenced(in0) || out0);
  assert(out0);
  return out0;
}

internal Term *
normalize(Typer *typer, Term *in0, String name_to_unfold)
{
  NormalizeContext ctx = {.depth=getScopeDepth(typer), .name_to_unfold=name_to_unfold};
  return normalize_(&ctx, in0);
}

internal Term *
normalize(Typer *env, Term *in0)
{
  NormalizeContext ctx = {.depth=getScopeDepth(env)};
  return normalize_(&ctx, in0);
}

inline void
addLocalBinding(Typer *env, String key, i32 var_id)
{
  auto lookup = lookupCurrentFrame(env->bindings, key, true);
  lookup.slot->var_id = var_id;
}

inline Scope *
introduceSignature(Scope *outer_scope, Arrow *signature)
{
  i32 param_count = signature->param_count;
  Scope *scope = newScope(outer_scope, param_count);
  for (i32 param_i=0; param_i < param_count; param_i++)
  {
    String  name = signature->param_names[param_i];
    Term   *type = toValue(scope, signature->param_types[param_i]);
    scope->values[param_i] = newStackPointer(name, scope->depth, param_i, type);
  }
  return scope;
}

inline GlobalBinding *
lookupGlobalName(Token *token)
{
  if (GlobalBinding *slot = lookupGlobalNameSlot(token->string, false))
    return slot;
  else
  {
    // note: assume that if the code gets here, then the identifier isn't in
    // local scope either.
    tokenError(token, "identifier not found");
    attach("identifier", token);
    return 0;
  }
}

inline Term *
lookupBuiltin(char *name)
{
  Token token = newToken(name);
  GlobalBinding *slot = lookupGlobalName(&token);
  assert(slot->count == 1);
  return slot->items[0];
}

inline void
addGlobalBinding(Token *name, Term *value)
{
  assert(inArena(global_state.top_level_arena, value));
  GlobalBinding *slot = lookupGlobalNameSlot(name->string, true);
  // TODO #cleanup check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));
  Token *name_copy = copyStruct(global_state.top_level_arena, name);
  value->global_name = name_copy;
}

inline void
addBuiltinGlobalBinding(char *key, Term *value)
{
  Token token = newToken(key);
  addGlobalBinding(&token, value);
}

inline void
addBuiltinGlobalBinding(String key, Term *value)
{
  Token token = newToken(key);
  addGlobalBinding(&token, value);
}

inline LookupLocalName
lookupLocalName(Typer *env, Token *token)
{
  LocalBindings *bindings = env->bindings;
  LookupLocalName out = {};
  for (i32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupCurrentFrame lookup = lookupCurrentFrame(bindings, token->string, false);
    if (lookup.found)
    {
      out.found       = true;
      out.var_index   = lookup.slot->var_id;
      out.stack_delta = stack_delta;
      break;
    }
    else
      bindings = bindings->tail;
  }

  return out;
}

inline b32
requireChar(char c, char *reason=0, Tokenizer *tk=global_tokenizer)
{
  auto out = false;
  if (!reason)
    reason = "";
  if (hasMore(tk))
  {
    Token token = nextToken(tk);
    if (token.string.length == 1 && token.string.chars[0] == c)
      out = true;
    else
      reportError(tk, &token, "expected character '%c' (%s)", c, reason);
  }
  return out;
}

inline b32
requireKind(TokenKind tc, char *message=0, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    if (nextToken(tk).kind == tc) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
requireIdentifier(char *message=0, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (!message)
  {
    message = "expected identifier";
  }
  if (hasMore())
  {
    Token token = nextToken(tk);
    if (isIdentifier(&token)) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
optionalKind(TokenKind tc, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (hasMore())
    if (peekToken(tk).kind == tc)
    {
      out = true;
      nextToken();
    }
  return out;
}

inline b32
optionalDirective(char *string, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken(tk);
    if (token.kind == Token_Directive)
    {
      if (equal(token.string, string))
      {
        out = true;
        eatToken();
      }
    }
  }
  return out;
}

inline b32
optionalChar(char c, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken(tk);
    if (equal(&token, c))
    {
      out = true;
      nextToken(tk);
    }
  }
  return out;
}

inline b32
optionalString(char *str, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken(tk);
    if (equal(&token, str))
    {
      out = true;
      nextToken(tk);
    }
  }
  return out;
}

struct OptionalU32 { b32 success; u32 value; };

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
  if (inString(")]}{,;:", token))
  {
    return true;
  }

  // Halt at all directives
  if (token->kind == Token_Directive)
  {
    return true;
  }

  switch (token->kind)
  {
    case Token_DoubleColon:
    case Token_ColonEqual:
    case Token_DoubleDash:
    case Token_StrongArrow:
    case Token_Keyword_in:
    case Token_DoubleDot:
    {
      return true;
    }
    default: {}
  }

  return false;
}

inline b32
seesExpressionEndMarker()
{
  Token token = peekToken();
  return isExpressionEndMarker(&token);
}

// todo remove recursion.
internal Term *
subExpressionAtPath(Term *in, TreePath *path)
{
  if (path)
  {
    switch (in->kind)
    {
      case Term_Composite:
      {
        Composite *composite = castTerm(in, Composite);
        Term *arg = composite->args[path->head];
        return subExpressionAtPath(arg, path->tail); 
      } break;

      invalidDefaultCase;
    }
  }
  else
    return in;
}

inline b32
matchType(Term *actual, Term *goal)
{
  b32 out = false;
  if (goal->kind == Term_Hole)
    out = true;
  else
  {
    if (equal(actual, goal))
      out = true;
  }
  return out;
}

inline b32
isGrounded(Term *in0)
{
  return isGlobalValue(in0) || (in0->kind == Term_Pointer);
}

internal b32
unify(UnifyContext *ctx, Term *in0, Term *goal0)
{
  b32 success = false;
  Arena *arena = temp_arena;

  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_unify)
  {
    DEBUG_INDENT(); DUMP("unify(", serial, ") ", in0, " with ", goal0, "\n");
  }

  if (isGrounded(in0))
  {
    success = equal(in0, goal0);
  }
  else
  {
    switch (in0->kind)
    {
      case Term_Variable:
      {
        Variable *in = (Variable *)in0;
        UnifyContext *lookup_ctx = ctx;
        for (i32 delta=0;  delta < in->delta && lookup_ctx;  delta++)
        {
          lookup_ctx = lookup_ctx->outer;
        }
        // unification variable
        if (Term *lookup = lookup_ctx->values[in->index])
        {
          success = equal(lookup, goal0);
        }
        else
        {
          Term *type = lookup_ctx->signature->param_types[in->index];
          b32 same_type = unify(lookup_ctx, type, goal0->type);
          if (same_type)
          {
            lookup_ctx->values[in->index] = goal0;
            success = true;
          }
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in = (Arrow *)in0;
        if (Arrow *goal = castTerm(goal0, Arrow))
        {
          i32 param_count = in->param_count;
          if (param_count == goal->param_count)
          {
            success = true;
            UnifyContext *new_ctx = extendUnifyContext(in, ctx);

            Term **intros = pushArray(arena, param_count, Term *);
            for (i32 param_i=0; param_i < param_count && success; param_i++)
            {
              String  name       = goal->param_names[param_i];
              Term   *param_type = substitute(goal->param_types[param_i], param_count, intros);
              intros[param_i] = newStackPointer(name, new_ctx->depth, param_i, param_type);
              if (!unify(new_ctx, in->param_types[param_i], param_type))
              {
                success = false;
              }
            }

            if (success)
            {
              Term *output_type = substitute(goal->output_type, param_count, intros);
              success = unify(new_ctx, in->output_type, output_type);
            }
          }
        }
      } break;

      case Term_Accessor:
      {
        Accessor *in = (Accessor *)in0;
        if (Accessor *goal = castTerm(goal0, Accessor))
        {
          if (in->index == goal->index)
          {
            success = unify(ctx, in->record, goal->record);
          }
        }
      } break;

      case Term_Composite:
      {
        Composite *in = (Composite *)in0;
        maybeDeref(&goal0);
        if (Composite *goal = castTerm(goal0, Composite))
        {
          if (unify(ctx, in->op, goal->op))
          {
            success = true;
            for (int i=0; i < in->arg_count && success; i++)
            {
              if (!unify(ctx, in->args[i], goal->args[i]))
              {
                success = false;
              }
            }
          }
        }
      } break;

      case Term_Union:
      case Term_Constructor:
      {
        invalidCodePath;
      } break;

      case Term_Primitive:
      {
        success = equal(in0, goal0);
      } break;

      case Term_Function:
      {
        success = false;
      } break;

      default:
      {
        todoIncomplete;
      } break;
    }
  }

  if (DEBUG_LOG_unify)
  {
    DEBUG_DEDENT(); DUMP("=>(", serial, ") ", ((char *)(success ? "true\n" : "false\n")));
  }

  return success;
}

inline SolveArgs
solveArgs(Solver *solver, Term *op, Term *goal0, Token *blame_token=0)
{
  i32    arg_count = 0;
  Term **args      = 0;

  i32 serial = DEBUG_SERIAL++;

  if (Arrow *signature = castTerm(getType(op), Arrow))
  {
    UnifyContext *ctx = newUnifyContext(signature, getScopeDepth(solver->typer));
    b32 unify_success = unify(ctx, signature->output_type, goal0);
    if (unify_success)
    {
      arg_count = signature->param_count;
      args      = ctx->values;
      for (i32 arg_i=0; arg_i < arg_count; arg_i++)
      {
        // solving loop
        if (!args[arg_i])
        {
          Term *type = substitute(signature->param_types[arg_i], arg_count, args);
          Term *arg  = solveGoal(solver, type);
          if (arg)
          {
            args[arg_i] = arg;
          }
          else
          {
            if (blame_token)
            {
              reportError(blame_token, "failed to solve arg %d", arg_i);
              // :solveArgs-only-error-if-unification-succeeds
              attach("arg_type", type);
              attach("serial", serial);
            }
            args = 0;
            break;
          }
        }
      }
    }
  }
  return SolveArgs{arg_count, args};
}

inline Computation *
newComputation_(Term *lhs, Term *rhs)
{
  Term *eq = newEquality(lhs, rhs);
  Computation *out = newTerm(temp_arena, Computation, eq);
  return out;
}

inline Term *
maybeEqualByComputation(Typer *typer, Term *lhs, Term *rhs)
{
  Term *out = 0;
  if (equal(normalize(typer, lhs),
            normalize(typer, rhs)))
  {
    out = newComputation_(lhs, rhs);
  }
  return out;
}

inline Term *
reaEqualByComputation(Typer *typer, Term *lhs, Term *rhs)
{
  Term *out = maybeEqualByComputation(typer, lhs, rhs);
  if (!out)
  {
    DUMP("lhs: ", lhs, " =/= rhs: ", rhs, "\n");
    invalidCodePath;
  }
  return out;
}

inline Term *
reaIdentity(Term *term)
{
  return newComputation_(term, term);
}

// todo: cutnpaste from "seekGoal"
inline Term *
reductioAdAbsurdum(Solver *solver, Term *goal)
{
  Term *out = 0;
  todoIncomplete;
#if 0
  if (getType(goal) != rea_Type) {todoIncomplete}
  auto temp = beginTemporaryMemory(solver->arena);
  if (solver->typer)
  {
    i32 delta = 0;
    for (Scope *scope = solver->typer->scope;
         scope && !out;
         scope=scope->outer)
    {
      // Arrow *arrow = scope->head;
      Arrow *arrow = 0;
      for (i32 param_i=0;
           (param_i < arrow->param_count) && !out;
           param_i++)
      {
        Term *var = newVariable(solver->arena, solver->typer, delta, param_i);
        Term *var_type = getType(var);
        if (equal(var_type, rea_False))
        {
          out = reaComposite(solver->arena, rea_falseImpliesAll, var, goal);
        }
        else if (Arrow *hypothetical = castTerm(var_type, Arrow))
        {
          if (hypothetical->output_type == rea_False)
          {
            SolveArgs solve_args = solveArgs(solver, var, rea_False);
            if (solve_args.args)
            {
              Term *f = newComposite(solver->arena, var, solve_args.arg_count, solve_args.args);
              out = reaComposite(solver->arena, rea_falseImpliesAll, f, goal);
            }
          }
        }
      }
      delta++;
    }
  }
  if (out)
    commitTemporaryMemory(temp);
  else
    endTemporaryMemory(temp);
#endif
  return out;
}

inline Term *
seekGoal(Solver *solver, Term *goal, b32 try_reductio=false)
{
  Term *out = 0;
  Arena *arena = temp_arena;
  if (solver->typer)  // no typer -> no local context
  {
    i32 delta = 0;
    for (Scope *scope = solver->typer->scope;
         scope && !out;
         scope=scope->outer)
    {
      for (i32 scope_i=0;
           (scope_i < scope->param_count) && !out;
           scope_i++)
      {
        Term *value = scope->values[scope_i];
        if (equal(value->type, rea.False))
        {
          out = reaComposite(rea.falseImpliesAll, value, goal);
        }
        else if (equal(value->type, goal))
        {
          out = value;
        }
        else if (Record *record = castRecord(value))
        {
          for (i32 member_i = 0; member_i < record->arg_count && !out; member_i++)
          {
            Term *member = record->args[member_i];
            if (equal(member->type, goal))
            {
              out = member;
            }
          }
        }
        if (!out && try_reductio && goal == rea.Type)
        {
          if (Arrow *hypothetical = castTerm(value->type, Arrow))
          {
            if (hypothetical->output_type == rea.False)
            {
              SolveArgs solve_args = solveArgs(solver, value, rea.False);
              if (solve_args.args)
              {
                Term *f = newComposite(arena, value, solve_args.arg_count, solve_args.args);
                out = reaComposite(rea.falseImpliesAll, f, goal);
              }
            }
          }
        }
      }
      delta++;
    }
  }
  return out;
}

forward_declare internal Term *
solveGoal(Solver *solver, Term *goal)
{
  Term *out = 0;
  Arena *arena = temp_arena;
  solver->depth++;
  b32 try_reductio = solver->try_reductio;
  solver->try_reductio = false;

  b32 should_attempt = true;
  if (solver->depth > MAX_SOLVE_DEPTH ||
      goal == rea.Type ||
      goal->kind == Term_Hole)
  {
    should_attempt = false;
  }
  else if (Union *uni = castTerm(goal, Union))
  {
    if (uni->global_name && goal != rea.False)
    {
      should_attempt = false;
    }
  }

  if (should_attempt)
  {
    if (DEBUG_LOG_solve)
    {
      i32 serial = DEBUG_SERIAL++;
      DEBUG_INDENT(); DUMP("solve(", serial, "): ", goal, "\n");
    }

    if (auto [l,r] = getEqualitySides(goal, false))
    {
      out = maybeEqualByComputation(solver->typer, l, r);
    }

    if (!out)
    {
      b32 tried_global_hints = false;
      for (HintDatabase *hints = solver->local_hints;
           !out;
           hints = hints->tail)
      {
        if (!hints)
        {
          if (!tried_global_hints && solver->use_global_hints)
          {
            hints = global_state.hints;
            tried_global_hints = true;
          }
        }

        if (hints)
        {
          Term *hint = hints->head;
          if (getType(hint)->kind == Term_Arrow)
          {
            SolveArgs solve_args = solveArgs(solver, hint, goal);
            if (solve_args.args)
            {
              out = newComposite(arena, hint, solve_args.arg_count, solve_args.args);
            }
          }
          else if (equal(getType(hint), goal))
          {
            out = hint;
          }
        }
        else
          break;
      }
    }

    if (!out)
    {
      out = seekGoal(solver, goal, try_reductio);
    }

    if (out)
    {
      assert(equal(getType(out), goal));
    }

    if (DEBUG_LOG_solve)
    {
      DEBUG_DEDENT(); DUMP("=> ", out, "\n");
    }
  }

  solver->depth--;
  return out;
}

inline b32
expectedWrongType(Typer *typer)
{
  return checkFlag(typer->expected_errors, Error_WrongType);
}

inline b32
expectedAmbiguous(Typer *typer)
{
  return checkFlag(typer->expected_errors, Error_Ambiguous);
}

inline TermArray
getFunctionOverloads(Typer *typer, Identifier *ident, Term *goal0)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL;
  TermArray out = {};
  if (equal(ident->token, "toArray"))
  {
    breakhere;
  }
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
  {
    if (goal0->kind == Term_Hole)
    {
      // bypass typechecking.
      out.items = slot->items;
      out.count = slot->count;
    }
    else
    {
      b32 matches = false;
      allocateArray(temp_arena, slot->count, out.items);
      for (int slot_i=0; slot_i < slot->count; slot_i++)
      {
        Term *item = slot->items[slot_i];
        if (Arrow *signature = castTerm(getType(item), Arrow))
        {
          UnifyContext *ctx = newUnifyContext(signature, getScopeDepth(typer->scope));
          matches = unify(ctx, signature->output_type, goal0);
        }
        if (matches)
        {
          out.items[out.count++] = slot->items[slot_i];
        }
      }
      if (out.count == 0)
      {
        if (expectedWrongType(typer)) silentError();
        else
        {
          reportError(ident, "found no matching overload");
          attach("serial", serial);
          attach("function", ident->token.string);
          attach("output_type_goal", goal0);
          attach("available_overloads", slot->count, slot->items, printOptionPrintType());
        }
      }
    }
  }
  else
  {
    reportError(ident, "identifier not found");
    attach("identifier", ident->token.string);
  }
  return out;
}

inline Term *
fillInEllipsis(Arena *arena, Typer *typer, Identifier *op_ident, Term *goal)
{
  Term *out = 0;
  pushContext(__func__);
  i32 serial = DEBUG_SERIAL++;

  if (goal->kind == Term_Hole)
  {
    reportError(op_ident, "cannot solve for arguments since we do know what the output type of this function should be");
  }
  else if (lookupLocalName(typer, &op_ident->token))
  {
    todoIncomplete;
  }
  else if (GlobalBinding *slot = lookupGlobalNameSlot(op_ident, false))
  {
    for (int slot_i=0;
         slot_i < slot->count && noError() && !out;
         slot_i++)
    {
      Term *item = slot->items[slot_i];
      SolveArgs solution = solveArgs(Solver{.typer=typer}, item, goal, &op_ident->token);
      if (solution.args)
      {
        // NOTE: we don't care which function matches, just grab whichever
        // matches first.
        Term **args = copyArray(arena, solution.arg_count, solution.args);
        out = newComposite(arena, slot->items[slot_i], solution.arg_count, args);
        assert(equal(getType(out), goal));
      }
    }
    if (!out && noError())
    {
      // :solveArgs-only-error-if-unification-succeeds
      reportError(op_ident, "either no matching overload was found, or failed to solve args");
      attach("available_overloads", slot->count, slot->items, printOptionPrintType());
      attach("serial", serial);
    }
  }
  else
  {
    reportError(op_ident, "identifier not found");
    attach("identifier", op_ident->token.string);
  }
  
  popContext();
  return out;
}

internal SearchOutput
searchExpression(Arena *arena, Typer *env, Term *lhs, Term* in0)
{
  b32       found = false;
  TreePath *path  = 0;
  if (equal(in0, lhs))
  {
    found = true;
  }
  else
  {
    maybeDeref(&in0);
    switch (in0->kind)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        SearchOutput op = searchExpression(arena, env, lhs, in->op);
        if (op.found)
        {
          allocate(arena, path);
          found       = true;
          path->head = -1;
          path->tail  = op.path;
        }
        else
        {
          for (int arg_i=0; arg_i < in->arg_count; arg_i++)
          {
            SearchOutput arg = searchExpression(arena, env, lhs, in->args[arg_i]);
            if (arg.found)
            {
              allocate(arena, path);
              found      = true;
              path->head = arg_i;
              path->tail = arg.path;
            }
          }
        }
      } break;

      case Term_Accessor:
      {
        Accessor* in = castTerm(in0, Accessor);
        SearchOutput recurse = searchExpression(arena, env, lhs, in->record);
        found = recurse.found;
        path  = recurse.path;
      } break;

      case Term_Hole:
      case Term_Computation:
      case Term_Primitive:
      case Term_Union:
      case Term_Function:
      case Term_Constructor:
      case Term_Variable:
      case Term_Arrow:
      case Term_Rewrite:
      case Term_Fork:
      {} break;
    }
  }
  return {.found=found, .path=path};
}

inline Ast *
parseSequence(b32 require_braces=true)
{
  Arena *arena = temp_arena;
  i32 serial = DEBUG_SERIAL;
  if (serial == 41)
    breakhere;
  Ast *out = 0;
  i32 count = 0;
  AstList *list = 0;

  b32 brace_opened = false;
  if (require_braces) brace_opened = requireChar('{');
  else                brace_opened = optionalChar('{');

  for (b32 expect_sequence_to_end = false;
       noError() && !expect_sequence_to_end;
       )
  {
    // Can't get out of this rewind business, because sometimes the sequence is empty :<
    Tokenizer tk_save = *global_tokenizer;
    Token  token_ = nextToken();
    Token *token  = &token_;
    Ast *ast0 = 0;
    String tactic = token->string;
    if (equal(tactic, "norm"))
    {
      pushContext("norm [EXPRESSION]");
      String name_to_unfold = {};

      if (optionalString("unfold"))
      {
        pushContext("unfold(FUNCTION_NAME)");
        if (requireChar('('))
        {
          if (requireIdentifier("expect function name"))
          {
            name_to_unfold = lastToken()->string;
            requireChar(')');
          }
        }
        popContext();
      }

      if (noError())
      {
        NormalizeMeAst *ast_goal = newAst(arena, NormalizeMeAst, token);
        ast_goal->name_to_unfold = name_to_unfold;
        if (seesExpressionEndMarker())
        {// normalize goal
          GoalTransform *ast = newAst(arena, GoalTransform, token);
          ast->new_goal = ast_goal;
          ast0 = ast;
        }
        else if (Ast *expression = parseExpression())
        {// normalize with let.
          Let *let = newAst(arena, Let, token);
          let->rhs  = expression;
          let->type = ast_goal;
          ast0 = let;
          if (expression->kind == Ast_Identifier)
          {
            // borrow the name if the expression is an identifier 
            let->lhs  = expression->token.string;
          }
          else
          {
            // NOTE This case can happen if it's a "seek"
          }
        }
      }

      popContext();
    }
    else if (equal(tactic, "rewrite"))
    {
      pushContext("rewrite EXPRESSION [in EXPRESSION]");
      RewriteAst *rewrite = newAst(arena, RewriteAst, token);
      if (optionalString("<-"))
      {
        rewrite->right_to_left = true;
      }
      rewrite->eq_proof = parseExpression();
      if (optionalKind(Token_Keyword_in))
      {
        rewrite->in_expression = parseExpression();
      }
      ast0 = rewrite;
      popContext();
    }
    else if (equal(tactic, "=>"))
    {
      pushContext("Goal transform: => NEW_GOAL [{ EQ_PROOF_HINT }]; ...");
      GoalTransform *ast = newAst(arena, GoalTransform, token);
      ast0 = ast;
      if (optionalDirective("print_proof"))
      {
        ast->print_proof = true;
      }
      if (optionalString("norm"))
      {
        ast->new_goal = newAst(arena, NormalizeMeAst, token);
      }
      else
      {
        ast->new_goal = parseExpression();
        if (optionalChar('{'))
        {
          if (optionalChar('}'))
          {
            // no hint provided, this case is just for editing convenience.
          }
          else
          {
            ast->hint = parseExpression();
            requireChar('}');
          }
        }
      }
      popContext();
    }
    else if (equal(tactic, "prove"))
    {
      pushContext("prove PROPOSITION {SEQUENCE} as IDENTIFIER");  // todo don't need the "as" anymore
      if (Ast *proposition = parseExpression())
      {
        if (Ast *proof = parseSequence(true))
        {
          String name = toString("anon");
          if (optionalString("as") && requireIdentifier("expected name for the proof"))
          {
            name = lastToken()->string;
          }
          if (noError())
          {
            Let *let = newAst(arena, Let, token);
            let->lhs  = name;
            let->rhs  = proof;
            let->type = proposition;
            ast0 = let;
          }
        }
      }
      popContext();
    }
    else if (equal(tactic, "return"))
    {
      ast0 = parseExpression();
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "fork"))
    {
      ast0 = parseFork();
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "seek"))
    {
      SeekAst *ast = newAst(arena, SeekAst, token);
      ast0 = ast;
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "reductio"))
    {
      ReductioAst *ast = newAst(arena, ReductioAst, token);
      ast0 = ast;
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "invert"))
    {
      Invert *ast = newAst(arena, Invert, token);
      ast->pointer = parseExpression();
      ast0 = ast;
    }
    else if (equal(tactic, "use"))
    {
      if (requireIdentifier())
      {
        Token op_name = *lastToken();
        Ellipsis *ellipsis = newAst(arena, Ellipsis, token);

        CompositeAst *ast = newAst(arena, CompositeAst, token);
        ast->op = newAst(arena, Identifier, &op_name);
        ast->arg_count = 1;
        pushItems(arena, ast->args, ellipsis);

        ast0 = ast;
        expect_sequence_to_end = true;
      }
    }
    else
    {
      if (isIdentifier(token))
      {
        // NOTE: identifiers can't be tactics, but I don't think that's a concern.
        Token *name = token;
        Token after_name = nextToken();
        switch (after_name.kind)
        {
          case Token_ColonEqual:
          {
            pushContext("let: NAME := VALUE");
            if (Ast *rhs = parseExpression())
            {
              Let *let = newAst(arena, Let, name);
              ast0 = let;
              let->lhs = name->string;
              let->rhs = rhs;
            }
            popContext();
          } break;

          case Token_Colon:
          {
            pushContext("typed let: NAME : TYPE := VALUE");
            if (Ast *type = parseExpression())
            {
              if (requireKind(Token_ColonEqual, ""))
              {
                if (Ast *rhs = parseExpression())
                {
                  Let *let = newAst(arena, Let, name);
                  let->lhs  = name->string;
                  let->rhs  = rhs;
                  let->type = type;
                  ast0 = let;
                }
              }
            }
            popContext();
          } break;

          default:
          {
            reportError("invalid syntax for sequence item (keep in mind that we're in a sequence, so you need to use the \"return\" keyword to return an expression)");
          } break;
        }
      }
      else if (isExpressionEndMarker(token))
      {// synthetic hole
        ast0  = newAst(arena, Hole, token);
        *global_tokenizer = tk_save;
        expect_sequence_to_end = true;
      }
      else
      {
        reportError("expected a sequence item");
      }
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->head = ast0;
      new_list->tail  = list;
      list = new_list;
      // f.ex function definitions doesn't need to end with ';'
      optionalChar(';');
    }
  }

  if (brace_opened) requireChar('}');

  if (noError())
  {
    assert(count > 0);
    Ast *previous = 0;
    for (i32 item_i = 0; item_i < count; item_i++)
    {
      Ast *item0 = list->head;
      if (item_i > 0)
      {
        if (Let *let = castAst(item0, Let))
          let->body = previous;
        else if (RewriteAst *rewrite = castAst(item0, RewriteAst))
          rewrite->body = previous;
        else if (GoalTransform *item = castAst(item0, GoalTransform))
          item->body = previous;
        else if (Invert *item = castAst(item0, Invert))
          item->body = previous;
        else
          invalidCodePath;
      }
      previous = item0;
      if (item_i != count-1)
        list = list->tail;
    }
    out = list->head;
  }

  return out;
}

inline Ast *
newSyntheticAst(Term *term, Token *token)
{
  SyntheticAst *out = newAst(temp_arena, SyntheticAst, token);
  out->term = term;
  return out;
}

internal Arrow *
copyArrow(Arena *arena, Arrow *in)
{
  Arrow *out = copyTerm(arena, in);
  return out;
}

inline Term *
buildCtorAst(Arena *arena, CtorAst *in, Term *output_type)
{
  Term *out = 0;
  if (Union *uni = getUnionOrPolyUnion(output_type))
  {
    if (in->ctor_i < uni->ctor_count)
    {
      out = uni->constructors[in->ctor_i];
    }
    else
      reportError(in, "union only has %d constructors", uni->ctor_count);
  }
  else
  {
    reportError(in, "cannot guess union of constructor");
  }
  return out;
}

inline HintDatabase *
addHint(Arena *arena, HintDatabase *hint_db, Term *term)
{
  HintDatabase *new_hints = pushStruct(arena, HintDatabase, true);
  new_hints->head = term;
  new_hints->tail = hint_db;
  return new_hints;
}

inline Term *
getOverloadFromDistinguisher(GlobalBinding *lookup, Term *distinguisher)
{
  Term *out = 0;
  if (distinguisher->kind != Term_Union)
  {
    todoIncomplete;
  }

  for (i32 slot_i=0;
       slot_i < lookup->count && !out;
       slot_i++)
  {
    Term *item = lookup->items[slot_i];
    if (Arrow *signature = castTerm(getType(item), Arrow))
    {
      for (i32 param_i=0; param_i < signature->param_count && !out; param_i++)
      {
        Term *type0 = signature->param_types[param_i];
        if (equal(type0, distinguisher))
        {
          out = item;
        }
        else if (Composite *type = castTerm(type0, Composite))
        {
          if (equal(type->op, distinguisher))
          {
            out = item;
          }
        }
      }
    }
  }
  return out;
}

inline Term *
getOverloadFromDistinguisher(Token *token, const char *name, Term *distinguisher)
{
  Term *out = 0;
  if (GlobalBinding *lookup = lookupGlobalNameSlot(toString(name), false))
  {
    out = getOverloadFromDistinguisher(lookup, distinguisher);
  }
  else
    reportError(token, "no function named \"%s\" found that matches distinguisher", name);

  return out;
}

inline b32
stringLessThan(String a, String b)
{
  b32 out = false;
  if (a.length < b.length)
    out = true;
  else if (a.length == b.length)
  {
    for (i32 i=0; i < a.length; i++)
    {
      if (a.chars[i] < b.chars[i])
      {
        out = true;
        break;
      }
    }
  }
  return out;
}

inline b32
algebraLessThan(Term *a0, Term *b0)
{
  b32 out = false;
  if (a0->global_name && b0->global_name)
  {
    out = stringLessThan(a0->global_name->string, b0->global_name->string);
  }
  else
  {
    switch (a0->kind)
    {
      case Term_Variable:
      {
        Variable *a = castTerm(a0, Variable);
        if (Variable *b = castTerm(b0, Variable))
          out = stringLessThan(a->name, b->name);
      } break;
    }
  }
  return out;
}

inline TreePath *
treePath(i32 head, TreePath *tail)
{
  TreePath *out = pushStruct(temp_arena, TreePath, true);
  out->head = head;
  out->tail = tail;
  return out;
}

inline TreePath *
reverseInPlace(TreePath *in)
{
  TreePath *out = 0;
  for (TreePath *it = in; it; )
  {
    TreePath *next_it = it->tail;
    it->tail = out;
    out = it;
    it = next_it;
  }
  return out;
}

inline TreePath *
reversePath(Arena *arena, TreePath *in)
{
  TreePath *out = 0;
  for (TreePath *it = in; it; it = it->tail)
  {
    TreePath *new_out = pushStruct(arena, TreePath, true);
    new_out->head = it->head;
    new_out->tail = out;
    out = new_out;
  }
  return out;
}

inline TreePath *
addToEnd(Arena *arena, TreePath *prefix, i32 item)
{
  TreePath *reverse_prefix = reversePath(arena, prefix);
  TreePath *out = pushStruct(arena, TreePath, true);
  out->head = item;
  out->tail = reverse_prefix;
  out = reverseInPlace(out);
  return out;
}

inline Term *
getTransformResult(Term *in)
{
  auto [_, out] = getEqualitySides(in->type);
  return out;
}

inline Term *
eqChain(Term *e1, Term *e2)
{
  auto [a,b] = getEqualitySides(getType(e1));
  auto [_,c] = getEqualitySides(getType(e2));
  Term *A = getType(a);
  Term *out = reaComposite(rea.eqChain, A, a,b,c, e1,e2);
  return out;
}

inline Term *
transformSubExpression(Term *eq_proof, TreePath *path, Term *in)
{
  Term *id = newIdentity(in);
  return newRewrite(temp_arena, eq_proof, id, treePath(2, path), true);
}

inline Term *
algebraFlatten(Typer *typer, Algebra *algebra, Term *in0)
{
  Term *out = 0;
  Term *expression0 = in0;

  if (Composite *expression = castTerm(expression0, Composite))
  {
    if (equal(expression->op, algebra->add))
    {
      Term *r = expression->args[1];
      if (Term *norm_r = algebraFlatten(typer, algebra, r))
      {
        out = transformSubExpression(norm_r, treePath(1, 0), expression0);
        expression0 = getTransformResult(out);
      }
    }
  }

  for (b32 stop = false; !stop; )
  {
    stop = true;
    if (Composite *expression = castTerm(expression0, Composite))
    {
      if (equal(expression->op, algebra->add))
      {
        Term *l0 = expression->args[0];
        Term *r  = expression->args[1];

        if (Composite *l = castTerm(l0, Composite))
        {
          if (equal(l->op, algebra->add))
          {
            stop = false;
            Term *new_proof = reaComposite(algebra->addAssociative, l->args[0], l->args[1], r);
            if (out)
              out = eqChain(out, new_proof);
            else
              out = new_proof;
            expression0 = getTransformResult(out);
          }
        }
      }
    }
  }

  return out;
}

internal Term *
getFoldList(Typer *typer, Algebra *algebra, Term *in0)
{
  // todo need to pass the operator in here.
  Term *out = 0;
  if (Composite *in = castTerm(in0, Composite))
  {
    if (equal(in->op, algebra->add))
    {
      Term *tail = getFoldList(typer, algebra, in->args[1]);
      out = reaCons(in->args[0], tail);
    }
  }
  if (!out)
  {
    out = reaSingle(in0);
  }
  return out;
}

internal TermArray
toCArray(Arena *arena, Term *list0)
{
  TermArray out = {};
  const i32 MAX_TERM_ARRAY_LENGTH = 20;
  allocateArray(arena, MAX_TERM_ARRAY_LENGTH, out.items);

  b32 stop=false;
  for (Term *iter0=list0; !stop; )
  {
    Composite *iter = castTerm(iter0, Composite);
    Term *head = iter->args[0];
    out.items[out.count++] = head;
    assert(out.count <= MAX_TERM_ARRAY_LENGTH);

    Constructor *ctor = castTerm(iter->op, Constructor);
    if (ctor->index == 0)
    {
      stop = true;
    }
    else
    {
      assert(ctor->index == 1);
      Term *tail = iter->args[1];
      iter0 = tail;
    }
  }

  return out;
}

internal Term *
toReaList(Term **array, i32 count)
{
  assert(count > 0);
  Term *T = getType(array[0]);
  Term *out = reaComposite(rea.single, T, array[count-1]);
  for (i32 i=count-2; i >= 0; i--)
  {
    out = reaComposite(rea.cons, T, array[i], out);
  }
  return out;
}

internal i32
qsortPartition(Term **in, i32 *indexes, i32 count)
{
  Term *pivot = in[count-1];
  i32 write = 0;
  for (i32 i=0; i < count-1; i++)
  {
    if (algebraLessThan(in[i], pivot))
    {
      SWAP(in[write], in[i]);
      SWAP(indexes[write], indexes[i]);
      write++;
    }
  }
  SWAP(in[write], in[count-1]);
  SWAP(indexes[write], indexes[count-1]);
  return write;
}

internal void
quickSort(Term **in, i32 *indexes, i32 count)
{
  if (count > 1)
  {
    i32 pivot_index = qsortPartition(in, indexes, count);
    quickSort(in, indexes, pivot_index);
    quickSort(in+(pivot_index+1), indexes+(pivot_index+1), count-(pivot_index+1));
  }
}

inline b32
reaIsNil(Term *in0)
{
  todoIncomplete;
}

internal Term *
algebraSort(Record *in)
{
  Term *out = 0;
  Term *list_type = reaListType(in);
  if (reaIsNil(in))
  {
    out = reaComposite(rea.permuteNil);
  }
  else
  {
    Term *head = reaHead(in);
    Term *tail = reaTail(in);
    if (reaIsNil(tail))
    {
      out = reaComposite(rea.permuteSame, in);
    }
    else
    {
      Term *tail_sort = algebraSort(castRecord(tail));
      Term *new_tail = getTransformResult(tail_sort);
      if (algebraLessThan(head, reaHead(new_tail)))
      {
        // insertion goes here...
      }
      else
      {
        out = reaComposite(rea.permuteSkip, list_type, head, tail, new_tail, tail_sort);
      }
    }
  }
  return out;
}

internal Term *
buildTestSort(Typer *typer, CompositeAst *ast)
{
  Term *out = 0;
  assert(ast->arg_count == 1);
  if (Term *list0 = buildTerm(typer, ast->args[0], holev))
  {
    if (Record *list = castRecord(list0))
    {
      out = algebraSort(list);
    }
    else
    {
      reportError(ast, "please pass me a list");
    }
  }
  return out;
}

inline Term *
buildAlgebraNorm(Typer *typer, CompositeAst *in)
{
  Term *out = 0;
  if (in->arg_count == 1)
  {
    if (Term *expression0 = buildTerm(typer, in->args[0], holev).value)
    {
      b32 found_algebra_match = false;
      for (AlgebraDatabase *algebras = global_state.algebras;
           algebras && !found_algebra_match;
           algebras = algebras->tail)
      {
        Algebra *algebra = &algebras->head;
        if (equal(getType(expression0), algebra->type))
        {
          found_algebra_match = true;

          Term *eq_flattened = algebraFlatten(typer, algebra, expression0);
          Term *flattened    = eq_flattened ? getTransformResult(eq_flattened) : expression0;
          Term *list         = getFoldList(typer, algebra, flattened);

          Term *folded    = reaComposite(rea.fold, algebra->type, algebra->add, list);
          Term *eq_folded = reaEqualByComputation(typer, flattened, folded);
          out = eq_flattened ? eqChain(eq_flattened, eq_folded) : eq_folded;
        }
      }
    }
  }
  else
    reportError("expected 1 argument");

  if (!out && noError())
    reportError(in, "expression is already algebraically normalized");

  return out;
}

inline Term *
copyToGlobalArena(Term *in0)
{
  Term *out0 = 0;
  Arena *arena = global_state.top_level_arena;
  if (isGlobalValue(in0))
  {
    out0 = in0;
  }
  else
  {
    switch (in0->kind)
    {
      case Term_Variable:
      {
        Variable *in  = castTerm(in0, Variable);
        Variable *out = copyTerm(arena, in);
        out0 = out;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyTerm(arena, in);
        out->op = copyToGlobalArena(in->op);
        allocateArray(arena, in->arg_count, out->args);
        for (i32 i=0; i < in->arg_count; i++)
        {
          out->args[i] = copyToGlobalArena(in->args[i]);
        }
        out0 = out;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);
        i32 param_count = in->param_count;
        allocateArray(arena, param_count, out->param_types);
        for (i32 i=0; i < param_count; i++)
        {
          out->param_types[i] = copyToGlobalArena(in->param_types[i]);
        }
        out->output_type = copyToGlobalArena(in->output_type);
        // :arrow-copy-done-later
        out->param_names = copyArray(arena, param_count, in->param_names);
        out->param_flags = copyArray(arena, param_count, in->param_flags);
        out0 = out;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyTerm(arena, in);
        out->body = copyToGlobalArena(in->body);
        out0 = out;
      } break;

      case Term_Fork:
      {
        Fork *in  = castTerm(in0, Fork);
        Fork *out = copyTerm(arena, in);
        out->subject = copyToGlobalArena(in->subject);
        allocateArray(arena, in->case_count, out->bodies);
        for (i32 i=0; i < in->case_count; i++)
        {
          out->bodies[i] = copyToGlobalArena(in->bodies[i]);
        }
        out0 = out;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        Rewrite *out = copyTerm(arena, in);
        out->eq_proof = copyToGlobalArena(in->eq_proof);
        out->body     = copyToGlobalArena(in->body);
        out0 = out;
      } break;

      case Term_Computation:
      {
        Computation *in = castTerm(in0, Computation);
        Computation *out = copyTerm(arena, in);
        out0 = out;
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Accessor *out = copyTerm(arena, in);
        out->record = copyToGlobalArena(in->record);
        out0 = out;
      } break;

      invalidDefaultCase;
    }

    out0->type = copyToGlobalArena(in0->type);
  }
  return out0;
}


inline Function *
buildFunctionGivenSignature(Typer *typer, Arrow *signature, Ast *in_body,
                            i32 function_flags=0, Token *global_name=0)
{
  i32 unused_var serial = DEBUG_SERIAL;
  // :persistent-global-function.

  // NOTE: We MUST control the arena, otherwise the self-reference will be
  // invalidated (TODO: maybe the copier should know about self-reference).
  Arena *arena = global_name ? global_state.top_level_arena : temp_arena;

  Function *out       = newTerm(arena, Function, signature);
  out->function_flags = function_flags;

  Term *body = 0;
  Typer new_typer = *typer;
  {
    Typer *typer = &new_typer;
    typer->scope = introduceSignature(typer->scope, signature);
    extendBindings(typer);

    if (global_name)
    {
      // NOTE: add binding first to support recursion
      addGlobalBinding(global_name, out);
      current_global_function      = out;
      current_global_function_args = typer->scope->values;
    }

    for (i32 index=0; index < signature->param_count; index++)
    {
      String name = signature->param_names[index];
      addLocalBinding(typer, name, index);
    }
    Term *body_type = toValue(typer->scope, signature->output_type);
    body = buildTerm(typer, in_body, body_type);

    current_global_function       = 0;
    current_global_function_args = 0;
  }

  if (body)
  {
    out->body = toAbstractTerm(temp_arena, body, getScopeDepth(typer));
    if (global_name)
    {
      out->body = copyToGlobalArena(out->body);
    }
  }
  return out;
}

inline Term *
buildWithNewAssets(Typer *typer, i32 asset_count, String *names, Term **assets, Ast *body, Term *goal)
{
  Term *out = 0;
  Arena *arena = temp_arena;
  Arrow *signature = newTerm(arena, Arrow, rea.Type);
  signature->param_count = asset_count;
  allocateArray(arena, asset_count, signature->param_names);
  allocateArray(arena, asset_count, signature->param_types);
  allocateArray(arena, asset_count, signature->param_flags, true);

  signature->param_names = names;
  if (!names)
  {
    allocateArray(arena, asset_count, signature->param_names, true);
  }

  for (i32 i=0; i < asset_count; i++)
  {
    signature->param_types[i] = assets[i]->type;
  }
  signature->output_type = goal;

  if (Function *fun = buildFunctionGivenSignature(typer, signature, body))
  {
    out = newComposite(arena, fun, asset_count, assets);
  }

  return out;
}

inline Term *
buildWithNewAsset(Typer *typer, String name, Term *asset, Ast *body, Term *goal)
{
  pushItemsAs(temp_arena, assets, asset);
  pushItemsAs(temp_arena, names, name);
  Term *out = buildWithNewAssets(typer, 1, names, assets, body, goal);
  return out;
}

forward_declare internal BuildTerm
buildTerm(Typer *typer, Ast *in0, Term *goal)
{
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;

  assert(goal);
  Arena *arena = temp_arena;
  Term *value = 0;
  b32 should_check_type = true;
  b32 recursed = false;
  b32 try_reductio = typer->try_reductio;
  if (!checkFlag(in0->flags, AstFlag_Generated))
  {
    // NOTE: Only turn off reductio if the user wanna do something (instead of
    // automated generated expressions).
    typer->try_reductio = false;
  }

  switch (in0->kind)
  {
    case Ast_CompositeAst:
    {
      CompositeAst *in  = castAst(in0, CompositeAst);

      if (in->arg_count == 1 &&
          in->args[0]->kind == Ast_Ellipsis)
      {
        // Solve all arguments. NOTE: We might invent some syntactic convenience
        // for this, but in future we might add the ability to specify only some
        // paramters. So this case will occur anyway.
        if (Identifier *op_ident = castAst(in->op, Identifier))
        {
          value = fillInEllipsis(arena, typer, op_ident, goal);
        }
        else
        {
          reportError(in->args[0], "todo: ellipsis only works with identifier atm");
        }
      }
      else if (equal(in->op->token, "test_sort"))
      {
        // macro interception
        value = buildTestSort(typer, in);
      }
      else if (equal(in->op->token, "algebra_norm"))
      {
        // macro interception
        todoIncomplete;
        // out0 = buildAlgebraNorm(arena, typer, in);
      }
      else
      {
        TermArray op_list = {};
        b32 should_build_op = true;
        if (Identifier *op_ident = castAst(in->op, Identifier))
        {
          if (!lookupLocalName(typer, &in->op->token))
          {
            should_build_op = false;
            op_list = getFunctionOverloads(typer, op_ident, goal);
          }
        }
        else if (CtorAst *op_ctor = castAst(in->op, CtorAst))
        {
          if (Term *ctor = buildCtorAst(arena, op_ctor, goal))
          {
            should_build_op = false;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.count    = 1;
            op_list.items[0] = ctor;
          }
        }

        if (noError() && should_build_op)
        {
          if (Term *op0 = buildTerm(typer, in->op, holev).value)
          {
            op_list.count = 1;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.items[0] = op0;
          }
        }

        Typer new_typer = *typer;
        {
          Typer *typer = &new_typer;
          if (op_list.count > 1)
          {
            setFlag(&typer->expected_errors, Error_WrongType);
          }

          for (i32 attempt=0;
               (attempt < op_list.count) && (!value) && noError();
               attempt++)
          {
            Term *op = op_list.items[attempt];
            if (Arrow *signature = getSignature(op))
            {
              i32 param_count = signature->param_count;
              Ast **expanded_args = in->args;
              if (param_count != in->arg_count)
              {
                i32 explicit_param_count = getExplicitParamCount(signature);
                if (in->arg_count == explicit_param_count)
                {
                  allocateArray(arena, param_count, expanded_args);
                  for (i32 param_i = 0, arg_i = 0;
                       param_i < param_count;
                       param_i++)
                  {
                    if (isInferredParameter(signature, param_i))
                    {
                      // NOTE: We fill the missing argument with synthetic holes,
                      // because the user input might also have actual holes, so
                      // this makes the code more uniform.
                      expanded_args[param_i] = newAst(arena, Hole, &in->op->token);
                    }
                    else
                    {
                      assert(arg_i < explicit_param_count);
                      expanded_args[param_i] = in->args[arg_i++];
                    }
                  }
                }
                else
                {
                  if (expectedWrongType(typer)) silentError();
                  else
                  {
                    reportError(&in0->token, "argument count does not match the number of explicit parameters (expected: %d, got: %d)", explicit_param_count, in->arg_count);
                  }
                }
              }

              if (noError())
              {
                UnifyContext *ctx = newUnifyContext(signature, getScopeDepth(typer->scope));
                Term **args = ctx->values;
                b32 stack_has_hole = false;  // This var is an optimization: in case we can just solve all the args in one pass.

                if (goal->kind != Term_Hole)
                {
                  b32 ouput_unify = unify(ctx, signature->output_type, goal);
                  if (!ouput_unify)
                  {
                    if (expectedWrongType(typer)) silentError();
                    else
                    {
                      reportError(in0, "cannot unify output");
                      attach("signature->output_type", signature->output_type);
                      attach("serial", serial);
                    }
                  }
                }

                for (int arg_i = 0;
                     (arg_i < param_count) && noError();
                     arg_i++)
                {
                  // First round: Build and Infer arguments.
                  Term *param_type0 = signature->param_types[arg_i];
                  Ast *in_arg = expanded_args[arg_i];
                  b32 arg_was_filled = false;
                  if (args[arg_i])
                  {
                    arg_was_filled = true;
                    if (in_arg->kind != Ast_Hole)
                    {
                      Term *already_filled_arg_type = args[arg_i]->type;
                      if (Term *arg = buildTerm(typer, in_arg, already_filled_arg_type))
                      {
                        if (!equal(arg, args[arg_i]))
                        {
                          reportError(in_arg, "actual arg differs from inferred arg");
                          attach("actual", arg);
                          attach("inferred", args[arg_i]);
                        }
                      }
                    }
                  }
                  else if (in_arg->kind != Ast_Hole)
                  {
                    if (stack_has_hole)
                    {
                      Typer new_typer = *typer;
                      setFlag(&new_typer.expected_errors, Error_Ambiguous);
                      if (Term *arg = buildTerm(&new_typer, in_arg, holev))
                      {
                        args[arg_i] = arg;
                        arg_was_filled = true;
                        b32 unify_result = unify(ctx, param_type0, arg->type);
                        if (!unify_result)
                        {
                          if (expectedWrongType(typer)) silentError();
                          else
                          {
                            reportError(in_arg, "cannot unify parameter type with argument %d's type", arg_i);
                            attach("serial", serial);
                            attach("parameter_type", param_type0);
                            attach("argument_type", arg->type);
                          }
                        }
                      }
                      else if (hasSilentError())
                      {
                        wipeError();  // :argument-builds-retried-in-round-two
                      }
                    }
                    else
                    {
                      Term *expected_arg_type = substitute(param_type0, param_count, args);
                      if (Term *arg = buildTerm(typer, in_arg, expected_arg_type).value)
                      {
                        args[arg_i] = arg;
                        arg_was_filled = true;
                      }
                    }
                  }
                  stack_has_hole = stack_has_hole || !arg_was_filled;
                }

                if (noError() && stack_has_hole)
                {
                  // Second round, Build and Solve the remaining args.
                  for (int arg_i = 0;
                       (arg_i < param_count) && noError();
                       arg_i++)
                  {
                    if (!args[arg_i])
                    {
                      Ast *in_arg = expanded_args[arg_i];
                      Term *param_type0 = signature->param_types[arg_i];
                      Term *expected_arg_type = substitute(param_type0, param_count, args);
                      if (in_arg->kind == Ast_Hole)
                      {
                        if (Term *fill = solveGoal(Solver{.typer=typer, .use_global_hints=true}, expected_arg_type))
                        {
                          args[arg_i] = fill;
                        }
                        else if (expectedAmbiguous(typer))
                        {
                          silentError();
                        }
                        else
                        {
                          reportError(in_arg, "cannot solve argument %d", arg_i);
                          attach("expected_arg_type", expected_arg_type);
                          attach("serial", serial);
                        }
                      }
                      else if (Term *arg = buildTerm(typer, in_arg, expected_arg_type))
                      {
                        // :argument-builds-retried-in-round-two
                        args[arg_i] = arg;
                      }
                    }
                  }
                }

                if (noError())
                {
                  assert(!value);
                  if (Function *fun = castTerm(op, Function))
                  {
                    if (checkFlag(fun->function_flags, FunctionFlag_expand))
                    {
                      value = substitute(fun->body, param_count, args);
                    }
                  }
                  if (!value)
                  {
                    args = copyArray(arena, param_count, args);
                    value = newComposite(arena, op, param_count, args);
                  }
                }
              }
            }
            else
            {
              if (expectedWrongType(typer)) silentError();
              else
              {
                reportError(in->op, "operator must have an arrow type");
                attach("operator type", getType(op));
              }
            }

            if (op_list.count > 1)
            {
              if (hasSilentError())
              {
                wipeError();
                if (attempt == op_list.count-1)
                {
                  reportError(in->op, "found no suitable overload");
                  attach("available_overloads", op_list.count, op_list.items, printOptionPrintType());
                  attach("serial", serial);
                }
              }
            }
          }
        }
      }
    } break;

    case Ast_Identifier:
    {
      Identifier *in = castAst(in0, Identifier);
      Token *name = &in->token;
      if (goal == rea.U32)
      {
        i32 number = toInt32(name);  // todo: wrong number type.
        if (noError())
        {
          Primitive *primitive_num = newTerm(arena, Primitive, rea.U32);
          primitive_num->u32    = number;
          primitive_num->prim_kind = Primitive_U32;
          value = primitive_num;
        }
      }
      else
      {
        if (LookupLocalName local = lookupLocalName(typer, name))
        {
          value = lookupStack(typer, local.stack_delta, local.var_index);
        }
        else
        {
          if (GlobalBinding *globals = lookupGlobalName(name))
          {
            for (i32 value_id = 0; value_id < globals->count; value_id++)
            {
              Term *slot_value = globals->items[value_id];
              if (matchType(getType(slot_value), goal))
              {
                if (value)
                {// ambiguous
                  if (expectedAmbiguous(typer)) silentError();
                  else
                  {
                    tokenError(name, "not enough type information to disambiguate global name");
                    attach("serial", serial);
                  }
                  break;
                }
                else
                {
                  value = slot_value;
                }
              }
            }
            if (!value)
            {
              if (expectedWrongType(typer)) silentError();
              else
              {
                tokenError(name, "global name does not match expected type");
                attach("name", name);
                attach("expected_type", goal);
                attach("serial", serial);
                if (globals->count == 1)
                {
                  attach("actual_type", getType(globals->items[0]));
                }
              }
            }
          }

          if (value)
          {
            should_check_type = false;
          }
        }
      }
    } break;

    case Ast_Hole:
    {
      Solver solver = {.typer=typer, .use_global_hints=true, .try_reductio=try_reductio};
      if (Term *solution = solveGoal(&solver, goal))
      {
        value = solution;
      }
      else
      {
        if (serial == 33873)
          breakhere;
        reportError(in0, "please provide an expression here");
        attach("serial", serial);
      }
    } break;

    case Ast_SyntheticAst:
    {
      SyntheticAst *in = (SyntheticAst *)(in0);
      value = toValue(typer->scope, in->term);
    } break;

    case Ast_ArrowAst:
    {
      ArrowAst *in = (ArrowAst *)(in0);
      Arrow *out = newTerm(arena, Arrow, rea.Type);
      i32 param_count = in->param_count;
      // :arrow-copy-done-later
      out->param_count = param_count;
      out->param_names = in->param_names;
      out->param_flags = in->param_flags;
      out->param_types = pushArray(arena, param_count, Term*);
      {
        Scope *scope = typer->scope = newScope(typer->scope, out->param_count);
        extendBindings(typer);
        for (i32 i=0; i < param_count && noError(); i++)
        {
          if (Term *param_type = buildTerm(typer, in->param_types[i], holev).value)
          {
            out->param_types[i] = toAbstractTerm(arena, param_type, getScopeDepth(scope->outer));
            scope->values[i] = newStackPointer(out->param_names[i], scope->depth, i, param_type);
            String name = in->param_names[i];
            addLocalBinding(typer, name, i);
          }
        }

        if (noError())
        {
          value = out;
          if (Term *output_type = buildTerm(typer, in->output_type, holev).value)
          {
            out->output_type = toAbstractTerm(arena, output_type, getScopeDepth(scope->outer));
          }
        }
        unwindBindingsAndScope(typer);
      }
    } break;

    case Ast_AccessorAst:
    {
      AccessorAst *in = (AccessorAst *)(in0);
      if (Term *record0 = buildTerm(typer, in->record, holev))
      {
        i32 ctor_i = 0;
        Term **members = 0;
        if (Record *record = castRecord(record0))
        {
          ctor_i  = record->ctor->index;
          members = record->members;
        }
        else
        {
          reportError(in->record, "cannot access a non-record");
        }

        if (noError())
        {
          Union *uni = getUnionOrPolyUnion(getType(record0));
          Arrow *struc = getConstructorSignature(uni, ctor_i);
          i32 param_count = struc->param_count;
          b32 valid_param_name = false;
          i32 field_i = -1;
          for (i32 param_i=0; param_i < param_count; param_i++)
          {// figure out the param id
            if (equal(in->field_name.string, struc->param_names[param_i]))
            {
              field_i = param_i;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
          {
            value = members[field_i];
          }
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", getConstructorName(uni, ctor_i));
          }
        }
      }
    } break;

    case Ast_FunctionAst:
    {
      FunctionAst *in = castAst(in0, FunctionAst);
      Term *type = goal;
      if (in->signature)
      {
        type = buildTerm(typer, in->signature, holev).value;
      }

      if (noError())
      {
        if (Arrow *signature = castTerm(type, Arrow))
        {
          Function *fun = buildFunctionGivenSignature(typer, signature, in->body, in->function_flags);
          value = fun;
        }
        else
        {
          reportError(in0, "function signature is required to be an arrow type");
          attach("type", type);
        }
      }
    } break;

    case Ast_RewriteAst:
    {
      if (goal->kind == Term_Hole)
      {
        reportError(in0, "we do not know what the goal is, so nothing to rewrite");
      }
      else
      {
        RewriteAst *in  = castAst(in0, RewriteAst);
        if (Term *eq_proof = buildTerm(typer, in->eq_proof, holev).value)
        {
          Term *proof_type = getType(eq_proof);
          if (auto [lhs, rhs] = getEqualitySides(proof_type, false))
          {
            Term *from = in->right_to_left ? rhs : lhs;
            Term *to   = in->right_to_left ? lhs : rhs;
            if (in->in_expression)
            {
              if (Term *in_expression = buildTerm(typer, in->in_expression, holev).value)
              {
                if (SearchOutput search = searchExpression(arena, typer, from, getType(in_expression)))
                {
                  b32 right_to_left = !in->right_to_left;  // since we rewrite the body, not the goal.
                  Term *asset = newRewrite(arena, eq_proof, in_expression, search.path, right_to_left);
                  String name = {};
                  Pointer *var = castTerm(in_expression, Pointer);
                  if (var && var->is_stack_pointer)
                  {
                    name = var->stack.name;
                  }
                  else
                  {
                    todoIncomplete;
                  }
                  value = buildWithNewAsset(typer, name, asset, in->body, goal);
                }
                else
                {
                  reportError(in0, "cannot find a place to apply the rewrite");
                  attach("substitution", proof_type);
                  attach("in_expression_type", getType(in_expression));
                }
              }
            }
            else
            {
              SearchOutput search = searchExpression(arena, typer, from, goal);
              if (search.found)
              {
                Term *new_goal = rewriteTerm(arena, from, to, search.path, goal);
                if (Term *body = buildTerm(typer, in->body, new_goal).value)
                {
                  value = newRewrite(arena, eq_proof, body, search.path, in->right_to_left);
                }
              }
              else
              {
                reportError(in0, "cannot find a place to apply the rewrite");
                attach("substitution", proof_type);
              }
            }
          }
          else
          {
            reportError(in->eq_proof, "please provide a proof of equality for rewrite");
            attach("got", proof_type);
          }
        }
      }
    } break;

    case Ast_GoalTransform:
    {
      GoalTransform *in = castAst(in0, GoalTransform);
      Term     *new_goal      = 0;
      Term     *eq_proof      = 0;
      TreePath *rewrite_path  = 0;
      b32       right_to_left = false;

      if (NormalizeMeAst *in_new_goal = castAst(in->new_goal, NormalizeMeAst))
      {// just normalize the goal, no need for tactics (for now).
        Term *norm_goal = normalize(typer, goal, in_new_goal->name_to_unfold);
        if (checkFlag(in->flags, AstFlag_Generated) &&
            equal(goal, norm_goal))
        {// superfluous auto-generated transforms.
          value = buildTerm(typer, in->body, goal).value;
          recursed = true;
        }
        else
        {
          eq_proof = newComputation_(goal, norm_goal);
          new_goal = norm_goal;
          rewrite_path = 0;
        }
      }
      else if ((new_goal = buildTerm(typer, in->new_goal, holev).value))
      {
        CompareTerms compare = compareTerms(arena, goal, new_goal);
        if (compare.result == Trinary_True)
        {
          reportError(in0, "new goal is exactly the same as current goal");
        }
        else if (compare.result == Trinary_False)
        {
          reportError(in0, "new goal is totally different from current goal");
        }
        else
        {
          rewrite_path = compare.diff_path;
          Term *from = subExpressionAtPath(goal, compare.diff_path);
          Term *to   = subExpressionAtPath(new_goal, compare.diff_path);

          HintDatabase *hints = 0;
          if (in->hint)
          {
            b32 is_global_identifier = false;
            if (Identifier *ident = castAst(in->hint, Identifier))
            {
              if (!lookupLocalName(typer, &ident->token))
              {
                if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
                {
                  is_global_identifier = true;
                  for (i32 i=0; i < slot->count; i++)
                  {
                    hints = addHint(temp_arena, hints, slot->items[i]);
                  }
                }
                else
                {
                  reportError(ident, "identifier not found");
                  attach("identifier", ident->token.string);
                }
              }
            }

            if (!is_global_identifier)
            {
              if ((eq_proof = buildTerm(typer, in->hint, holev).value))
              {
                hints = addHint(temp_arena, hints, eq_proof);
              }
            }
          }

          Term *lr_eq = newEquality(from, to);
          Term *rl_eq = newEquality(to, from);

          Solver solver = Solver{.typer=typer, .local_hints=hints, .use_global_hints=true};
          if (!(eq_proof = solveGoal(&solver, lr_eq)))
          {
            if ((eq_proof = solveGoal(&solver, rl_eq)))
            {
              right_to_left = true;
            }
            else
            {
              reportError(in0, "cannot solve for equality proof");
              attach("equality", lr_eq);
              attach("serial", serial);
            }
          }
        }
      }

      if (noError() && !recursed)
      {
        if (Term *body = buildTerm(typer, in->body, new_goal).value)
        {
          value = newRewrite(arena, eq_proof, body, rewrite_path, right_to_left);
        }
      }

      if (in->print_proof && eq_proof)
      {
        print(0, eq_proof);
        print(0, "\n");
      }
    } break;

    case Ast_Let:
    {
      Let  *in = castAst(in0, Let);
      Term *type_hint = holev;
      if (in->type && in->type->kind != Ast_NormalizeMeAst)
      {
        if (Term *type = buildTerm(typer, in->type, holev).value)
        {
          type_hint = type;
        }
      }
      if (noError())
      {
        if (Term *rhs = buildTerm(typer, in->rhs, type_hint).value)
        {
          Term *rhs_type = (type_hint->kind == Term_Hole) ? getType(rhs) : type_hint;

          if (in->type)
          {// type coercion
            if (NormalizeMeAst *in_type = castAst(in->type, NormalizeMeAst))
            {
              Term *norm_rhs_type = normalize(typer, rhs_type, in_type->name_to_unfold);
              if (checkFlag(in->flags, AstFlag_Generated) &&
                  equal(rhs_type, norm_rhs_type))
              {// superfluous auto-generated transforms.
                value = buildTerm(typer, in->body, goal).value;
                recursed = true;
              }
              else
              {
                Term *computation = newComputation_(norm_rhs_type, rhs_type);
                rhs_type = norm_rhs_type;
                rhs = newRewrite(arena, computation, rhs, 0, false);
              }
            }
          }

          if (!recursed)
          {
            value = buildWithNewAsset(typer, in->lhs, rhs, in->body, goal);
          }
        }
      }
    } break;

    case Ast_ForkAst:
    {// no need to return value since nobody uses the value of a fork
      ForkAst *fork = castAst(in0, ForkAst);
      value = buildFork(typer, fork, goal);
      recursed = true;
    } break;

    case Ast_CtorAst:
    {
      reportError(in0, "please use this constructor syntax as an operator");
    } break;

    case Ast_SeekAst:
    {
      SeekAst *in = castAst(in0, SeekAst);
      Term *proposition = goal;
      if (in->proposition)
      {
        proposition = buildTerm(typer, in->proposition, holev).value;
      }

      if (noError())
      {
        value = seekGoal(Solver{.typer=typer}, proposition);
        if (!value)
          reportError(in0, "cannot find a matching proof in scope");
      }
    } break;

    case Ast_OverloadAst:
    {
      OverloadAst *in = castAst(in0, OverloadAst);
      if (GlobalBinding *lookup = lookupGlobalName(&in->function_name))
      {
        if (Term *distinguisher = buildTerm(typer, in->distinguisher, holev).value)
        {
          value = getOverloadFromDistinguisher(lookup, distinguisher);
          if (!value)
            reportError(in0, "found no overload corresponding to distinguisher");
        }
      }
    } break;

    case Ast_TypedExpression:
    {
      TypedExpression *in = (TypedExpression *)(in0);
      if (Term *type = buildTerm(typer, in->type, holev).value)
      {
        value = buildTerm(typer, in->expression, type).value;
      }
    } break;

    case Ast_ReductioAst:
    {
      value = reductioAdAbsurdum(Solver{.typer=typer}, goal);
      if (!value)
        reportError(in0, "no contradiction found");
    } break;

    case Ast_ListAst:
    {
      ListAst *in = (ListAst *)in0;
      // auto [uni, uni_args] = castUnion(goal);
      // NOTE: The plan is to just lean on the typechecking as much as possible.
      Ast *tail = in->tail;
      if (!tail)
      {
        CompositeAst *nil = newAst(arena, CompositeAst, &in->token);
        nil->op = newSyntheticAst(rea.nil, &in->token);
        // NOTE: no arg: we let the typer infer it.
        tail = nil;
      }

      for (i32 i = in->count-1; i >= 0; i--)
      {
        Ast *item = in->items[i];
        CompositeAst *new_tail = newAst(arena, CompositeAst, &item->token);
        new_tail->op        = newSyntheticAst(rea.cons, &item->token);
        new_tail->arg_count = 2;
        new_tail->args      = pushArray(arena, 2, Ast *);
        new_tail->args[0]   = item;
        new_tail->args[1]   = tail;
        tail = new_tail;
      }

      recursed = true;
      value = buildTerm(typer, tail, goal);
    } break;

    case Ast_Invert:
    {
      Invert *in = (Invert *)in0;
      if (Term *pointer0 = buildTerm(typer, in->pointer, holev))
      {
        if (Pointer *pointer = castTerm(pointer0, Pointer))
        {
          if (pointer->ref)
          {
            auto [uni, uni_args] = castUnion(pointer->type);
            if (uni && uni_args)
            {
              Arrow *uni_signature = castTerm(uni->type, Arrow);
              Composite *ref_type = castTerm(pointer->ref->type, Composite);
              i32 poly_count = getPolyParamCount(uni_signature);

              i32 eq_count = uni_signature->param_count - poly_count;
              Term **eqs = pushArray(arena, eq_count, Term *);
              for (i32 i=0; i < eq_count; i++)
              {
                Term *uni_arg = uni_args[poly_count+i];
                Term *ref_arg = ref_type->args[poly_count+i];
                eqs[i] = newComputation_(uni_arg, ref_arg);
              }
              value = buildWithNewAssets(typer, eq_count, 0, eqs, in->body, goal);
              recursed = true;
            }
            else
            {
              reportError(in, "cannot invert this type");
            }
          }
          else
          {
            reportError(in, "variable has no constructor information");
          }
        }
        else
        {
          reportError(in, "invert only support pointers (since atm you can only fork pointers anyway, and this is mean to be used in a fork)");
        }
      }
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// typecheck if needed
    Term *actual = value->type;
    if (should_check_type && !recursed)
    {
      if (!matchType(actual, goal))
      {
        if (expectedWrongType(typer)) silentError();
        else
        {
          reportError(in0, "actual type differs from expected type");
          attach("got", actual);
          attach("serial", serial);
        }
      }
    }
  }

  if (InterpError *error = getError())
  {
    if (!hasSilentError())
    {
      if (!error->goal_attached)
      {
        error->goal_attached = true;
        attach("goal", goal);

        StartString start = startString(error_buffer);
        print(error_buffer, "\n");
        prettyPrint(error_buffer, typer->scope);
        attach("scope", endString(start));

        start = startString(error_buffer);
      }
    }
    value = 0;
  }
  else
  {
    assert(value);
  }
  return BuildTerm{.value=value};
}

internal Term *
buildGlobalTerm(Typer *typer, Ast *in0, Term *goal)
{
  Term *out = buildTerm(typer, in0, goal);
  if (out)
  {
    out = copyToGlobalArena(out);
  }
  return out;
}

forward_declare internal Term *
buildFork(Typer *typer, ForkAst *in, Term *goal)
{
  Arena *arena = temp_arena;
  if (goal->kind == Term_Hole)
  {
    reportError(in, "fork expressions require a goal, please provide one (f.ex instead of writing \"a := b\", write \"a: A := b\")");
  }
  Fork *out = newTerm(arena, Fork, goal);
  out->case_count = in->case_count;
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  if (Term *subject = buildTerm(typer, in->subject, holev).value)
  {
    out->subject = subject;
    Term *subject_type = subject->type;
    if (Union *uni = getUnionOrPolyUnion(subject_type))
    {
      Term **ordered_bodies = pushArray(arena, uni->ctor_count, Term *, true);

      // NOTE: For ux reason, we don't care if you have less cases, just
      // typecheck what we have.
      if (in->case_count > uni->ctor_count)
      {
        reportError("fork provides more cases than expected!");
      }

      for (i32 input_case_i = 0;
           input_case_i < in->case_count && noError();
           input_case_i++)
      {
        Token *ctor_name = in->ctors + input_case_i;

        i32 ctor_i = -1;
        if (equal(ctor_name, "auto"))
        {
          for (i32 i=0; i < in->case_count; i++)
          {
            if (!ordered_bodies[i])
            {
              ctor_i = i;
              break;
            }
          }
        }
        else
        {
          for (i32 i = 0; i < uni->ctor_count; i++)
          {
            if (equal(getConstructorName(uni, i), ctor_name->string))
            {
              ctor_i = i;
              break;
            }
          }
        }

        if (ctor_i != -1)
        {
          if (instantiate(subject, ctor_i))
          {
            if (ordered_bodies[ctor_i])
            {
              reportError(in->bodies[input_case_i], "fork case handled twice");
              attach("constructor", getConstructorName(uni, ctor_i));
            }
            else
            {
              typer->try_reductio = true;
              if (Term *body = buildTerm(typer, in->bodies[input_case_i], goal).value)
              {
                ordered_bodies[ctor_i] = body;
              }
            }
            uninstantiate(subject);
          }
          else
          {
            reportError(in->subject, "cannot fork this term");
          }
        }
        else
        {
          tokenError(ctor_name, "not a valid constructor");
          attach("union", uni);

          StartString ctor_names = startString(error_buffer);
          for (i32 id=0; id < uni->ctor_count; id++)
          {
            print(error_buffer, getConstructorName(uni, id));
            if (id != uni->ctor_count-1)
              print(error_buffer, ", ");
          }
          attach("valid constructors", endString(ctor_names));
        }
      }

      out->bodies = ordered_bodies;

      if (noError() && in->case_count != uni->ctor_count)
      {
        reportError(in, "wrong number of cases, expected: %d, got: %d",
                    uni->ctor_count, in->case_count);
      }
    }
    else
    {
      reportError(in->subject, "cannot fork expression of this type");
      attach("type", subject_type);
    }
  }
  if (noError())
  {
    for (i32 id=0; id < in->case_count; id++)
      assert(in->bodies[id]);
  }
  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare inline Term *
newRewrite(Arena *arena, Term *eq_proof, Term *body, TreePath *path, b32 right_to_left)
{
  auto [lhs, rhs] = getEqualitySides(eq_proof->type);
  Term *from = right_to_left ? lhs : rhs;
  Term *to   = right_to_left ? rhs : lhs;
  Term *type = rewriteTerm(arena, from, to, path, body->type);

  Rewrite *out = newTerm(arena, Rewrite, type);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return out;
}

inline Term *
parseAndBuildTemp(Typer *typer, Term *expected_type=holev)
{
  Term *out = 0;
  if (Ast *ast = parseExpression())
  {
    out  = buildTerm(typer, ast, expected_type);
  }
  return out;
}

inline Term *
parseAndBuildGlobal(Typer *typer, Term *expected_type=holev)
{
  Term *out = 0;
  if (Ast *ast = parseExpression())
  {
    out = buildTerm(typer, ast, expected_type);
    out = copyToGlobalArena(out);
  }
  return out;
}

struct NormList {
  i32          count;
  Identifier **items;
};

// todo No need to normalize a fork if that fork contains other forks inside.
inline void
insertAutoNormalizations(Arena *arena, NormList norm_list, Ast *in0)
{
  switch (in0->kind)
  {
    case Ast_ForkAst:
    {
      ForkAst *in = castAst(in0, ForkAst);
      for (i32 case_id=0; case_id < in->case_count; case_id++)
      {
        Ast *body = in->bodies[case_id];
        insertAutoNormalizations(arena, norm_list, body);
        for (i32 norm_id=0; norm_id < norm_list.count; norm_id++)
        {
          Identifier *item = norm_list.items[norm_id];
          // todo cleanup: we'll need to clean useless let-normalization too!
          Let *new_body = newAst(arena, Let, &item->token);
          new_body->lhs   = item->token.string;
          new_body->rhs   = item;
          new_body->type  = newAst(arena, NormalizeMeAst, &item->token);
          new_body->body  = body;
          setFlag(&new_body->flags, AstFlag_Generated);
          body = new_body;
        }
        GoalTransform *new_body = newAst(arena, GoalTransform, &body->token);
        new_body->new_goal = newAst(arena, NormalizeMeAst, &body->token);
        setFlag(&new_body->flags, AstFlag_Generated);
        new_body->body = body;
        in->bodies[case_id] = new_body;
      }
    } break;

    case Ast_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      assert(in->body);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    case Ast_Let:
    {
      Let *in = castAst(in0, Let);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    default:
    {} break;
  }
}

internal FunctionAst *
parseGlobalFunction(Arena *arena, Token *name, b32 is_theorem)
{
  FunctionAst *out = newAst(arena, FunctionAst, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpression())
  {
    NormList norm_list = {};
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      while (true)
      {
        // todo #speed calling "optionalKind" repeatedly is slow
        if (optionalDirective("norm"))
        {
          pushContext("auto normalization: #norm(IDENTIFIER...)");
          if (requireChar('('))
          {
            norm_list.items = pushArray(temp_arena, DEFAULT_MAX_LIST_LENGTH, Identifier*);
            for (; noError(); )
            {
              if (optionalChar(')'))
                break;
              else if (requireIdentifier("expect auto-normalized parameter"))
              {
                // todo handle unbound identifier: all names in the norm list
                // should be in the function signature.
                Token *name = lastToken();
                i32 norm_i = norm_list.count++;
                assert(norm_i < DEFAULT_MAX_LIST_LENGTH);
                norm_list.items[norm_i] = newAst(arena, Identifier, name);
                if (!optionalChar(','))
                {
                  requireChar(')');
                  break;
                }
              }
            }
          }
          popContext();
        }
        else if (optionalDirective("hint"))
        {
          setFlag(&out->function_flags, FunctionFlag_is_global_hint);
        }
        else if (optionalDirective("no_apply"))
        {
          // todo: we can automatically infer this!
          setFlag(&out->function_flags, FunctionFlag_no_apply);
        }
        else if (optionalDirective("no_print_as_binop"))
        {
          setFlag(&out->function_flags, FunctionFlag_no_print_as_binop);
        }
        else if (optionalDirective("expand"))
        {
          setFlag(&out->function_flags, FunctionFlag_expand);
        }
        else if (optionalDirective("builtin"))
        {
          setFlag(&out->flags, AstFlag_is_builtin);
        }
        else
          break;
      }

      if (Ast *body = parseSequence())
      {
        if (is_theorem)
        {
          insertAutoNormalizations(arena, norm_list, body);
        }
        out->body      = body;
        out->signature = signature;
      }
    }
    else
      reportError(signature0, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare internal Ast *
parseFork()
{
  ForkAst *out = 0;
  Arena *arena = parse_arena;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpression();
  if (requireChar('{', "to open the typedef body"))
  {
    Token *ctors = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Token);
    Ast **bodies = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Ast*);

    i32 actual_case_count = 0;
    for (b32 stop = false;
         !stop && hasMore();)
    {
      if (optionalChar('}'))
        stop = true;
      else
      {
        pushContext("fork case: CASE: BODY");
        i32 input_case_i = actual_case_count++;
        Token ctor = nextToken();
        if (isIdentifier(&ctor))
          ctors[input_case_i] = ctor;
        else
          tokenError(&ctor, "expected a constructor name");

        optionalChar(':');  // just decoration
        if (Ast *body = parseSequence(false))
        {
          bodies[input_case_i] = body;
          if (!optionalChar(','))
          {
            requireChar('}', "to end fork expression; or use ',' to end the fork case");
            stop = true;
          }
        }
        popContext();
      }
    }

    if (noError())
    {
      out = newAst(arena, ForkAst, &token);
      out->token    = token;
      out->subject    = subject;
      out->case_count = actual_case_count;
      out->bodies     = bodies;
      out->ctors      = ctors;
    }
  }

  return out;
}

internal ArrowAst *
parseArrowType(Arena *arena, b32 is_struct)
{
  ArrowAst *out = 0;
  i32      param_count = 0;
  String  *param_names;
  Ast    **param_types;
  u32     *param_flags;
  Token marking_token = peekToken();
  char begin_arg_char = '(';
  char end_arg_char   = ')';
  if (requireChar(begin_arg_char))
  {
    // :arrow-copy-done-later
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_names, true);
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_flags, true);
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_types, true);

    i32 typeless_run = 0;
    Token typeless_token;
    for (b32 stop = false;
         !stop && hasMore();
         )
    {
      if (optionalChar(end_arg_char))
        stop = true;
      else
      {
        i32 param_i = param_count++;
        assert(param_i < DEFAULT_MAX_LIST_LENGTH);

        if (optionalDirective("unused"))
        {
          setFlag(&param_flags[param_i], ParameterFlag_Unused);
        }
        if (optionalChar('$'))
        {
          setFlag(&param_flags[param_i], ParameterFlag_Inferred);
          if (optionalChar('$'))
          {
            setFlag(&param_flags[param_i], ParameterFlag_Poly);
          }
        }

        Tokenizer tk_save = *global_tokenizer;
        String param_name = {};
        Token maybe_param_name_token = nextToken();
        if (isIdentifier(&maybe_param_name_token))
        {
          Token after_name = peekToken();
          if (equal(&after_name, ':'))
          {
            eatToken();
            param_name = maybe_param_name_token.string;
            pushContext("parameter type");
            if (Ast *param_type = parseExpression())
            {
              param_types[param_i] = param_type;
              if (typeless_run)
              {
                for (i32 offset = 1; offset <= typeless_run; offset++)
                {
                  param_types[param_i - offset] = param_type;
                }
                typeless_run = 0;
              }
            }
            popContext();
          }
          else if (equal(&after_name, ','))
          {
            param_name = maybe_param_name_token.string;
            typeless_run++;
            typeless_token = maybe_param_name_token;
          }
        }

        if (param_name.chars)
        {
          param_names[param_i] = param_name;
        }
        else
        {
          *global_tokenizer = tk_save;
          pushContext("anonymous parameter");
          Token anonymous_parameter_token = global_tokenizer->last_token;
          if (Ast *param_type = parseExpression())
          {
            param_types[param_i] = param_type;
            if (typeless_run)
            {
              tokenError(&anonymous_parameter_token, "cannot follow a typeless parameter with an anonymous parameter");
            }
          }
          popContext();
        }

        if (hasMore())
        {
          Token delimiter = nextToken();
          if (equal(&delimiter, end_arg_char))
            stop = true;
          else if (!equal(&delimiter, ','))
            tokenError("unexpected token");
        }
      }
    }

    if (noError())
    {
      if (typeless_run)
      {
        tokenError(&typeless_token, "please provide types for all parameters");
      }
    }
  }

  if (noError())
  {
    out = newAst(arena, ArrowAst, &marking_token);
    out->param_count = param_count;
    out->param_names = param_names;
    out->param_types = param_types;
    out->param_flags = param_flags;

    if (optionalKind(Token_Arrow))
    {
      if (Ast *return_type = parseExpression())
        out->output_type = return_type;
    }
    else if (!is_struct)  // structs don't need return type
    {
      reportError("non-struct arrow types require an output type");
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline b32
areSequential(Token *first, Token *next)
{
  return next->string.chars == first->string.chars + first->string.length;
}

inline b32
eitherOrChar(char optional, char require)
{
  b32 out = false;
  if (!optionalChar(optional))
  {
    out = requireChar(require);
  }
  return out;
}

internal UnionAst *
parseUnion(Arena *arena, Token *uni_name)
{
  UnionAst *uni = newAst(arena, UnionAst, uni_name);

  i32 uni_param_count = 0;
  i32 poly_count      = 0;
  i32 non_poly_count  = 0;
  if (peekChar() == ('('))
  {
    if ((uni->signature = parseArrowType(arena, true)))
    {
      if (uni->signature->output_type)
      {
        reportError(uni->signature->output_type, "didn't expect an output type");
      }
      else
      {
        uni->signature->output_type = newSyntheticAst(rea.Type, uni_name);
        uni_param_count = uni->signature->param_count;
        poly_count      = getPolyParamCount(uni->signature);
        non_poly_count  = uni_param_count - poly_count;
      }
    }
  }

  if (optionalDirective("builtin"))
  {
    setFlag(&uni->flags, AstFlag_is_builtin);
  }

  if (requireChar('{'))
  {
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, uni->ctor_signatures);
    if (uni_name)
    {
      allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, uni->ctor_names);
    }

    Ast *auto_ctor_output_type = 0;
    if (!non_poly_count)
    {
      if (poly_count)
      {
        CompositeAst *output_type = newAst(arena, CompositeAst, uni_name);
        output_type->arg_count = uni_param_count;
        allocateArray(arena, uni_param_count, output_type->args);
        for (i32 i=0; i < uni_param_count; i++)
        {
          // we got rid of the param token, so now we gotta make one up...
          Token token = newToken(uni->signature->param_names[i]);
          output_type->args[i] = newAst(arena, Identifier, &token);
        }
        output_type->op = newAst(arena, Identifier, uni_name);
        auto_ctor_output_type = output_type;
      }
      else
      {
        auto_ctor_output_type = newAst(arena, Identifier, uni_name);
      }
    }

    for (b32 stop=false; noError() && !stop; )
    {
      if (optionalChar('}')) stop=true;
      else
      {
        i32 ctor_i = uni->ctor_count++;
        Token ctor_name = nextToken();
        uni->ctor_names[ctor_i] = ctor_name;
        if (isIdentifier(&ctor_name))
        {
          ArrowAst *sig = 0;
          if (peekChar() == '(')
          {// composite constructor
            sig = uni->ctor_signatures[ctor_i] = parseArrowType(arena, true);
          }
          else
          {// atomic constructor
            sig = newAst(arena, ArrowAst, &ctor_name);
            uni->ctor_signatures[ctor_i] = sig;
            allocateArray(arena, poly_count, sig->param_names);
            allocateArray(arena, poly_count, sig->param_types);
            allocateArray(arena, poly_count, sig->param_flags);
          }

          if (noError())
          {
            // modification to add poly variables
            assert((sig->param_count + poly_count) < DEFAULT_MAX_LIST_LENGTH);
            for (i32 i = sig->param_count-1; i >= 0; i--)
            {
              sig->param_names[i+poly_count] = sig->param_names[i];
              sig->param_types[i+poly_count] = sig->param_types[i];
              sig->param_flags[i+poly_count] = sig->param_flags[i];
            }
            for (i32 i=0; i < poly_count; i++)
            {
              sig->param_names[i] = uni->signature->param_names[i];
              sig->param_types[i] = uni->signature->param_types[i];
              sig->param_flags[i] = uni->signature->param_flags[i];
            }
            sig->param_count += poly_count;

            // modification to add output type
            if (auto_ctor_output_type)
            {
              if (sig->output_type)
              {
                reportError(sig->output_type, "did not expect output type");
              }
              else
              {
                sig->output_type = auto_ctor_output_type;
              }
            }
            else if (!sig->output_type)
            {
              reportError(sig, "output type required since there are non-poly parameters");
            }
          }
        }
        else
        {
          tokenError("expected an identifier as constructor name");
        }

        stop = eitherOrChar(',', '}');
      }
    }
  }
  
  return uni;
}

internal void
addBuiltinTerm(Term *term)
{
  String builtin_name = term->global_name->string;
  b32 installed = false;
  for (i32 i=0;
       !installed && i < arrayCount(rea_builtin_names);
       i++)
  {
    BuiltinEntry entry = rea_builtin_names[i];
    if (equal(builtin_name, entry.name))
    {
      installed = true;
      *entry.term = term;
    }
  }
}

forward_declare internal Term *
buildUnion(Typer *typer, UnionAst *in, Token *global_name)
{
  assert(global_name);
  Arena *arena = global_state.top_level_arena;
  Union *uni = newTerm(arena, Union, rea.Type);
  b32 UNUSED_VAR serial = DEBUG_SERIAL++;
  if (serial == 2815)
    breakhere;

  i32 ctor_count = in->ctor_count;
  uni->ctor_count = ctor_count;
  Arrow **ctor_signatures = pushArray(temp_arena, ctor_count, Arrow *);
  uni->constructors = pushArray(arena, ctor_count, Constructor *);

  Arrow *uni_signature  = 0;
  i32    poly_count     = 0;
  i32    non_poly_count = 0;
  if (in->signature)
  {
    if (Term *uni_params0 = buildGlobalTerm(typer, in->signature, holev))
    {
      uni_signature              = castTerm(uni_params0, Arrow);
      uni_signature->output_type = rea.Type;
      uni->type = uni_signature;
      poly_count     = getPolyParamCount(uni_signature);
      non_poly_count = uni_signature->param_count - poly_count;
    }
  }

  if (noError())
  {
    // NOTE: bind the name first to support recursive data structure.
    addGlobalBinding(global_name, uni);

    for (i32 ctor_i=0; noError() && ctor_i < ctor_count; ctor_i++)
    {
      Ast *ast_sig = in->ctor_signatures[ctor_i];
      if (Term *sig0 = buildGlobalTerm(typer, ast_sig, holev))
      {
        Arrow *sig = ctor_signatures[ctor_i] = castTerm(sig0, Arrow);
        assert(sig);

        if (uni_signature && non_poly_count)
        {
          b32 valid_output = false;
          if (Composite *output_type = castTerm(sig->output_type, Composite))
          {
            if (Union *output_uni = castTerm(output_type->op, Union))
            {
              if (output_uni == uni)
              {
                valid_output = true;
                for (i32 poly_i=0; poly_i < poly_count; poly_i++)
                {
                  if (Variable *var = castTerm(output_type->args[poly_i], Variable))
                  {
                    b32 correct_var = (var->delta == 0 && var->index == poly_i);
                    if (!correct_var)
                    {
                      valid_output = false;
                    }
                  }
                }
              }
            }
          }
          if (!valid_output)
          {
            reportError(ast_sig, "constructor has to return the same union as the one being defined");
            attach("output_type", sig->output_type);
          }
        }
      }
    }
  }

  if (noError())
  {
    if (uni_signature)
    {
      for (i32 ctor_i=0; noError() && ctor_i < ctor_count; ctor_i++)
      {
        Arrow *ctor_sig = ctor_signatures[ctor_i];
        Constructor *ctor = newTerm(arena, Constructor, ctor_sig);
        ctor->index = ctor_i;
        ctor->name  = in->ctor_names[ctor_i];
        addGlobalBinding(&in->ctor_names[ctor_i], ctor);
        uni->constructors[ctor_i] = ctor;
      }
    }
    else
    {
      // no union parameters
      for (i32 ctor_i=0; noError() && ctor_i < ctor_count; ctor_i++)
      {
        Arrow *struc = ctor_signatures[ctor_i];
        struc->output_type = uni;
        Constructor *ctor = newTerm(arena, Constructor, struc);
        ctor->index = ctor_i;
        ctor->name  = in->ctor_names[ctor_i];

        Term *term_to_bind = ctor;
        if (struc->param_count == 0)
        {
          // todo: need to rethink "no-arg composite" thing
          term_to_bind = newComposite(arena, ctor, 0, 0);
        }
        addGlobalBinding(&in->ctor_names[ctor_i], term_to_bind);
        uni->constructors[ctor_i] = ctor;
      }
    }
  }

  b32 is_builtin = checkFlag(in->flags, AstFlag_is_builtin);
  if (is_builtin && noError())
  {
    addBuiltinTerm(uni);
    for (i32 i=0; i < uni->ctor_count; i++)
    {
      addBuiltinTerm(uni->constructors[i]);
    }
  }

  NULL_WHEN_ERROR(uni);
  return uni;
}

inline CtorAst *
parseCtorAst(Arena *arena)
{
  CtorAst *out = newAst(arena, CtorAst, &global_tokenizer->last_token);
  if (requireChar('['))
  {
    out->ctor_i = parseInt32();
    requireChar(']');
  }
  return out;
}

inline SeekAst *
parseSeek(Arena *arena)
{
  SeekAst *seek = newAst(arena, SeekAst, &global_tokenizer->last_token);
  if (!seesExpressionEndMarker())
  {
    seek->proposition = parseExpression();
  }
  return seek;
}

inline Ast *
parseOverload(Arena *arena)
{
  OverloadAst *out = newAst(arena, OverloadAst, lastToken());
  if (requireChar('('))
  {
    if (requireIdentifier("require a function name"))
    {
      out->function_name = *lastToken();
      if (requireChar(','))
      {
        out->distinguisher = parseExpression();
      }
    }
    requireChar(')');
  }
  if (hasError()) out = 0;
  return out;
}

internal Ast *
parseFunctionExpression(Arena *arena)
{
  // cutnpaste from "parseGlobalFunction"
  FunctionAst *out = newAst(arena, FunctionAst, lastToken());

  ArrowAst *signature = 0;
  if (peekChar() == '{')
  {
    // inferred signature.
  }
  else
  {
    signature = parseArrowType(arena, false);
  }

  if (noError())
  {
    if (Ast *body = parseSequence())
    {
      out->body      = body;
      out->signature = signature;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

internal Ast *
parseList(Arena *arena)
{
  ListAst *out = 0;
  // :list-opening-brace-eaten
  Token *first_token = lastToken();
  i32 count = 0;
  Ast **items = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Ast*);
  char closing = ']';
  Ast *tail = 0;
  for (; noError(); )
  {
    if (optionalChar(closing))
      break;

    items[count++] = parseExpression();

    if (!optionalChar(','))
    {
      if (optionalKind(Token_DoubleDot))
      {
        tail = parseExpression();
      }
      requireChar(closing);
      break;
    }
  }
  if (noError())
  {
    out = newAst(arena, ListAst, first_token);
    out->count = count;
    out->items = items;
    out->tail  = tail;
  }
  return out;
}

internal Ast *
parseOperand()
{
  Ast *operand = 0;
  Token token = nextToken();
  Arena *arena = parse_arena;
  switch (token.kind)
  {
    case '_':
    {
      operand = newAst(arena, Hole, &token);
    } break;

    case '(':
    {
      operand = parseExpression();
      requireChar(')');
    } break;

    case '[':
    {// :list-opening-brace-eaten
      operand = parseList(arena);
    } break;

    case Token_Keyword_fn:
    {
      operand = parseFunctionExpression(arena);
    } break;

    case Token_Keyword_prove:
    {
      Ast *type = 0;
      
      if (peekChar() != '{')
      {
        type = parseExpression();
      }
      if (noError())
      {
        if (Ast *expression = parseSequence(true))
        {
          if (type)
          {
            TypedExpression *typed = newAst(arena, TypedExpression, &type->token);
            typed->type       = type;
            typed->expression = expression;
            operand = typed;
          }
          else
            operand = expression;
        }
      }
    } break;

    case Token_Alphanumeric:
    case Token_Special:
    {
      operand = newAst(arena, Identifier, &token);
    } break;

    case Token_Keyword_union:
    {
      reportError(&token, "anonymous union deprecated");
    } break;

    case Token_Keyword_ctor:
    {
      operand = parseCtorAst(arena);
    } break;

    case Token_Keyword_seek:
    {
      operand = parseSeek(arena);
    } break;

    case Token_Keyword_overload:
    {
      operand = parseOverload(arena);
    } break;

    default:
    {
      tokenError("expected start of expression");
    }
  }

  while (hasMore())
  {
    if (optionalChar('('))
    {// function call syntax, let's keep going
      Ast *op = operand;
      Ast **args = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Ast*);
      CompositeAst *new_operand = newAst(arena, CompositeAst, &op->token);
      new_operand->op        = op;
      new_operand->arg_count = 0;
      new_operand->args      = args;
      operand = new_operand;
      while (hasMore())
      {
        if (optionalChar(')'))
          break;
        else
        {
          i32 arg_i = new_operand->arg_count++;
          if (optionalKind(Token_Ellipsis))
          {
            if (arg_i == 0)
              args[0] = newAst(arena, Ellipsis, &global_tokenizer->last_token);
            else
              reportError("ellipsis must be the only argument");

            requireChar(')', "ellipsis must be the only argument");
            break;
          }
          else
          {
            if ((args[arg_i] = parseExpression()))
            {
              if (!optionalChar(','))
              {
                requireChar(')', "expected ',' or ')'");
                break;
              }
            }
          }
        }
      }
    }
    else if (optionalChar('.'))
    {// member accessor
      AccessorAst *accessor = newAst(arena, AccessorAst, &global_tokenizer->last_token);
      accessor->record      = operand;
      if (requireIdentifier("expected identifier as field name"))
      {
        accessor->field_name = *lastToken();
        operand              = &accessor->a;
      }
    }
    else break;
  }
  NULL_WHEN_ERROR(operand);
  return operand;
}

inline b32
seesArrowExpression()
{
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (equal(nextToken(tk), '('))
    if (eatUntilMatchingPair(tk))
      out = (nextToken(tk).kind == Token_Arrow);
  return out;
}

internal Ast *
parseExpression_(ParseExpressionOptions opt)
{
  Arena *arena = parse_arena;
  Ast *out = 0;
  if (seesArrowExpression())
  {
    // todo Arrow could just be an operand maybe?
    out = parseArrowType(arena, false);
  }
  else if (Ast *operand = parseOperand())
  {
    // (a+b) * c
    //     ^
    for (b32 stop = false; !stop && hasMore();)
    {
      Token op_token = peekToken();
      if (isIdentifier(&op_token))
      {// infix operator syntax
        // (a+b) * c
        //        ^
        Identifier *op = newAst(arena, Identifier, &op_token);
        i32 precedence = precedenceOf(op_token.string);
        if (precedence >= opt.min_precedence)
        {
          // recurse
          nextToken();
          // a + b * c
          //      ^
          ParseExpressionOptions opt1 = opt;
          opt1.min_precedence = precedence;
          if (Ast *recurse = parseExpression_(opt1))
          {
            i32 arg_count = 2;
            Ast **args    = pushArray(arena, arg_count, Ast*);
            args[0] = operand;
            args[1] = recurse;

            CompositeAst *new_operand = newAst(arena, CompositeAst, &op_token);
            new_operand->op        = op;
            new_operand->arg_count = arg_count;
            new_operand->args      = args;
            operand = new_operand;
          }
        }
        else
        {
          // we are pulled to the left
          // a * b + c
          //      ^
          stop = true;
        }
      }
      else if (isExpressionEndMarker(&op_token))
      {
        stop = true;
      }
      else
      {
        tokenError(&op_token, "expected operator token");
      }
    }
    if (noError())
      out = operand;
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare inline Ast *
parseExpression()
{
  return parseExpression_(ParseExpressionOptions{});
}

inline void
addGlobalHint(Function *fun)
{
  HintDatabase *new_hint = pushStruct(global_state.top_level_arena, HintDatabase);
  new_hint->head = fun;
  new_hint->tail = global_state.hints;
  global_state.hints = new_hint;
}

internal Function *
buildGlobalFunction(Typer *typer, FunctionAst *in)
{
  i32 unused_var serial = DEBUG_SERIAL;
  pushContext(in->token.string, true);
  Function *out = 0;
  if (Term *type = buildTerm(typer, in->signature, holev))
  {
    type = copyToGlobalArena(type);
    if (Arrow *signature = castTerm(type, Arrow))
    {
      out = buildFunctionGivenSignature(typer, signature, in->body,
                                        in->function_flags, &in->token);
      if (out)
      {
        // :persistent-global-function
        if (checkFlag(in->function_flags, FunctionFlag_is_global_hint))
        {
          addGlobalHint(out);
        }
        if (checkFlag(in->flags, AstFlag_is_builtin))
        {
          addBuiltinTerm(out);
        }
      }
    }
    else
    {
      reportError(in->signature, "function signature is required to be an arrow type");
    }
  }

  popContext();
  return out;
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  Arena *arena = state->top_level_arena;
  b32 should_fail_active = false;

  Token token_ = nextToken(); 
  Token *token = &token_;

  while (hasMore())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
    error_buffer_ = subArena(temp_arena, 2048);
#endif

    // NOTE: We don't wanna persist the typer across top-level forms, even if it
    // happens to work.
    Typer  typer_ = {};
    Typer *typer  = &typer_;
    if (should_fail_active)
    {
      setFlag(&typer->expected_errors, Error_WrongType);
    }

    switch (token_.kind)
    {
      case Token_Directive:
      {
        if (equal(token->string, "load"))
        {
          pushContext("load");
          Token file = nextToken();
          if (file.kind != Token_StringLiteral)
            tokenError("expect \"FILENAME\"");
          else
          {
            String load_path = print(arena, global_tokenizer->directory);
            load_path.length += print(arena, file.string).length;
            arena->used++;

            // note: this could be made more efficient but we don't care.
            FilePath full_path = platformGetFileFullPath(arena, load_path.chars);

            b32 already_loaded = false;
            for (auto file_list = state->file_list;
                 file_list && !already_loaded;
                 file_list = file_list->tail)
            {
              if (equal(file_list->head_path, load_path))
                already_loaded = true;
            }

            if (!already_loaded)
            {
              auto interp_result = interpretFile(state, full_path, false);
              if (!interp_result)
                tokenError("failed loading file");
            }
          }
          popContext();
        }
        else if (equal(token->string, "primitive"))
        {
          if (requireIdentifier())
          {
            String global_name = lastToken()->string;
            String primitive_name = global_name;
            if (optionalString("as"))
            {
              if (requireIdentifier())
              {
                primitive_name = lastToken()->string;
              }
            }

            if (requireChar(':'))
            {
              if (Term *primitive_type = parseAndBuildGlobal(typer))
              {
                b32 installed = false;
                for (i32 i=0;
                     !installed && i < arrayCount(rea_builtin_names);
                     i++)
                {
                  BuiltinEntry entry = rea_builtin_names[i];
                  if (equal(primitive_name, entry.name))
                  {
                    installed = true;
                    *entry.term = newTerm(arena, Primitive, primitive_type);
                    addBuiltinGlobalBinding(global_name, *entry.term);
                  }
                }
                // assert(installed);
              }
            }
          }
        }
        else if (equal(token->string, "print"))
        {
          if (optionalString("all_args"))
          {
            print_all_args = !optionalString("off");
          }
          else if (optionalString("var_delta"))
          {
            print_var_delta = !optionalString("off");
          }
          else if (optionalString("var_index"))
          {
            print_var_index = !optionalString("off");
          }
        }
        else if (equal(token->string, "should_fail"))
        {
          if (optionalString("off"))
          {
            should_fail_active = false;
          }
          else
          {
            should_fail_active = true;
            silentError();  // #hack just a signal to skip this form
          }
        }
        else if (equal(token->string, "debug"))
        {
          b32 value = !optionalString("off");
          global_state.top_level_debug_mode = value;
          print_var_delta                   = value;
        }
      } break;

      case Token_Keyword_test_eval:
      {
        if (Term *expr = parseAndBuildTemp(typer))
        {
          normalize(typer, expr);
        }
      } break;

      case Token_Keyword_print:
      {
        u32 flags = PrintFlag_Detailed;
        if (optionalString("lock_detailed"))
        {
          setFlag(&flags, PrintFlag_LockDetailed);
        }
        if (Term *expr = parseAndBuildTemp(typer))
        {
          Term *norm = normalize(0, expr);
          print(0, norm, {.flags=flags, .print_type_depth=1});
          print(0, "\n");
        }
      } break;

      case Token_Keyword_print_raw:
      {
        if (Term *parsing = parseAndBuildTemp(typer))
          print(0, parsing, {.flags = PrintFlag_Detailed|PrintFlag_LockDetailed,
                             .print_type_depth = 1});
        print(0, "\n");
      } break;

      case Token_Keyword_print_ast:
      {
        if (Ast *exp = parseExpression())
          print(0, exp, {.flags = PrintFlag_Detailed});
        print(0, "\n");
      } break;

      case Token_Keyword_check:
      {
        pushContext("check TERM: TYPE");
        Term *expected_type = holev;
        if (Ast *ast = parseExpression())
        {
          if (optionalChar(':'))
          {
            if (Term *type = parseAndBuildTemp(typer))
            {
              expected_type = type;
            }
          }
          if (noError())
          {
            buildTerm(typer, ast, expected_type);
          }
        }
        popContext();
      } break;

      case Token_Keyword_check_truth:
      {
        if (Term *goal = parseAndBuildTemp(typer))
        {
          b32 goal_valid = false;
          if (Composite *eq = castTerm(goal, Composite))
          {
            if (eq->op == rea.equal)
            {
              goal_valid = true;
              Term *lhs = normalize(typer, eq->args[1]);
              Term *rhs = normalize(typer, eq->args[2]);
              if (!equal(lhs, rhs))
              {
                tokenError(token, "equality cannot be proven by computation");
                Term *lhs = normalize(typer, eq->args[1]);
                attach("lhs", lhs);
                attach("rhs", rhs);
              }
            }
          }
          if (!goal_valid)
          {
            tokenError(token, "computation can only prove equality");
            attach("got", goal);
          }
        }
      } break;

      case Token_Keyword_algebra_declare:
      {
        if (Term *type = parseAndBuildGlobal(typer))
        {
          AlgebraDatabase *new_algebras = pushStruct(global_state.top_level_arena, AlgebraDatabase);
          new_algebras->tail            = global_state.algebras;
          global_state.algebras = new_algebras;

          Algebra *algebra = &new_algebras->head;
          algebra->type = type;
          const i32 function_count = 7;
          const char *function_names[function_count] = {
            "+", "addCommutative", "addAssociative",
            "*", "mulCommutative", "mulAssociative",
            "mulDistributive",
          };
          Term **functions[function_count] = {
            &algebra->add, &algebra->addCommutative, &algebra->addAssociative,
            &algebra->mul, &algebra->mulCommutative, &algebra->mulAssociative,
            &algebra->mulDistributive,
          };

          for (i32 i=0; i < function_count && noError(); i++)
          {
            if (Term *function = getOverloadFromDistinguisher(token, function_names[i], type))
              *functions[i] = function;
          }
        }
      } break;

      default:
      {
        if (isIdentifier(token))
        {
          Token after_name = nextToken();
          if (isIdentifier(&after_name) &&
              areSequential(token, &after_name))
          {// token combination
            token_.string.length += after_name.string.length;
            after_name = nextToken();
          }

          switch (after_name.kind)
          {
            case Token_ColonEqual:
            {
              pushContext("constant definition: CONSTANT := VALUE;");
              if (Term *rhs = parseAndBuildGlobal(typer))
              {
                addGlobalBinding(token, rhs);
              }
              popContext();
            } break;

            case Token_DoubleColon:
            {
              Token after_dcolon = peekToken();
              if (after_dcolon.kind == Token_Keyword_union)
              {
                nextToken();
                if (UnionAst *ast = parseUnion(arena, token))
                {
                  buildUnion(typer, ast, token);
                }
              }
              else
              {
                b32 is_theorem;
                if (after_dcolon.kind == Token_Keyword_fn)
                {
                  is_theorem = false;
                  nextToken();
                }
                else is_theorem = true;
                if (FunctionAst *fun = parseGlobalFunction(arena, token, is_theorem))
                {
                  buildGlobalFunction(typer, fun);
                }
              }
            } break;

            case ':':
            {
              if (Term *type = parseAndBuildGlobal(typer))
              {
                if (requireKind(Token_ColonEqual, "require :=, syntax: name : type := value"))
                {
                  if (Term *rhs = parseAndBuildGlobal(typer, type))
                  {
                    addGlobalBinding(token, rhs);
                  }
                }
              }
            } break;

            default:
            {
              tokenError("unexpected token after identifier");
            } break;
          }
        }
        else tokenError("unexpected token to begin top-level form");
      } break;
    }

#if CLEAN_TEMPORARY_MEMORY
    endTemporaryMemory(top_level_temp);
#endif

    if (should_fail_active)
    {
      if (noError())
      {
        tokenError(token, "#should_fail active but didn't fail");
      }
      else if (hasSilentError())
      {
        wipeError();
      }
    }

    if (hasMore())
    {
      token_ = nextToken();
      while (equal(token_.string, ";"))
      {// todo: should we do "eat all semicolons after the first one?"
        token_ = nextToken();
      }
    }
  }
}

forward_declare internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  Arena *arena = state->top_level_arena;
  b32 success = true;
#define REA_PROFILE 0
#if REA_PROFILE
  auto begin_time = platformGetWallClock(arena);
#endif

  ReadFileResult read = platformReadEntireFile(input_path.path);
  if (read.content)
  {
    auto new_file_list          = pushStruct(arena, FileList);
    new_file_list->head_path    = input_path.path;
    new_file_list->head_content = read.content;
    new_file_list->tail         = state->file_list;
    state->file_list            = new_file_list;

    Tokenizer  tk_ = newTokenizer(read.content, input_path.directory);
    Tokenizer *tk  = &tk_;

    Tokenizer *old_tokenizer = global_tokenizer;
    global_tokenizer         = tk;

    parseTopLevel(state);
    if (InterpError *error = tk->error)
    {
      success = false;
      printf("%s:%d:%d: ", input_path.path, error->line, error->column);
      if (error->context)
      {
        print(0, "[");
        for (InterpContext *context = error->context;
             context;
             context=context->next)
        {
          if (context->is_important || !context->next)
          {
            print(0, context->first);
            if (context->next)
              print(0, " / ");
          }
        }
        print(0, "] ");
      }
      print(0, error->message);

      if (error->attachment_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attachment_count;
             attached_id++)
        {
          auto attachment = error->attachments[attached_id];
          print(0, "%s: ", attachment.key);
          print(0, attachment.value);
          if (attached_id != error->attachment_count-1) 
            printf("\n");
        }
      }
      printf("\n");
    }

    if (is_root_file)
    {
#if REA_PROFILE
      auto compile_time = platformGetSecondsElapsed(begin_time, platformGetWallClock(arena));
      printf("Compile time for file %s: %fs\n", input_path.file, compile_time);
#endif
    }

    global_tokenizer = old_tokenizer;
  }
  else
  {
    if (is_root_file)
      printf("Failed to read input file %s\n", input_path.file);
    success = false;
  }

  if (is_root_file)
    checkArena(temp_arena);

  fflush(stdout);
  return success;
}

internal b32
beginInterpreterSession(Arena *top_level_arena, FilePath input_path)
{
  // :global_state_cleared_at_startup Clear global state as we might run the
  // interpreter multiple times.
  auto arena = top_level_arena;
  global_state       = {};
  global_state.top_level_arena = arena;

  global_state.bindings = pushStruct(arena, GlobalBindings);  // :global-bindings-zero-at-startup because // :global_state_cleared_at_startup

  // NOTE: Atm we gotta create the builtins every interpreter session, since the
  // parsing depends on the global bindings, which resets every time. Since
  // aren't many sessions, this redundancy is fine, just ugly.
  {
    error_buffer_ = subArena(temp_arena, 2048);
    rea.Type       = newTerm(arena, Primitive, 0);
    rea.Type->type = rea.Type; // NOTE: circular types
    addBuiltinGlobalBinding("Type", rea.Type);

    rea.False = newTerm(arena, Union, rea.Type);  // NOTE: "union {}"
    addBuiltinGlobalBinding("False", rea.False);

    auto path = platformGetFileFullPath(arena, "../data/builtin.rea");
    interpretFile(&global_state, path, true);

#define LOOKUP_BUILTIN(name) rea_##name = lookupBuiltin(#name);

#if 0
    // TODO #cleanup These List builtins are going too far...
    LOOKUP_BUILTIN(List);
    LOOKUP_BUILTIN(single);
    LOOKUP_BUILTIN(cons);
    LOOKUP_BUILTIN(fold);
    rea_concat = lookupBuiltin("+");
    LOOKUP_BUILTIN(Permute);
    LOOKUP_BUILTIN(foldConcat);
    LOOKUP_BUILTIN(foldPermute);
    LOOKUP_BUILTIN(permuteSame);
    LOOKUP_BUILTIN(permute);
    LOOKUP_BUILTIN(permuteFirst);
    LOOKUP_BUILTIN(permuteLast);
#undef LOOKUP_BUILTIN
#endif

    resetArena(temp_arena);
  }

  b32 success = interpretFile(&global_state, input_path, true);

  for (FileList *file_list = global_state.file_list;
       file_list;
       file_list = file_list->tail)
  {
    platformFreeFileMemory(file_list->head_content);
  }
    
  checkArena(arena);
  return success;
}

int engineMain()
{
  int success = true;

#if 0
  // for printf debugging: when it crashes you can still see the prints
  setvbuf(stdout, NULL, _IONBF, 0);
#endif

  assert(arrayCount(language_keywords) == Token_Keyword_END - Token_Keyword_START);

  void   *top_level_arena_base = (void*)teraBytes(2);
  size_t  top_level_arena_size = megaBytes(256);
  top_level_arena_base = platformVirtualAlloc(top_level_arena_base, top_level_arena_size);
  Arena top_level_arena_ = newArena(top_level_arena_size, top_level_arena_base);
  Arena *top_level_arena = &top_level_arena_;

  void   *temp_arena_base = (void*)teraBytes(3);
  size_t  temp_arena_size = megaBytes(4);
  temp_arena_base = platformVirtualAlloc(temp_arena_base, top_level_arena_size);
  temp_arena_ = newArena(temp_arena_size, temp_arena_base);

  char *files[] = {
    "../data/test.rea",
    "../data/natp.rea",
    "../data/z-slider.rea",
  };
  for (i32 file_id=0; file_id < arrayCount(files); file_id++)
  {
    FilePath input_path = platformGetFileFullPath(top_level_arena, files[file_id]);
    printf("> Interpreting file: %s\n", input_path.file);
    b32 file_success = beginInterpreterSession(top_level_arena, input_path);
    success = success && file_success;
    for (i32 i=0; i < 80; i++)
    {
      printf("-");
    }
    printf("\n\n");
    resetArena(top_level_arena, true);
  }
  return success;
}

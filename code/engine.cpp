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
#include "parser.cpp"
#include "debug_config.h"

global_variable Fixpoint *current_global_fixpoint;

Term  hole_ = {.kind = Term_Hole};
Term *hole = &hole_;

global_variable EngineState global_state;

inline b32
isDebugOn()
{
  return global_state.top_level_debug_mode;
}

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

inline b32
isNameOnlyArrowType(ArrowAst *in)
{
  return !(b32)in->param_types;
}

inline void
initTerm(Term *in, TermKind cat, Term *type)
{
  in->kind  = cat;
  in->type = type;
}

inline Term *
_newTerm(Arena *arena, TermKind kind, Term *type, size_t size)
{
  Term *out = (Term *)pushSize(arena, size, true);
  initTerm(out, kind, type);
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

inline Term *
getPath(Term *in0, TreePath *path)
{
  Term *in = in0;
  for (;path;)
  {
    in = getArg(in, path->head);
    path = path->tail;
  }
  return in;
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
  return (in)->type->kind == Term_Arrow;
}

inline void
attach(char *key, String value)
{
  InterpError *error = TK->error;
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

inline void
attach(char *key, Token *token)
{
  attach(key, token->string);
}

inline void
attach(char *key, Ast *ast)
{
  StartString start = startString(error_buffer);
  print(error_buffer, ast);
  attach(key, endString(start));
}

inline void
attach(char *key, Term *value)
{
  StartString start = startString(error_buffer);
  print(error_buffer, value);
  attach(key, endString(start));
}

inline void
attach(char *key, i32 n)
{
  StartString start = startString(error_buffer);
  print(error_buffer, "%d", n);
  attach(key, endString(start));
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
  return scope->pointers[index];
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
  Arrow *signature = castTerm(in->type, Arrow);
  return signature->param_count;
}

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
    return eq->op == rea.equal;
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
getPolyParamCount(Union *uni)
{
  if (Arrow *signature = castTerm(uni->type, Arrow))
  {
    return getPolyParamCount(signature);
  }
  return 0;
}

inline i32
getNonPolyParamCount(Union *uni)
{
  if (Arrow *signature = castTerm(uni->type, Arrow))
  {
    return signature->param_count - getPolyParamCount(signature);
  }
  return 0;
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
rewriteTerm(Term *from, Term *to, TreePath *path, Term *in0)
{
  Term *out0 = 0;
  maybeDeref(&in0);
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyTerm(temp_arena, in);
    if (path->head == -1)
    {
      out->op = rewriteTerm(from, to, path->tail, in->op);
    }
    else
    {
      assert((path->head >= 0) && (path->head < out->arg_count));
      allocateArray(temp_arena, out->arg_count, out->args);
      for (i32 arg_i=0; arg_i < out->arg_count; arg_i++)
      {
        if (arg_i == (i32)path->head)
          out->args[arg_i] = rewriteTerm(from, to, path->tail, in->args[arg_i]);
        else
          out->args[arg_i] = in->args[arg_i];
      }
    }
    out0 = out;
  }
  else
  {
    if (!equalNorm(in0, from))
    {
      DUMP("\nin0: ", in0, "\n", "from: ", from, "\n");
      invalidCodePath;
    }
    out0 = to;
  }
  return out0;
}

internal Term *
rewriteTerm(Term *eq_proof, TreePath *path, b32 right_to_left, Term *in0)
{
  auto [l,r] = getEqualitySides(eq_proof->type);
  Term *to_rewrite = 0;
  Term *rewrite_to = 0;   // lol naming
  if (right_to_left) {to_rewrite = r; rewrite_to = l;}
  else               {to_rewrite = l; rewrite_to = r;}

  return rewriteTerm(to_rewrite, rewrite_to, path, in0);
}

inline void
addRewrite(ProofState *state, Term *eq_proof, TreePath *path, b32 right_to_left)
{
  state->goal     = rewriteTerm(eq_proof, path, right_to_left, state->goal);
  state->rewrites = newRewriteChain(eq_proof, path, right_to_left, state->rewrites);
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

internal void
printArrow(StringBuffer *buffer, Arrow *in, b32 skip_output, PrintOptions opt)
{
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
    print(buffer, in->param_types[param_i], opt);
    if (param_i < in->param_count-1)
    {
      print(buffer, ", ");
    }
  }
  print(buffer, ")");

  if (in->output_type && !skip_output)
  {
    print(buffer, " -> ");
    print(buffer, in->output_type, opt);
  }
}

inline char *
printComposite(Arena *buffer, Composite *in, PrintOptions opt)
{
  char *out = buffer ? (char *)getNext(buffer) : 0;

  b32 print_list = false;
  if (Composite *type = castTerm(in->type, Composite))
  {
    if (!print_full_list &&
        ((type->op == rea.List) || (type->op == rea.PList)) &&
        in->op->kind == Term_Constructor)
    {
      print_list = true;
    }
  }

  b32 print_exists = false;
  if (!print_list)
  {
    print_exists = (in->op == rea.Exists);
  }

  if (print_list)
  {// list path
    print(buffer, "[");
    for (Record *iter = in; iter; )
    {
      if (iter->ctor == rea.nil)
      {
        // no need to print anything
        break;
      }
      else if (iter->ctor == rea.single)
      {
        print(buffer, reaHead(iter));
        break;
      }
      else
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
  else if (print_exists)
  {
    // Raw:   Exists(fn(c: Natp) -> Type {a = b + c})
    // Print: exists(c: Natp) a = b + c
    
    print(buffer, "exists");
    Function *prop = castTerm(getArg(in, 1), Function);
    assert(prop);
    Arrow *signature = castTerm(prop->type, Arrow);
    assert(signature);
    printArrow(buffer, signature, true, opt);
    print(buffer, " ");
    print(buffer, prop->body);
  }
  else
  {
    Arrow *op_signature = castTerm(in->op->type, Arrow);

    String op_name = {};
    if (Token *global_name = in->op->global_name)
    {
      op_name = global_name->string;
    }
    else if (Variable *var = castTerm(in->op, Variable))
    {
      op_name = var->name;
    }
    int precedence = precedenceOf(op_name);

    Term **printed_args = in->args;
    i32 printed_arg_count = in->arg_count;
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

    if (printed_arg_count == 2 && precedence)
    {// special path for infix binary operator
      if (precedence < opt.no_paren_precedence)
        print(buffer, "(");

      PrintOptions arg_opt = opt;
      // #hack to force printing parentheses when the precedence is the same (a+b)+c.
      arg_opt.no_paren_precedence = precedence+1;
      print(buffer, printed_args[0], arg_opt);

      print(buffer, " ");
      print(buffer, in->op, opt);
      print(buffer, " ");

      arg_opt.no_paren_precedence = precedence;
      print(buffer, printed_args[1], arg_opt);
      if (precedence < opt.no_paren_precedence)
        print(buffer, ")");
    }
    else
    {// normal prefix path
      print(buffer, in->op, opt);
      if (!(in->op->kind == Term_Constructor && printed_arg_count == 0))
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
        print(buffer, in->eq_or_proof, new_opt);
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
          print(buffer, in->cases[ctor_id], new_opt);
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

internal void
printStackPointerName(Arena *buffer, StackPointer *in)
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

internal void
printPointerName(StringBuffer *buffer, Pointer *in)
{
  const i32 max_path_length = 32;  // todo #grow
  String rev_field_names[max_path_length];
  i32 path_length = 0;
  Pointer *iter = in;
  for (b32 stop = false; !stop;)
  {
    if (iter->is_stack_pointer)
    {
      printStackPointerName(buffer, &iter->stack);
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

inline b32
shouldPrintExpanded(Pointer *in)
{
  b32 out = false;
  if (in->ref)
  {
    out = true;
    auto [uni, _] = castUnion(in->type);
    if (uni->ctor_count == 1)
    {
      out = false;
      if (in->ref)
      {
        Composite *ref = in->ref;
        for (i32 i=0; i < ref->arg_count && !out; i++)
        {
          if (Pointer *arg = castTerm(ref->args[i], Pointer))
          {
            if (shouldPrintExpanded(arg))
            {
              out = true;
            }
          }
        }
      }
    }
  }
  return out;
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
          if (shouldPrintExpanded(in))
          {
            print(buffer, in->ref, opt);
          }
          else
          {
            printPointerName(buffer, in);
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
          printArrow(buffer, in, false, new_opt);
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
          print(buffer, "<REWRITE>");
          Rewrite *rewrite = castTerm(in0, Rewrite);
          print(buffer, (rewrite)->type, new_opt);
          skip_print_type = true;
          print(buffer, " <=>");
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, (rewrite->body)->type, new_opt);
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
          newlineAndIndent(buffer, new_opt.indentation);
          print(buffer, rewrite->body, new_opt);
        } break;

        case Term_Computation:
        {
          print(buffer, "computation: ");
          print(buffer, (in0)->type, new_opt);
          skip_print_type = true;
        } break;

        case Term_Fork:
        {
          Fork *in = castTerm(in0, Fork);
          print(buffer, "fork ");
          print(buffer, in->subject, new_opt);
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          Union *uni = getUnionOrPolyUnion((in->subject)->type);
          for (i32 ctor_id = 0;
               ctor_id < uni->ctor_count;
               ctor_id++)
          {
            print(buffer, getConstructorName(uni, ctor_id));
            print(buffer, ": ");
            print(buffer, in->cases[ctor_id], new_opt);
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
      print(buffer, (in0)->type, new_opt);
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

internal b32
shouldPrintTypeInScope(Pointer *pointer)
{
  Term *type = pointer->type;
  if (!print_full_scope)
  {
    if (pointer->ignored) return false;

    if (type == rea.Type) return false;

    if (Union *uni = castTerm(type, Union))
    {
      // if you have no constructor, you're suddenly the MVP.
      if (uni->ctor_count) return false;
      else                 return true;
    }

    // if (castUnion(type)) return true;  // TODO: idk why this was here?

    if (type->kind == Term_Pointer) return false;

    Union *uni = getUnionOrPolyUnion(type);
    if (uni == rea.Or)
    {
      if (pointer->ref) return false;
    }
    else if (uni == rea.And)    return false;
    else if (uni == rea.Exists) return false;
  }
  return true;
}

inline void
prettyPrintScope(StringBuffer *buffer, Scope *scope)
{
  Arena *arena = temp_arena;
  struct PointerList {Pointer *head; PointerList *tail;};

  // NOTE: Skip the last scope since we already know
  while (scope)
  {
    Pointer **pointers = scope->pointers;
    for (int param_i = 0;
         param_i < scope->param_count;
         param_i++)
    {
      PointerList *list = pushStruct(arena, PointerList);
      list->head = pointers[param_i];
      list->tail = 0;

      while (list)
      {
        Pointer *pointer = list->head;
        list = list->tail;
        if (pointer)  // sometimes we error out, so pointer is null
        {
          if (shouldPrintTypeInScope(pointer))
          {
            printPointerName(buffer, pointer);
            print(buffer, ": ");
            print(buffer, pointer->type);
            print(buffer, "\n");
          }

          if (Record *record = castRecord(pointer))
          {
            Arrow *signature = getSignature(record->ctor);
            for (i32 i=0; i < record->member_count; i++)
            {
              // NOTE: print the member types.
              if (!isInferredParameter(signature, i))
              {
                Pointer *member = castTerm(record->members[i], Pointer);
                assert(member);
                llPush(arena, member, list);
              }
            }
          }
        }
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
  scope->pointers    = values;
  scope->param_count = param_count;
  return scope;
}

inline Scope *
newScope(Scope *outer, i32 param_count)
{
  Pointer **values = pushArray(temp_arena, param_count, Pointer *, true);
  return newScope(outer, param_count, values);
}

inline Function *
isAlwaysExpandFunction(Term *op)
{
  if (Function *fun = castTerm(op, Function))
  {
    if (checkFlag(fun->function_flags, FunctionFlag_expand))
      return fun;
  }
  return 0;
}

inline b32
isAnonymousFunction(Term *op0)
{
  if (Function *op = castTerm(op0, Function))
  {
    return !op->global_name;
  }
  return false;
}

internal Term *
evaluate_(EvalContext *ctx, Term *in0)
{
  Term *out0 = 0;
  Arena *arena = temp_arena;
  b32 substitute_only = ctx->substitute_only;  // TODO: this is more like "prefer_to_not_apply"

  i32 unused_var serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_evaluate)
  {
    DEBUG_INDENT(); DUMP("evaluate(", serial, "): ", in0);
  }

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

        if (ctx->offset == 0 &&
            (!substitute_only           ||
             isAlwaysExpandFunction(op) ||
             isAnonymousFunction(op) // NOTE: expand annoying bs
             ))
        {
          out0 = apply(op, in->arg_count, args, ctx->unfold_name);
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
        new_ctx.substitute_only = true;
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
          allocateArray(arena, in->case_count, out->cases);
          for (i32 i=0; i < in->case_count; i++)
          {
            out->cases[i] = evaluate_(ctx, in->cases[i]);
          }
          out0 = out;
        }
        else
        {
          if (Record *subject = castRecord(subject0))
          {
            i32 ctor_index = subject->ctor->index;
            out0 = evaluate_(ctx, in->cases[ctor_index]);
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

      case Term_Hole:
      {
        out0 = in0;
      } break;

      default:
        todoIncomplete;
    }
  }

  if (DEBUG_LOG_evaluate)
  {
    DEBUG_DEDENT(); DUMP("=> ", out0);
  }

  if (substitute_only) assert(out0);
  return out0;
}

inline Term *
toValue(Scope *scope, Term *in0)
{
  Term **args = (Term **)scope->pointers;  // NOTE: not gonna write to the scope, so casting is ok
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
evaluate(Term *in0, i32 arg_count, Term **args, String unfold_name={})
{
  EvalContext ctx = {.arg_count=arg_count, .args=args, .unfold_name=unfold_name};
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
isRootedFrom(Term *pointer0, Pointer *test_root)
{
  assert(test_root->is_stack_pointer);
  if (Pointer *pointer = castTerm(pointer0, Pointer))
  {
    if (!pointer->is_stack_pointer)
    {
      Pointer *root = pointer;
      while (!root->is_stack_pointer)
      {
        root = root->heap.record;
      }
      return root == test_root;
    }
  }
  return false;
}

inline b32
reaIsSingle(Term *in0)
{
  Record *in = castRecord(in0);
  return in->ctor == rea.single;
}

inline b32
reaIsCons(Term *in0)
{
  Record *in = castRecord(in0);
  return in->ctor == rea.cons;
}

// TODO: I think we can eliminate this comparison by simply storing a temporary
// pointer in the fork case.
inline b32
equalPointer(Term *l0, Term *r0)
{
  b32 out = false;
  Pointer *l = castTerm(l0, Pointer);
  Pointer *r = castTerm(r0, Pointer);
  if (l && r)
  {
    if (l->is_stack_pointer && r->is_stack_pointer)
    {
      out = (l->stack.depth == r->stack.depth &&
             l->stack.index == r->stack.index);
    }
    else if (l->heap.index == r->heap.index)
    {
      // TODO: not happy with this "looping up" thing. Since "compareTerms"
      // might have already compared the parents, then descend down.
      out = equalPointer(l->heap.record, r->heap.record);
    }
  }
  return out;
}

// TODO: We should only compare terms of the same type!
internal CompareTerms
compareTerms(Arena *arena, Term *l0, Term *r0)
{
  CompareTerms out = {.result = Trinary_Unknown};

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_compare)
  {
    DEBUG_INDENT(); DUMP("compare(", serial, "): ", l0, " and ", r0);
  }

  if (l0 == r0)
  {
    out.result = {Trinary_True};
  }
  else if (equalPointer(l0, r0))
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
            i32 false_count    = 0;
            i32       unique_diff_id   = 0;
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

        // NOTE: Anonymous functions can appear in terms such as Exist, so we
        // gotta handle them.
        case Term_Function:
        {
          Function *lhs = (Function *)l0;
          Function *rhs = (Function *)r0;
          if (equal(lhs->type, rhs->type))
          {
            if (equal(lhs->body, rhs->body))
            {
              out.result = Trinary_True;
            }
          }
        } break;

        case Term_Union:
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
    DEBUG_DEDENT(); DUMP("=>(", serial, ") ", out.result);
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

inline Term *
toAbstractTerm_(AbstractContext *ctx, Term *in0)
{
  assert(ctx->zero_depth >= ctx->env_depth);
  Term *out0 = 0;
  Arena *arena = ctx->arena;

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_toAbstractTerm)
  {
    DEBUG_INDENT(); DUMP("abstract(", serial, "): ", in0);
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
        out->cases  = pushArray(arena, in->case_count, Term*);
        for (i32 i=0; i < in->case_count; i++)
        {
          out->cases[i] = toAbstractTerm_(ctx, in->cases[i]);
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
    DEBUG_DEDENT(); DUMP("=> ", out0);
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

internal Term *
normalize_(NormContext *ctx, Term *in0) 
{
  Term *out0 = in0;
  Arena *arena = temp_arena;

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_normalize)
  {
    DEBUG_INDENT(); DUMP("normalize(", serial, "): ", in0);
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

        out0 = apply(norm_op, in->arg_count, norm_args, ctx->unfold_name);

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

        NormContext new_ctx = *ctx;
        {
          NormContext *ctx  = &new_ctx;
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
    DEBUG_DEDENT(); DUMP("=> ", out0);
  }

  // assert(isSequenced(in0) || out0);
  assert(out0);
  return out0;
}

internal Term *
normalize(Term *in0, NormOptions options={})
{
  i32 arbitrary_init_depth = 1000;
  String name_to_unfold = options.unfold_name;
  if (options.unfold_topmost_operator)
  {
    assert((!name_to_unfold));
    if (Composite *in = castTerm(in0, Composite))
    {
      Token *global_name = in->op->global_name;
      if (global_name) name_to_unfold = global_name->string;
    }
  }
  NormContext ctx = {.depth          = arbitrary_init_depth,
                     .unfold_name = name_to_unfold};
  return normalize_(&ctx, in0);
}

// todo #speed make this comparison faster by expanding along the way.
forward_declare inline b32
equalNorm(Term *l, Term *r)
{
  if (equal(l, r))
  {
    return true;
  }
  else
  {
    Term *lnorm = normalize(l, {.unfold_name=Unfold_Everything});
    Term *rnorm = normalize(r, {.unfold_name=Unfold_Everything});
    return equal(lnorm, rnorm);
  }
  return false;
}

#if REA_INTERNAL
inline void
assertEqualNorm(Term *l, Term *r)
{
  if (!equalNorm(l, r))
  {
    // print_var_delta = true;
    DUMP("l: ", l);
    DUMP("r: ", r);
    invalidCodePath;
  }
}
#else
inline void assertEqualNorm(Term *l, Term *r) {}
#endif

inline Term *
newRewrite(Term *eq_proof, Term *body, TreePath *path, b32 right_to_left, Term *type_to_rewrite=0)
{
  if (type_to_rewrite)
  {
    assertEqualNorm(body->type, type_to_rewrite);
  }
  else
    type_to_rewrite = body->type;

  auto [lhs, rhs] = getEqualitySides(eq_proof->type);
  Term *from = right_to_left ? lhs : rhs;
  Term *to   = right_to_left ? rhs : lhs;
  Term *type = rewriteTerm(from, to, path, type_to_rewrite);

  Rewrite *out = newTerm(temp_arena, Rewrite, type);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return out;
}

inline Composite *
newComposite(Term *op, i32 arg_count, Term **args, Term *reduce_proof=0)
{
  i32 unused_var serial = DEBUG_SERIAL++;
  
  checkRecursiveCall(op, arg_count, args, reduce_proof);
  Composite *out = 0;

  Arrow *signature = castTerm((op)->type, Arrow);
  assert(signature->param_count == arg_count);
  Term  *type      = substitute(signature->output_type, arg_count, args);

  for (i32 arg_i=0; arg_i < arg_count; arg_i++)
  {
    Term *actual_type   = args[arg_i]->type;
    Term *expected_type = substitute(signature->param_types[arg_i], arg_count, args);
    assertEqualNorm(actual_type, expected_type);
  }

  out = newTerm(temp_arena, Composite, type);
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

  return newComposite(op, param_count, args);
}

#define reaComposite(op, ...) reaComposite_(op, PP_NARG(__VA_ARGS__), __VA_ARGS__)

inline Term *
getReduceProofType(Fixpoint *fixpoint, i32 arg_count, Term **args)
{
  Term *recurse_measure = apply(fixpoint->measure_function, arg_count, args, {});
  Term *input_measure   = apply(fixpoint->measure_function, arg_count, (Term**)fixpoint->args, {});
  Composite *out = reaComposite(fixpoint->well_founded_order, recurse_measure, input_measure);
  return out;
}

inline b32
isFunctionBeingBuilt(Term *op0)
{
  if (Function *op = castTerm(op0, Function))
  {
    return (op->body == 0);
  }
  return false;
}

forward_declare inline void
checkRecursiveCall(Term *op0, i32 arg_count, Term **args, Term *reduce_proof)
{
  Fixpoint *fixpoint = current_global_fixpoint;
  if (Function *op = castTerm(op0, Function))
  {
    if (op->body == 0)
    {
      assert(op == fixpoint->fun);
      b32 recursive_call_valid = false;

      if (reduce_proof)
      {
        // manual reduction proof
        Term *expected_type = getReduceProofType(fixpoint, arg_count, args);
        assertEqualNorm(reduce_proof->type, expected_type);
        recursive_call_valid = true;
      }
      else
      {
        // fallback hacky automated check
        auto &subject = fixpoint->fork_subject;
        if (subject)
        {
          assert(subject->is_stack_pointer);
          i32 index = subject->stack.index;
          recursive_call_valid = isRootedFrom(args[index], subject);
        }
      }

      if (!recursive_call_valid)
      {
        String name = op->global_name->string;
        print(0, "RECURSION REJECTED in \"%.*s\"! ", name.length, name.chars);

        print(0, "(args : ");
        for (i32 i=0; i < arg_count; i++)
        {
          print(0, args[i]);
          if (i != arg_count-1) print(0, ", ");
        }
        print(0, ")\n");

        // assert(false);  // Let's leave that as a warning for now
      }
    }
  }
}

inline Composite *
newEquality(Term *lhs, Term *rhs)
{
  return reaComposite(rea.equal, lhs->type, lhs, rhs);
}

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
      pointer->ref = newComposite(ctor, member_count, members);
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
  pointer->ignored = false;  // TODO: hack to unwind the pointers ignored by unfolding
}

inline Fork *
newFork(Term *subject, i32 case_count, Term **cases, Term *goal)
{
  i32 unused_var serial = DEBUG_SERIAL;
  Arena *arena = temp_arena;
  Union *uni = getUnionOrPolyUnion(subject->type);
  assert(case_count == uni->ctor_count);
  for (i32 i=0; i < case_count; i++)
  {
    assert(instantiate(subject, i));
    assertEqualNorm(cases[i]->type, goal);
    uninstantiate(subject);
  }

  Fork *out = newTerm(arena, Fork, goal);
  out->subject    = subject;
  out->case_count = case_count;
  out->cases      = cases;
  return out;
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
  return reaComposite(rea.single, (head)->type, head);
}

inline Term *
reaCons(Term *head, Term *tail)
{
  return reaComposite(rea.cons, (head)->type, head, tail);
}

inline Term *
reaConcat(Arena *arena, Term *a, Term *b)
{
  return reaComposite(rea.concat, reaListType(a), a, b);
}

inline Term *
newIdentity(Term *term)
{
  Term *eq = newEquality(term, term);
  Computation *out = newTerm(temp_arena, Computation, eq);
  return out;
}

forward_declare internal Term *
apply(Term *op, i32 arg_count, Term **args, String unfold_name)
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
    if (fun->body == 0)
    {
      should_apply_function = false;  // NOTE: not strictly needed
    }
    if (checkFlag(fun->function_flags, FunctionFlag_no_expand))
    {
      should_apply_function = (unfold_name.chars &&
                               (unfold_name.chars == Unfold_Everything.chars ||
                                equal(fun->global_name->string, unfold_name)));
    }

    if (should_apply_function)
    {
      out0 = evaluate(fun->body, arg_count, args, unfold_name);
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
            out0 = apply(eq->op, eq->arg_count, eq->args, unfold_name);
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
    DEBUG_DEDENT(); DUMP("=> ", out0);
  }

  return out0;
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
    scope->pointers[param_i] = newStackPointer(name, scope->depth, param_i, type);
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
  return slot->terms[0];
}

inline void
addGlobalBinding(Token *name, Term *value, i32 tag_count=0, String *tags=0)
{
  Arena *arena = global_state.top_level_arena;
  assert(inArena(arena, value));
  GlobalBinding *slot = lookupGlobalNameSlot(name->string, true);
  // TODO #cleanup check for type conflict

  i32 slot_i = slot->count++;
  slot->terms[slot_i] = value;
  assert(slot->count <= arrayCount(slot->terms));

  Token *name_copy = pushCopy(arena, name);
  value->global_name = name_copy;
  if (tags)
  {
    slot->tag_counts[slot_i] = tag_count;
    slot->tags[slot_i]       = copyArray(arena, tag_count, tags);
  }
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

struct OptionalU32 { b32 success; u32 value; };

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
  if (goal->kind == Term_Hole) {return true;}
  if (equalNorm(actual, goal)) {return true;}
  return false;
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
    DEBUG_INDENT(); DUMP("unify(", serial, ") ", in0, " with ", goal0);
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
    DEBUG_DEDENT(); DUMP("=>(", serial, ") ", ((char *)(success ? "true" : "false")));
  }

  return success;
}

inline SolveArgs
solveArgs(Solver *solver, Term *op, Term *goal0, Token *blame_token=0)
{
  i32    arg_count = 0;
  Term **args      = 0;

  i32 unused_var serial = DEBUG_SERIAL++;

  if (Arrow *signature = castTerm((op)->type, Arrow))
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
maybeEqualByComputation(Term *lhs, Term *rhs)
{
  Term *out = 0;
  if (equalNorm(lhs, rhs))
  {
    out = newComputation_(lhs, rhs);
  }
  return out;
}

inline Term *
reaEqualByComputation(Term *lhs, Term *rhs)
{
  Term *out = maybeEqualByComputation(lhs, rhs);
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

inline Term *
seekGoalRecursive(Solver *solver, Term *value, Term *goal)
{
  Term *out = 0;

  if (equal(value->type, rea.False))
  {
    out = newFork(value, 0, 0, goal);
  }

  if (!out && equalNorm(value->type, goal))
  {
    out = value;
  }

  if (!out)
  {
    if (Record *record = castRecord(value))
    {
      for (i32 member_i = 0; member_i < record->arg_count && !out; member_i++)
      {
        out = seekGoalRecursive(solver, record->args[member_i], goal);
      }
    }
  }

  if (!out && solver->try_reductio && goal == rea.Type)
  {
    if (Arrow *hypothetical = castTerm(value->type, Arrow))
    {
      if (hypothetical->output_type == rea.False)
      {
        SolveArgs solve_args = solveArgs(solver, value, rea.False);
        if (solve_args.args)
        {
          Term *f = newComposite(value, solve_args.arg_count, solve_args.args);
          out = newFork(f, 0, 0, goal);
        }
      }
    }
  }

  return out;
}

inline Term *
seekGoal(Solver *solver, Term *goal)
{
  Term *out = 0;
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
        Term *value = scope->pointers[scope_i];
        out = seekGoalRecursive(solver, value, goal);
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
  solver->depth++;
  if (solver->depth > 1)
  {
    solver->try_reductio = false;  // clearly the upper level has failed to resolve the falsehood
  }

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
      out = maybeEqualByComputation(l, r);
    }

    if (!out)
    {
      out = seekGoal(solver, goal);
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
          if (hint->type->kind == Term_Arrow)
          {
            SolveArgs solve_args = solveArgs(solver, hint, goal);
            if (solve_args.args)
            {
              out = newComposite(hint, solve_args.arg_count, solve_args.args);
            }
          }
          else if (equal(hint->type, goal))
          {
            out = hint;
          }
        }
        else
          break;
      }
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
  return checkFlag(typer->expected_errors, ExpectError_WrongType);
}

inline b32
expectedAmbiguous(Typer *typer)
{
  return checkFlag(typer->expected_errors, ExpectError_Ambiguous);
}

inline TermArray
getOverloads(Typer *typer, Identifier *ident, Term *goal0)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL;
  TermArray out = {};
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
  {
    if (goal0->kind == Term_Hole)
    {
      // bypass typechecking.
      out.items = slot->terms;
      out.count = slot->count;
    }
    else
    {
      b32 matches = false;
      allocateArray(temp_arena, slot->count, out.items);
      for (int slot_i=0; slot_i < slot->count; slot_i++)
      {
        Term *item = slot->terms[slot_i];
        if (Arrow *signature = castTerm((item)->type, Arrow))
        {
          UnifyContext *ctx = newUnifyContext(signature, getScopeDepth(typer->scope));
          matches = unify(ctx, signature->output_type, goal0);
        }
        if (matches)
        {
          out.items[out.count++] = slot->terms[slot_i];
        }
      }
      if (out.count == 0)
      {
        if (expectedWrongType(typer)) silentError();
        else
        {
          reportError(ident, "found no matching overload");
          attach("operator", ident->token.string);
          attach("output_type_goal", goal0);
          attach("available_overloads", slot->count, slot->terms, printOptionPrintType());
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

internal SearchOutput
searchExpression(Term *lhs, Term* in0)
{
  if (DEBUG_LOG_search)
  {
    i32 serial = DEBUG_SERIAL++;
    DEBUG_INDENT(); DUMP("search(", serial, "): ", lhs, " in ", "in0");
  }

  b32       found = false;
  TreePath *path  = 0;
  Arena *arena = temp_arena;
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
        SearchOutput op = searchExpression(lhs, in->op);
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
            SearchOutput arg = searchExpression(lhs, in->args[arg_i]);
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
        SearchOutput recurse = searchExpression(lhs, in->record);
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

  if(DEBUG_LOG_search)
  {
    DEBUG_DEDENT(); DUMP("=> ", found);
  }

  return {.found=found, .path=path};
}

internal Arrow *
copyArrow(Arena *arena, Arrow *in)
{
  Arrow *out = copyTerm(arena, in);
  return out;
}

inline Term *
buildCtorAst(CtorAst *in, Term *output_type)
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
getOverloadFromTags(GlobalBinding *lookup, i32 query_tag_count, String *query_tags)
{
  Term *out = 0;
  for (i32 slot_i=0; slot_i < lookup->count && !out; slot_i++)
  {
    i32 tag_count = lookup->tag_counts[slot_i];
    String *tags  = lookup->tags[slot_i];
    b32 failed = false;
    for (i32 query_tag_i=0; query_tag_i < query_tag_count && !failed; query_tag_i++)
    {
      String query_tag = query_tags[query_tag_i];
      failed = true;
      for (i32 tag_i=0; tag_i < tag_count && failed; tag_i++)
      {
        String tag = tags[tag_i];
        if (equal(query_tag, tag))
        {
          failed = false;
        }
      }
    }
    if (!failed)
    {
      out = lookup->terms[slot_i];
    }
  }
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

inline i32
termKindScore(Term *in0)
{
  // NOTE: unfortunately we can't score based on the kind alone, since stack
  // pointers and heap pointers have the same kind -> lame!
  switch (in0->kind)
  {
    case Term_Pointer:
    {
      Pointer *in = (Pointer *)in0;
      return in->is_stack_pointer ? 0 : 1;
    } break;
  };
  return 10 + in0->kind;
}

inline b32
algebraLessThan(Term *a0, Term *b0)
{
  b32 out = false;

  // if (isDebugOn())
  // {
  //   DEBUG_INDENT(); DUMP(a0, " < ", b0);
  // }

  i32 ascore = termKindScore(a0);
  i32 bscore = termKindScore(b0);
  if (a0 == b0)
  {
  }
  else if (ascore < bscore)
  {
    out = true;
  }
  else if (ascore == bscore)
  {
    if (a0->global_name && b0->global_name)
    {
      out = stringLessThan(a0->global_name->string, b0->global_name->string);
    }
    else
    {
      switch (a0->kind)
      {
        case Term_Pointer:
        {
          Pointer *a = (Pointer *)a0;
          Pointer *b = (Pointer *)b0;
          {
            b32 is_stack_pointer = a->is_stack_pointer;
            assert(b->is_stack_pointer == is_stack_pointer);
            if (is_stack_pointer)
            {
              out = stringLessThan(a->stack.name, b->stack.name);
            }
            else
            {
              if (algebraLessThan(a->heap.record, b->heap.record))
              {
                out = true;
              }
              else if (a->heap.record == b->heap.record)
              {
                out = a->heap.index < b->heap.index;
              }
            }
          }
        } break;

        case Term_Composite:
        {
          Composite *a = (Composite *)a0;
          Composite *b = (Composite *)b0;
          if (algebraLessThan(a->op, b->op))
          {
            out = true;
          }
          else if (a->op == b->op)
          {
            assert(a->arg_count == b->arg_count);
            for (i32 i=0; i < a->arg_count; i++)
            {
              if (algebraLessThan(a->args[i], b->args[i]))
              {
                out = true;
                break;
              }
              if (algebraLessThan(b->args[i], a->args[i]))
              {
                break;
              }
            }
          }
        } break;
      }
    }
  }

  // if (isDebugOn())
  // {
  //   DEBUG_DEDENT(); DUMP("=> ", out);
  // }

  return out;
}

inline TreePath *
treePath(i32 head, TreePath *tail=0)
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
treePath(TreePath *prefix, i32 item)
{
  Arena *arena = temp_arena;
  TreePath *reverse_prefix = reversePath(arena, prefix);
  TreePath *out = pushStruct(arena, TreePath, true);
  out->head = item;
  out->tail = reverse_prefix;
  out = reverseInPlace(out);
  return out;
}

inline TreePath *
concatPath(TreePath *a, TreePath *b)
{
  TreePath *it  = a;
  TreePath *out = 0;
  auto &arena = temp_arena;
  for (;it;)
  {
    if (it)
    {
      if (out)
      {
        out->tail = pushStruct(arena, TreePath);
        out = out->tail;
      }
      else
      {
        out = pushStruct(arena, TreePath);
      }
      out->head = it->head;
      out->tail = 0;
      it = it->tail;
    }
    else
    {
      if (out) out->tail = b;
      else     out = b;
    }
  }
  return out;
}

inline Term *
getTransformResult(Term *in)
{
  auto [_, out] = getEqualitySides(in->type);
  return out;
}

inline Term *
getPermuteRhs(Term *in)
{
  return getArg(in->type, 2);
}

inline Term *
getEqualRhs(Term *in)
{
  return getArg(in->type, 2);
}

inline void
setEqProof(Term *eq_proof, Transformation *transform)
{
  if (eq_proof)
  {
    transform->eq_proof = eq_proof;
    transform->term = getEqualRhs(eq_proof);
  }
}

inline void
eqChain(Term *f, Transformation *transform)
{
  Term *e = transform->eq_proof;
  if (f)
  {
    transform->term = getEqualRhs(f);
    if (e)
    {
      Term *rewrite = newRewrite(f, e, treePath(2), true);
      setEqProof(rewrite, transform);
      assert(transform->term == getEqualRhs(f));
    }
    else
    {
      setEqProof(f, transform);
    }
  }
}

internal Term *
getFoldList(Term *op, Term *in0)
{
  Term *out = 0;
  if (Composite *in = castTerm(in0, Composite))
  {
    if (in->op == op)
    {
      Term *left_operand  = getArg(in, 0);
      Term *right_operand = getArg(in, 1);
      if (Composite *comp = castTerm(left_operand, Composite))
      {
        assert(comp->op != op);
      }
      Term *tail = getFoldList(op, right_operand);
      out = reaCons(left_operand, tail);
    }
  }
  if (!out)
  {
    out = reaSingle(in0);
  }
  return out;
}

internal TermArray
toCArray(Term *list0)
{
  i32    count = 0;
  Term **items = 0;
  const i32 cap = 32;  // todo #grow
  allocateArray(temp_arena, cap, items);

  for (Term *iter0=list0; ; )
  {
    Record *iter = castRecord(iter0);
    Term *head = reaHead(iter);
    assert(count < cap);
    items[count++] = head;

    if (iter->ctor == rea.single)
    {
      break;
    }
    else
    {
      assert(iter->ctor == rea.cons);
      Term *tail = reaTail(iter);
      iter0 = tail;
    }
  }

  return {count, items};
}

internal Term *
toReaList(Term **array, i32 count)
{
  assert(count > 0);
  Term *T = (array[0])->type;
  Term *out = reaComposite(rea.single, T, array[count-1]);
  for (i32 i=count-2; i >= 0; i--)
  {
    out = reaComposite(rea.cons, T, array[i], out);
  }
  return out;
}

inline void
descend(Transformation *transform, TreePath *path)
{
  if (path)
  {
    Transformation *up = pushCopy(temp_arena, transform);
    transform->term     = getPath(transform->term, path);
    transform->eq_proof = 0;
    transform->path     = path;
    transform->up       = up;
  }
}

inline void
descend(Transformation *transform, i32 index)
{
  descend(transform, treePath(index));
}

inline void
ascend(Transformation *transform)
{
  TreePath *down_path  = transform->path;
  Term     *down_proof = transform->eq_proof;
  *transform = *transform->up;
  if (!transform->eq_proof)
  {
    transform->eq_proof = newIdentity(transform->term);
  }
  if (down_proof)
  {
    TreePath *path = treePath(2, down_path); // rewrite on the rhs
    Term *rewrite = newRewrite(down_proof, transform->eq_proof, path, true);
    setEqProof(rewrite, transform);
  }
}

inline void
algebraFlatten(Term *op, Term *associative, Transformation *transform)
{
  for (b32 stop = false; !stop; )
  {
    stop = true;
    if (Composite *term = castTerm(transform->term, Composite))
    {
      if (term->op == op)
      {
        Term *l0 = getArg(term, 0);
        Term *r  = getArg(term, 1);

        if (Composite *l = castTerm(l0, Composite))
        {
          if (l->op == op)
          {
            stop = false;
            eqChain(reaComposite(associative, getArg(l, 0), getArg(l, 1), r), transform);
          }
        }
      }
    }
  }

  if (Composite *in = castTerm(transform->term, Composite))
  {
    if (in->op == op)
    {
      descend(transform, 1);
      algebraFlatten(op, associative, transform);
      ascend(transform);
    }
  }
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

inline void
changeType(Term *in, Term *type)
{
  assert(equal(normalize(in->type),
               normalize(type)));
  in->type = type;
}

internal Term *
provePermute_(Term *al, Term **Cbac, i32 *indexes, i32 count)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  Arena *arena = temp_arena;
  Term *out = 0;
  assert(count > 0);
  Term *T = (Cbac[0])->type;

  if (count == 1)
  {
    out = reaComposite(rea.permuteSame, T, al);
  }
  else
  {
    i32 a_index = indexes[0];
    Term *l = reaTail(al);

    Term **Cbc = pushArray(arena, count-1, Term *);
    for (i32 i=0; i < a_index; i++)
    {
      Cbc[i] = Cbac[i];
    }
    for (i32 i=a_index+1; i < count; i++)
    {
      assert(i-1 < count-1);
      Cbc[i-1] = Cbac[i];
    }

    Term *a = reaHead(al);
    Term *b = (a_index > 0)       ? toReaList(Cbc, a_index)                   : 0;
    Term *c = (a_index+1 < count) ? toReaList(Cbc+a_index, count-(a_index+1)) : 0;

    Term *recurse = provePermute_(l, Cbc, indexes+1, count-1);

    if (b && c)
    {// permuteMiddle
      out = reaComposite(rea.permuteMiddle, T,a,l,b,c, recurse);
      Term *bac = toReaList(Cbac, count);  // todo: can this be passed along?
      Term *type = reaComposite(rea.Permute, T,al,bac);
      changeType(out, type);
    }
    else if (c)
    {// permuteFirst
      out = reaComposite(rea.permuteFirst, T,a,l,c, recurse);
    }
    else
    {// permuteLast
      out = reaComposite(rea.permuteLast, T,a,l,b, recurse);
      Term *bac = toReaList(Cbac, count);  // todo: can this be passed along?
      Term *type = reaComposite(rea.Permute, T,al,bac);
      changeType(out, type);
    }
  }
  return out;
}

internal Term *
provePermute(Term *rea_list, Term **sorted, i32 *indexes, i32 count)
{
  Term *out = provePermute_(rea_list, sorted, indexes, count);
  return out;
}

internal Term *
algebraSort(Term *rea_list)
{
  Arena *arena = temp_arena;
  auto [count, array] = toCArray(rea_list);
  Term **sorted = copyArray(arena, count, array);

  i32 *tmp_indexes = pushArray(arena, count, i32);
  for (i32 i=0; i < count; i++) { tmp_indexes[i] = i; }

  quickSort(sorted, tmp_indexes, count);

  i32 *inverse = pushArray(arena, count, i32);
  for (i32 i=0; i < count; i++) { inverse[tmp_indexes[i]] = i; }

  i32 *indexes = pushArray(arena, count, i32);
  for (i32 i=0; i < count; i++)
  {
    indexes[i] = inverse[i];
    for (i32 left_index=0; left_index < i; left_index++)
    {
      if (inverse[left_index] < inverse[i])
      {
        indexes[i]--;
      }
    }
  }

  Term *proof = provePermute(rea_list, sorted, indexes, count);
  return proof;
}

internal Term *
buildTestSort(Typer *typer, CompositeAst *ast)
{
  Term *out = 0;
  assert(ast->arg_count == 1);
  if (Term *list0 = buildTerm(typer, ast->args[0], hole))
  {
    out = algebraSort(list0);
  }
  return out;
}

inline void
algebraNorm_(Algebra *algebra, Transformation *transform)
{
  i32 unused_var serial = DEBUG_SERIAL++;
  Term *T = algebra->type;

  if (Composite *comp = castTerm(transform->term, Composite))
  {
    Term *op          = comp->op;
    Term *associative = 0;
    Term *commutative = 0;

    if (op == algebra->add || op == algebra->mul)
    {
      if (op == algebra->add)
      {
        associative = algebra->addAssociative;
        commutative = algebra->addCommutative;
      }
      else
      {
        associative = algebra->mulAssociative;
        commutative = algebra->mulCommutative;
      }

      algebraFlatten(op, associative, transform);

      Term *list   = getFoldList(op, transform->term);
      Term *folded = reaComposite(rea.fold, T, op, list);
      eqChain(reaEqualByComputation(transform->term, folded), transform);

      TreePath *path = treePath(2);  // fold list
      for (; ; )
      {
        descend(transform, treePath(path, 1));  // list head
        algebraNorm_(algebra, transform);
        ascend(transform);

        Term *list = getPath(transform->term, path);
        if (reaIsSingle(list)) break;
        else
        {
          path = treePath(path, 2);
        }
      }
 
      comp = castTerm(transform->term, Composite);
      list = getPath(comp, treePath(2));
      Term *sort      = algebraSort(list);
      Term *sorted    = getPermuteRhs(sort);
      Term *eq_sorted = reaComposite(rea.foldPermute, T, op,
                                     associative, commutative,
                                     list, sorted, sort);
      eqChain(eq_sorted, transform);
    }
  }
}

internal void
applyMulDistributive(Algebra *algebra, Transformation *tform)
{
  if (Composite *comp = castTerm(tform->term, Composite))
  {
    for (i32 arg_i=0; arg_i < comp->arg_count; arg_i++)
    {
      descend(tform, arg_i);
      applyMulDistributive(algebra, tform);
      ascend(tform);
    }

    comp = castTerm(tform->term, Composite);
    assert(comp);
    if (comp->op == algebra->mul)
    {
      b32 changed = false;
      Composite *lcomp = castTerm(getArg(comp, 0), Composite);
      if (lcomp && (lcomp->op == algebra->add))
      {
        changed = true;
        Term *dist = reaComposite(algebra->mulDistributiveRight,
                                  getArg(lcomp, 0), getArg(lcomp, 1), getArg(comp, 1));
        eqChain(dist, tform);
      }
      else
      {
        Composite *rcomp = castTerm(getArg(comp, 1), Composite);
        if (rcomp && (rcomp->op == algebra->add))
        {
          changed = true;
          Term *dist = reaComposite(algebra->mulDistributiveLeft,
                                    getArg(rcomp, 0), getArg(rcomp, 1), getArg(comp, 0));
          eqChain(dist, tform);
        }
      }

      if (changed)
      {
        comp = castTerm(tform->term, Composite);
        for (i32 arg_i=0; arg_i < comp->arg_count; arg_i++)
        {
          descend(tform, arg_i);
          applyMulDistributive(algebra, tform);
          ascend(tform);
        }
      }
    }
  }
}

inline void
algebraNorm(Algebra *algebra, Transformation *transform)
{
  applyMulDistributive(algebra, transform);
  algebraNorm_(algebra, transform);
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
        allocateArray(arena, in->case_count, out->cases);
        for (i32 i=0; i < in->case_count; i++)
        {
          out->cases[i] = copyToGlobalArena(in->cases[i]);
        }
        out0 = out;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        Rewrite *out = copyTerm(arena, in);
        out->eq_proof = copyToGlobalArena(in->eq_proof);
        out->body     = copyToGlobalArena(in->body);

        out->path = 0;
        TreePath *path = 0;
        for (TreePath *iter = in->path; iter; iter = iter->tail)
        {
          TreePath *new_path = pushStruct(arena, TreePath);
          new_path->head = iter->head;
          new_path->tail = 0;
          if (path)
          {
            path->tail = new_path;
            path = new_path;
          }
          else
          {
            out->path = path = new_path;
          }
        }

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
buildFunctionGivenSignature(Typer *typer0, Arrow *signature, Ast *in_body,
                            Token *global_name=0, FunctionAst *in_fun=0)
{
  i32 unused_var serial = DEBUG_SERIAL;
  // :persistent-global-function.

  // NOTE: We MUST control the arena, otherwise the self-reference will be
  // invalidated (TODO: maybe the copier should know about self-reference).
  Arena *arena = global_name ? global_state.top_level_arena : temp_arena;

  Function *out = newTerm(arena, Function, signature);
  if (in_fun) out->function_flags = in_fun->function_flags;

  Term *body = 0;
  Typer typer_ = *typer0;
  {
    Typer *typer = &typer_;
    typer->scope = introduceSignature(typer->scope, signature);
    extendBindings(typer);

    Fixpoint *previous_global_fixpoint = current_global_fixpoint;
    Fixpoint fixpoint = {};
    if (global_name)
    {
      // NOTE: add binding first to support recursion
      addGlobalBinding(global_name, out, in_fun->tag_count, in_fun->tags);

      fixpoint.fun  = out;
      fixpoint.args = typer->scope->pointers;
      if (in_fun->measure_function)
      {
        if (in_fun->well_founded_proof)
        {
          if (Term *measure_function0 = buildTerm(typer0, in_fun->measure_function, hole))
          {
            fixpoint.measure_function = castTerm(measure_function0, Function);
            assert(fixpoint.measure_function);
            if (Term *well_founded_proof = buildTerm(typer0, in_fun->well_founded_proof, hole))
            {
              b32 valid_wf_proof = false;
              if (Composite *wf = castTerm(well_founded_proof->type, Composite))
              {
                if (wf->op == rea.WellFounded)
                {
                  valid_wf_proof = true;
                  fixpoint.well_founded_order = getArg(wf, 1);
                }
              }

              if (!valid_wf_proof)
              {
                reportError(in_fun->well_founded_proof, "well-founded proof is invalid");
                attach("wf_proof_type", well_founded_proof->type);
              }
            }
          }
        }
        else
          reportError(in_fun, "must supply both a measure function and a well-founded proof");
      }

      assert(!current_global_fixpoint);
      current_global_fixpoint = &fixpoint;
    }

    if (noError())
    {
      for (i32 index=0; index < signature->param_count; index++)
      {
        String name = signature->param_names[index];
        addLocalBinding(typer, name, index);
      }
      Term *body_type = toValue(typer->scope, signature->output_type);
      if ((body = buildTerm(typer, in_body, body_type)))
      {
        if (signature->output_type == hole)
        {
          // write back the output type
          signature->output_type = toAbstractTerm(temp_arena, body->type, getScopeDepth(typer0));
          Term *check = toValue(typer->scope, signature->output_type);
          assertEqualNorm(body->type, check);
        }
      }
    }

    current_global_fixpoint = previous_global_fixpoint;
  }

  if (body)
  {
    out->body = toAbstractTerm(temp_arena, body, getScopeDepth(typer0));
    if (global_name)
    {
      out->body = copyToGlobalArena(out->body);
    }
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline Term *
buildWithNewAssets(Typer *typer, i32 asset_count, String *names, Term **assets, Ast *body, Term *goal)
{
  Term *out = 0;
  if (asset_count)
  {
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
      out = newComposite(fun, asset_count, assets);
    }
  }
  else
  {
    out = buildTerm(typer, body, goal);
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

inline void
reportAmbiguousError(Typer *typer, Ast *ast, char *message)
{
  if (expectedAmbiguous(typer))
    silentError();
  else
    reportError(ast, message);
}

inline void
reportWrongTypeError(Typer *typer, Ast *ast, char *message)
{
  if (expectedWrongType(typer))
    silentError();
  else
    reportError(ast, message);
}


internal Term *
buildComposite(Typer *typer, CompositeAst *in, Term *goal)
{
  Arena *arena = temp_arena;
  i32 unused_var serial = DEBUG_SERIAL++;
  Term *value = 0;

  if (equal(in->op->token, "test_sort"))
  {
    // macro interception
    value = buildTestSort(typer, in);
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
        op_list = getOverloads(typer, op_ident, goal);
      }
    }
    else if (CtorAst *op_ctor = castAst(in->op, CtorAst))
    {
      if (Term *ctor = buildCtorAst(op_ctor, goal))
      {
        should_build_op = false;
        allocateArray(temp_arena, 1, op_list.items);
        op_list.count    = 1;
        op_list.items[0] = ctor;
      }
    }

    if (noError() && should_build_op)
    {
      if (Term *op0 = buildTerm(typer, in->op, hole).value)
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
        setFlag(&typer->expected_errors, ExpectError_WrongType);
        setFlag(&typer->expected_errors, ExpectError_Ambiguous);
      }

      for (i32 attempt=0;
           (attempt < op_list.count) && noError();
           attempt++)
      {
        Term *op = op_list.items[attempt];
        if (Arrow *signature = getSignature(op))
        {
          i32 param_count = signature->param_count;
          Ast **expanded_args = in->args;
          if (param_count != in->arg_count)
          {
            allocateArray(arena, param_count, expanded_args);
            i32 explicit_param_count = getExplicitParamCount(signature);
            if (in->partial_args)
            {
              for (i32 param_i = 0; param_i < param_count; param_i++)
              {
                expanded_args[param_i] = newAst(arena, Hole, &in->op->token);
              }

              if (in->keywords)
              {
                assert(in->args);
                for (i32 arg_i = 0;
                     arg_i < in->arg_count && noError();
                     arg_i++)
                {
                  String keyword = in->keywords[arg_i];
                  b32 filled = false;
                  for (i32 param_i = 0; param_i < param_count && !filled; param_i++)
                  {
                    String param_name = signature->param_names[param_i];
                    if (equal(keyword, param_name))
                    {
                      expanded_args[param_i] = in->args[arg_i];
                      filled = true;
                    }
                  }

                  if (!filled)
                  {
                    if (expectedWrongType(typer)) silentError();
                    else
                    {
                      reportError(in->args[arg_i], "keyword argument does not correspond to any parameter name");
                    }
                  }
                }
              }
            }
            else if (in->arg_count == explicit_param_count)
            {
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
                reportError(&in->token, "argument count does not match the number of explicit parameters (expected: %d, got: %d)", explicit_param_count, in->arg_count);
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
                  reportError(in, "cannot unify output");
                  attach("signature->output_type", signature->output_type);
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
                  setFlag(&new_typer.expected_errors, ExpectError_Ambiguous);
                  if (Term *arg = buildTerm(&new_typer, in_arg, hole))
                  {
                    args[arg_i] = arg;
                    arg_was_filled = true;
                    b32 unify_result = unify(ctx, param_type0, arg->type);
                    if (unify_result)
                    {
                      // NOTE: recheck the stack as an optimization
                      stack_has_hole = false;
                      for (i32 i=0; i <= arg_i && !stack_has_hole; i++)
                      {
                        if (!args[i]) stack_has_hole = true;
                      }
                    }
                    else
                    {
                      if (expectedWrongType(typer)) silentError();
                      else
                      {
                        reportError(in_arg, "cannot unify parameter type with argument %d's type", arg_i);
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
                  if (Term *arg = buildTerm(typer, in_arg, expected_arg_type))
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
                      reportError(in_arg, "cannot solve for argument %d", arg_i);
                      attach("parameter_name", signature->param_names[arg_i]);
                      attach("expected_arg_type", expected_arg_type);
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
              if (value)
              {
                reportAmbiguousError(typer, in->op, "composite is ambiguous");
              }
              else if (Function *fun = isAlwaysExpandFunction(op))
              {
                if (fun->body) value = substitute(fun->body, param_count, args);
                else reportError(fun->global_name, "function tries to expand into itself");
              }
              else
              {
                Term *reduce_proof = 0;
                if (in->reduce_proof)
                {
                  if (isFunctionBeingBuilt(op))
                  {
                    Fixpoint *fixpoint = current_global_fixpoint;
                    if (fixpoint->measure_function && fixpoint->well_founded_order)
                    {
                      Typer reduce_proof_typer = *typer;
                      reduce_proof_typer.expected_errors = 0;
                      Term *expected_type = getReduceProofType(fixpoint, param_count, args);
                      reduce_proof = buildTerm(&reduce_proof_typer, in->reduce_proof, expected_type);
                    }
                    else
                      reportError(in->reduce_proof, "please supply the measure function and the well founded order to use this feature");
                  }
                  else
                  {
                    reportError("reduce proof is only applicable when the function is the fixpoint being built");
                  }
                }

                if (noError())
                {
                  args = copyArray(arena, param_count, args);
                  value = newComposite(op, param_count, args, reduce_proof);
                }
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
            attach("operator type", (op)->type);
          }
        }

        if (op_list.count > 1)
        {
          if (hasSilentError())
          {
            wipeError();
            if (attempt == op_list.count-1 && !value)
            {
              reportError(in->op, "found no suitable overload");
              attach("available_overloads", op_list.count, op_list.items, printOptionPrintType());
            }
          }
        }
      }
    }
  }
  NULL_WHEN_ERROR(value);
  return value;
}

inline Term *
buildWithState(ProofState *state, Ast *body)
{
  Term *value = buildWithNewAssets(state->typer, state->asset_count, 0, state->assets, body, state->goal);
  if (noError())
  {
    for (auto chain = state->rewrites; chain; chain = chain->next)
    {
      value = newRewrite(chain->eq_proof, value, chain->path, chain->right_to_left);
    }
  }
  return value;
}

internal Term *
buildSubst(Typer *typer, SubstAst *in, Term *goal0)
{
  // todo #cleanup I think there is a super structure here: we add asset, and we
  // change the goal. Currently we use the stack and recursion to keep track of
  // that but maybe the typer can help with that, and we just push stuff onto it.

  struct Substitution {
    Term *to_rewrite;
    Term *eq_proof;
    b32   right_to_left;
  };

  Term *value = 0;
  Arena *arena = temp_arena;
  i32           sub_cap       = 16; // todo: #grow
  i32           sub_count     = 0;
  Substitution *substitutions = pushArray(arena, sub_cap, Substitution);

  ProofState state_ = newProofState(typer, goal0);
  auto state = &state_;

  for (i32 expr_i=0; expr_i < in->count && noError(); expr_i++)
  {
    // building expressions and storing substitutions
    Ast *to_rewrite_ast = in->to_rewrite[expr_i];
    if (Term *to_rewrite = buildTerm(typer, to_rewrite_ast, hole))
    {
      Pointer *eq_proof      = 0;
      b32      right_to_left = 0;
      for (Scope *scope = typer->scope; scope && !eq_proof; scope = scope->outer)
      {
        for (i32 pointer_i=0; pointer_i < scope->param_count && !eq_proof; pointer_i++)
        {
          Pointer *pointer = scope->pointers[pointer_i];
          if (auto [l,r]= getEqualitySides(pointer->type, false))
          {
            b32 equal_lhs = equal(l, to_rewrite);
            b32 equal_rhs = equal(r, to_rewrite);
            if (equal_lhs || equal_rhs)
            {
              eq_proof      = pointer;
              right_to_left = equal_rhs;
              pointer->ignored = true;

              substitutions[sub_count++] = {to_rewrite, eq_proof, right_to_left};
              assert(sub_count <= sub_cap);
            }
          }
        }
      }
    }
  }

  if (noError())
  {
    for (i32 sub_i = 0; sub_i < sub_count; sub_i++)
    {
      auto [to_rewrite, eq_proof, right_to_left] = substitutions[sub_i];
      for (Scope *scope = typer->scope; scope; scope = scope->outer)
      {
        // search the scope for stuff to rewrite
        for (i32 pointer_i=0; pointer_i < scope->param_count; pointer_i++)
        {
          Pointer *pointer = scope->pointers[pointer_i];
          if (!pointer->ignored)
          {
            assert(pointer != eq_proof);
            if (SearchOutput search = searchExpression(to_rewrite, pointer->type))
            {
              Term *asset = newRewrite(eq_proof, pointer, search.path, !right_to_left);
              pointer->ignored = true;
              addAsset(state, asset);
            }
          }
        }
      }

      for (i32 asset_i=0; asset_i < state->asset_count; asset_i++)
      {
        // search the existing assets we just created
        Term *asset = state->assets[asset_i];
        if (SearchOutput search = searchExpression(to_rewrite, asset->type))
        {
          state->assets[asset_i] = newRewrite(eq_proof, asset, search.path, !right_to_left);
        }
      }
    }

    for (i32 sub_i = 0; sub_i < sub_count; sub_i++)
    {
      auto [to_rewrite, eq_proof, right_to_left] = substitutions[sub_i];
      if (SearchOutput search = searchExpression(to_rewrite, state->goal))
      {
        addRewrite(state, eq_proof, search.path, right_to_left);
      }
    }

    value = buildWithState(state, in->body);
  }
  return value;
}

inline Identifier *
newIdentifier(Token *token)
{
  return newAst(temp_arena, Identifier, token);
}

inline Identifier *
newIdentifier(char *name)
{
  Token token = newToken(name);
  return newAst(temp_arena, Identifier, &token);
}

inline Term *
buildAlgebraNorm(Typer *typer, AlgebraNormAst *ast, Term *goal0)
{
  Term *value = 0;
  ProofState state_ = newProofState(typer, goal0);
  auto state = &state_;

  // todo: well this goal search isn't recursive;
  if (Composite *goal = castTerm(goal0, Composite))
  {
    for (i32 arg_i=0; arg_i < goal->arg_count; arg_i++)
    {
      Term *arg = goal->args[arg_i];
      Term *T = arg->type;
      Algebra *algebra = 0;
      for (AlgebraDatabase *algebras = global_state.algebras;
           algebras && !algebra;
           algebras = algebras->tail)
      {
        Algebra *it = &algebras->head;
        if (T == it->type) algebra = it;
      }

      if (algebra)
      {
        Transformation transform = {.term=arg};
        algebraNorm(algebra, &transform);
        if (transform.eq_proof)
        {
          addRewrite(state, transform.eq_proof, treePath(arg_i), false);
        }
      }
    }
  }

  value = buildWithState(state, ast->body);
  return value;
}

internal Term *
buildNameOnlyArrowType(Typer *typer, ArrowAst *in, Term *goal0)
{
  Arrow *out = 0;
  Arena *arena = temp_arena;
  Arrow *goal = castTerm(goal0, Arrow);
  if (goal)
  {
    if (in->param_count == goal->param_count)
    {
      out = pushCopy(arena, goal);
      out->param_names = in->param_names;
    }
    else
    {
      if (expectedWrongType(typer)) silentError();
      else reportError(in, "incorrect number of names given");
    }
  }
  else
  {
    if (goal0 == hole)
      reportAmbiguousError(typer, in, "illegal usage of name-only arrow syntax without expected type");
    else
      reportWrongTypeError(typer, in, "illegal usage of name-only arrow syntax since the goal is not an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare internal BuildTerm
buildTerm(Typer *typer, Ast *in0, Term *goal0)
{
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;

  assert(goal0);
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
      value = buildComposite(typer, (CompositeAst*)in0, goal0);
    } break;

    case Ast_Identifier:
    {
      Identifier *in = castAst(in0, Identifier);
      Token *name = &in->token;
      if (goal0 == rea.U32)
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
              Term *slot_value = globals->terms[value_id];
              if (matchType((slot_value)->type, goal0))
              {
                if (value)
                {// ambiguous
                  if (expectedAmbiguous(typer)) silentError();
                  else
                  {
                    tokenError(name, "not enough type information to disambiguate global name");
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
                attach("expected_type", goal0);
                if (globals->count == 1)
                {
                  attach("actual_type", (globals->terms[0])->type);
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
    case Ast_QuestionMark:
    {
      Solver solver = {.typer=typer, .use_global_hints=true, .try_reductio=try_reductio};
      value = solveGoal(&solver, goal0);
      if (value)
      {
        if (in0->kind == Ast_QuestionMark)
        {
          print(0, value, printOptionPrintType());
          print(0, "\n");
        }
      }
      else
      {
        reportError(in0, "please provide an expression here");
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

      if (noError())
      {
        Scope *scope = typer->scope = newScope(typer->scope, param_count);
        extendBindings(typer);
        out->param_types = pushArray(arena, param_count, Term*);
        for (i32 i=0; i < param_count && noError(); i++)
        {
          if (Term *param_type = buildTerm(typer, in->param_types[i], hole))
          {
            out->param_types[i] = toAbstractTerm(arena, param_type, getScopeDepth(scope->outer));
            String name = in->param_names[i];
            scope->pointers[i] = newStackPointer(name, scope->depth, i, param_type);
            addLocalBinding(typer, name, i);
          }
        }

        if (noError())
        {
          value = out;
          // :no-output-type
          if (in->output_type)
          {
            if (Term *output_type = buildTerm(typer, in->output_type, hole))
            {
              out->output_type = toAbstractTerm(arena, output_type, getScopeDepth(scope->outer));
            }
          }
          else
          {
            out->output_type = hole;
          }
        }
        unwindBindingsAndScope(typer);
      }
    } break;

    case Ast_AccessorAst:
    {
      AccessorAst *in = (AccessorAst *)(in0);
      if (Term *record0 = buildTerm(typer, in->record, hole))
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
          Union *uni = getUnionOrPolyUnion((record0)->type);
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
      Term *type = goal0;
      if (in->signature)
      {
        if (isNameOnlyArrowType(in->signature))
        {
          type = buildNameOnlyArrowType(typer, in->signature, goal0);
        }
        else
        {
          type = buildTerm(typer, in->signature, hole);
        }
      }

      if (noError())
      {
        if (Arrow *signature = castTerm(type, Arrow))
        {
          value = buildFunctionGivenSignature(typer, signature, in->body, 0, in);
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
      RewriteAst *in  = castAst(in0, RewriteAst);
      if (goal0->kind == Term_Hole)
      {
        reportError(in0, "we do not know what the goal is, so nothing to rewrite");
      }
      else if (Term *eq_or_proof = buildTerm(typer, in->eq_or_proof, hole))
      {
        Term *eq_proof = 0;
        Term *eq       = 0;
        if (isEquality(eq_or_proof))
        {
          eq = eq_or_proof;
          eq_proof = seekGoal(Solver{.typer=typer}, eq_or_proof);
          if (!eq_proof)
          {
            reportError("cannot find the proof for this proposition in scope");
            attach("equality", eq_or_proof);
          }
        }
        else
        {
          eq_proof = eq_or_proof;
          eq       = eq_or_proof->type;
          if (!isEquality(eq))
          {
            reportError(in->eq_or_proof, "please provide a proof of equality for rewrite");
            attach("got", eq);
          }
        }

        if (noError())
        {
          auto [lhs, rhs] = getEqualitySides(eq);
          Term *from = in->right_to_left ? rhs : lhs;
          Term *to   = in->right_to_left ? lhs : rhs;
          if (in->in_expression)
          {
            if (Term *in_expression = buildTerm(typer, in->in_expression, hole).value)
            {
              if (SearchOutput search = searchExpression(from, in_expression->type))
              {
                b32 right_to_left = !in->right_to_left;  // since we rewrite the body, not the goal.
                Term *asset = newRewrite(eq_proof, in_expression, search.path, right_to_left);
                String name = {};
                Pointer *var = castTerm(in_expression, Pointer);
                if (var && var->is_stack_pointer)
                {
                  name = var->stack.name;
                }
                value = buildWithNewAsset(typer, name, asset, in->body, goal0);
              }
              else
              {
                reportError(in0, "cannot find a place to apply the rewrite");
                attach("substitution", eq);
                attach("in_expression_type", (in_expression)->type);
              }
            }
          }
          else
          {
            SearchOutput search = searchExpression(from, goal0);
            if (search.found)
            {
              Term *new_goal = rewriteTerm(from, to, search.path, goal0);
              if (Term *body = buildTerm(typer, in->body, new_goal))
              {
                value = newRewrite(eq_proof, body, search.path, in->right_to_left, new_goal);
              }
            }
            else
            {
              reportError(in0, "cannot find a place to apply the rewrite");
              attach("substitution", eq);
            }
          }
        }
      }
    } break;

    case Ast_GoalTransform:
    {
      if (goal0 == hole)
      {
        reportAmbiguousError(typer, in0, "cannot transform because we don't know what the goal is");
      }
      else
      {
      GoalTransform *in = castAst(in0, GoalTransform);
      Term     *new_goal      = 0;
      Term     *eq_proof      = 0;
      TreePath *rewrite_path  = 0;
      b32       right_to_left = false;

      if (NormalizeMeAst *in_new_goal = castAst(in->new_goal, NormalizeMeAst))
      {// just normalize the goal, no need for tactics (for now).
        Term *norm_goal = normalize(goal0, in_new_goal->norm_options);
        if (checkFlag(in->flags, AstFlag_Generated) &&
            equal(goal0, norm_goal))
        {// superfluous auto-generated transforms.
          value = buildTerm(typer, in->body, goal0).value;
          recursed = true;
        }
        else
        {
          eq_proof = newComputation_(goal0, norm_goal);
          new_goal = norm_goal;
          rewrite_path = 0;
        }
      }
      else if ((new_goal = buildTerm(typer, in->new_goal, hole)))
      {
        if (equal(new_goal->type, goal0->type))
        {
          CompareTerms compare = compareTerms(arena, goal0, new_goal);
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
            Term *from = subExpressionAtPath(goal0, compare.diff_path);
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
                      hints = addHint(temp_arena, hints, slot->terms[i]);
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
                if ((eq_proof = buildTerm(typer, in->hint, hole)))
                {
                  hints = addHint(temp_arena, hints, eq_proof);
                }
              }
            }

            if (noError())
            {
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
                }
              }
            }
          }
        }
        else
        {
          reportError(in, "new goal does not have the same type as old goal!");
          attach("new_goal->type", new_goal->type);
          attach("goal0->type", goal0->type);
        }
      }

      if (noError() && !recursed)
      {
        if (Term *body = buildTerm(typer, in->body, new_goal).value)
        {
          value = newRewrite(eq_proof, body, rewrite_path, right_to_left);
        }
      }

      if (in->print_proof && eq_proof)
      {
        print(0, eq_proof);
        print(0, "\n");
      }
      }
    } break;

    case Ast_Let:
    {
      Let  *in = castAst(in0, Let);
      Term *type_hint = hole;
      if (in->type && in->type->kind != Ast_NormalizeMeAst)
      {
        type_hint = buildTerm(typer, in->type, hole);
      }
      if (noError())
      {
        if (Term *rhs0 = buildTerm(typer, in->rhs, type_hint))
        {
          Term *rhs = rhs0;
          Term *rhs_type = (type_hint->kind == Term_Hole) ? rhs->type : type_hint;

          if (in->type)
          {// type coercion
            if (NormalizeMeAst *in_type = castAst(in->type, NormalizeMeAst))
            {
              Term *norm_rhs_type = normalize(rhs_type, in_type->norm_options);
              if (checkFlag(in->flags, AstFlag_Generated) &&
                  equal(rhs_type, norm_rhs_type))
              {// superfluous auto-generated transforms.
                value = buildTerm(typer, in->body, goal0).value;
                recursed = true;
              }
              else
              {
                Term *computation = newComputation_(norm_rhs_type, rhs_type);
                rhs_type = norm_rhs_type;
                rhs = newRewrite(computation, rhs, 0, false);
              }
            }
          }

          if (!recursed)
          {
            String lhs = in->lhs;
            if (!lhs)
            {
              if (Pointer *pointer = castTerm(rhs0, Pointer))
              {
                if (pointer->is_stack_pointer)
                {
                  // pointer->ignored = true;  // NOTE: rhs could be rhs0
                  lhs = pointer->stack.name;
                }
              }
            }
            value = buildWithNewAsset(typer, lhs, rhs, in->body, goal0);
          }
        }
      }
    } break;

    case Ast_ForkAst:
    {
      ForkAst *fork = castAst(in0, ForkAst);
      value = buildFork(typer, fork, goal0);
      recursed = true;
    } break;

    case Ast_CtorAst:
    {
      reportError(in0, "please use this constructor syntax as an operator");
    } break;

    case Ast_SeekAst:
    {
      SeekAst *in = castAst(in0, SeekAst);
      Term *proposition = goal0;
      if (in->proposition)
      {
        proposition = buildTerm(typer, in->proposition, hole).value;
      }

      if (noError())
      {
        value = seekGoal(Solver{.typer=typer}, proposition);
        if (!value)
          reportError(in0, "cannot find a matching proof in scope");
      }
    } break;

    // todo: remove this syntax, use tags instead.
    case Ast_OverloadAst:
    {
      OverloadAst *in = castAst(in0, OverloadAst);
      if (GlobalBinding *lookup = lookupGlobalNameSlot(in->function_name, false))
      {
        pushItemsAs(arena, tags, in->distinguisher);
        value = getOverloadFromTags(lookup, 1, tags);
      }
      else
      {
        reportError(in, "no function named \"%s\" found", in->function_name);
      }

      if (!value)
      {
        reportError(in, "found no overload corresponding to distinguisher");
      }
    } break;

    case Ast_TypedExpression:
    {
      TypedExpression *in = (TypedExpression *)(in0);
      if (Term *type = buildTerm(typer, in->type, hole).value)
      {
        value = buildTerm(typer, in->expression, type).value;
      }
    } break;

    case Ast_ReductioAst:
    {
      todoIncomplete;
      if (!value)
        reportError(in0, "no contradiction found");
    } break;

    case Ast_ListAst:
    {
      // NOTE: The plan is to just lean on the typechecking as much as possible.
      ListAst *in = (ListAst *)in0;
      Ast *list = in->tail;
      if (in->count == 0)
      {
        assert(!in->tail);
        CompositeAst *nil = newAst(arena, CompositeAst, &in->token);
        nil->op = newIdentifier("nil");
        list = nil;
      }
      else
      {
        i32 loop_start = in->count-1;
        if (!in->tail)
        {
          Ast *item = in->items[in->count-1];
          CompositeAst *final_item = newAst(arena, CompositeAst, &item->token);
          final_item->op        = newIdentifier("single");
          final_item->arg_count = 1;
          pushItems(arena, final_item->args, item);
          list = final_item;

          loop_start = in->count-2;
        }

        for (i32 i = loop_start; i >= 0; i--)
        {
          Ast *item = in->items[i];
          CompositeAst *new_list = newAst(arena, CompositeAst, &item->token);
          new_list->op        = newIdentifier("cons");
          new_list->arg_count = 2;
          pushItems(arena, new_list->args, item, list);
          list = new_list;
        }
      }

      recursed = true;
      value = buildTerm(typer, list, goal0);
    } break;

    case Ast_Invert:
    {
      Invert *in = (Invert *)in0;
      if (Term *pointer0 = buildTerm(typer, in->pointer, hole))
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
              value = buildWithNewAssets(typer, eq_count, 0, eqs, in->body, goal0);
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

    case Ast_SubstAst:
    {
      SubstAst *in = (SubstAst *)in0;
      value = buildSubst(typer, in, goal0);
    } break;

    case Ast_AlgebraNormAst:
    {
      AlgebraNormAst *in = (AlgebraNormAst *)in0;
      value = buildAlgebraNorm(typer, in, goal0);
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// typecheck if needed
    Term *actual = value->type;
    if (should_check_type && !recursed)
    {
      if (!matchType(actual, goal0))
      {
        if (expectedWrongType(typer)) silentError();
        else
        {
          reportError(in0, "actual type differs from expected type");
          attach("got", actual);

#if 0
          DEBUG_LOG_compare = 1;
          matchType(actual, goal0);
          DEBUG_LOG_compare = 0;
#endif
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
        attach("GOAL", goal0);

        StartString start = startString(error_buffer);
        print(error_buffer, "\n");
        prettyPrintScope(error_buffer, typer->scope);
        attach("SCOPE", endString(start));

        start = startString(error_buffer);
      }
    }
    value = 0;
  }
  else
  {
    assert(value);
  }

  if (serial == 1389966)
    breakhere;

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
  assert(goal->kind != Term_Hole);
  Arena *arena = temp_arena;
  Fork *out = 0;
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  if (Term *subject = buildTerm(typer, in->subject, hole))
  {
    auto &fixpoint = current_global_fixpoint;
    Pointer *save_global_fork_subject = fixpoint ? fixpoint->fork_subject : 0;
    if (fixpoint)
    {
      if (fixpoint->fun)
      {
        // NOTE: massive #hack to mark this subject as "should be reducing when
        // calling recursively".
        if (fixpoint->fork_subject)
        {
          breakhere;  // STUDY: multiple fork subjects, what to do...?
        }
        else
        {
          i32 param_count = getParameterCount(fixpoint->fun);
          for (i32 param_i=0; param_i < param_count; param_i++)
          {
            Pointer *arg = fixpoint->args[param_i];
            if (subject == arg)
            {
              fixpoint->fork_subject = arg;
              break;
            }
          }
        }
      }
    }

    if (Union *uni = getUnionOrPolyUnion(subject->type))
    {
      Term **ordered_cases = pushArray(arena, uni->ctor_count, Term *, true);

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
            if (!ordered_cases[i])
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
            if (ordered_cases[ctor_i])
            {
              reportError(in->cases[input_case_i], "fork case handled twice");
              attach("constructor", getConstructorName(uni, ctor_i));
            }
            else
            {
              typer->try_reductio = true;
              ordered_cases[ctor_i] = buildTerm(typer, in->cases[input_case_i], goal);
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

      if (noError())
      {
        if (in->case_count == uni->ctor_count)
        {
          out = newFork(subject, in->case_count, ordered_cases, goal);
        }
        else
        {
          reportError(in, "wrong number of cases");
          StartString start = startString(error_buffer);
          for (i32 ctor_i=0; ctor_i < uni->ctor_count; ctor_i++)
          {
            if (!ordered_cases[ctor_i])
            {
              print(error_buffer, getConstructorName(uni, ctor_i));
              print(error_buffer, ", ");
            }
          }
          attach("constructors_remaining", endString(start));
        }
      }
    }
    else
    {
      reportError(in->subject, "cannot fork expression of this type");
      attach("type", subject->type);
    }

    if (fixpoint) fixpoint->fork_subject = save_global_fork_subject;
  }
  if (noError())
  {
    for (i32 id=0; id < in->case_count; id++)
      assert(in->cases[id]);
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline Term *
parseAndBuildTemp(Typer *typer, Term *expected_type=hole)
{
  Term *out = 0;
  if (Ast *ast = parseExpression())
  {
    out  = buildTerm(typer, ast, expected_type);
  }
  return out;
}

inline Term *
parseAndBuildGlobal(Typer *typer, Term *expected_type=hole)
{
  Term *out = 0;
  if (Ast *ast = parseExpression())
  {
    if ((out = buildTerm(typer, ast, expected_type)))
    {
      out = copyToGlobalArena(out);
    }
  }
  return out;
}

internal void
addBuiltinTerm(Term *term, String name={})
{
  String builtin_name = name ? name : term->global_name->string;
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

inline void
addGlobalHint(Term *hint)
{
  HintDatabase *new_hint = pushStruct(global_state.top_level_arena, HintDatabase);
  new_hint->head = hint;
  new_hint->tail = global_state.hints;
  global_state.hints = new_hint;
}

forward_declare internal Term *
buildUnion(Typer *typer, UnionAst *in, Token *global_name)
{
  assert(global_name);
  Arena *arena = global_state.top_level_arena;
  Union *uni = newTerm(arena, Union, rea.Type);
  b32 UNUSED_VAR serial = DEBUG_SERIAL++;

  i32 ctor_count = in->ctor_count;
  uni->ctor_count = ctor_count;
  Arrow **ctor_signatures = pushArray(temp_arena, ctor_count, Arrow *);
  uni->constructors = pushArray(arena, ctor_count, Constructor *);

  Arrow *uni_signature  = 0;
  i32    poly_count     = 0;
  i32    non_poly_count = 0;
  if (in->signature)
  {
    if (Term *uni_params0 = buildGlobalTerm(typer, in->signature, hole))
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
      if (Term *sig0 = buildGlobalTerm(typer, ast_sig, hole))
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

  for (i32 ctor_i=0; noError() && ctor_i < ctor_count; ctor_i++)
  {
    Arrow *ctor_sig = ctor_signatures[ctor_i];
    Constructor *ctor = newTerm(arena, Constructor, ctor_sig);
    ctor->index = ctor_i;
    ctor->name  = in->ctor_names[ctor_i];
    if (uni_signature)
    {
      addGlobalBinding(&in->ctor_names[ctor_i], ctor);
    }
    else
    {
      ctor_sig->output_type = uni;
      Term *term_to_bind = ctor;
      if (ctor_sig->param_count == 0)
      {
        // todo: need to rethink "no-arg composite" thing
        term_to_bind = newComposite(ctor, 0, 0);
        term_to_bind = copyToGlobalArena(term_to_bind);
      }
      addGlobalBinding(&in->ctor_names[ctor_i], term_to_bind);
    }
    uni->constructors[ctor_i] = ctor;
    addGlobalHint(ctor);
  }

  b32 is_builtin = checkFlag(in->flags, AstFlag_IsBuiltin);
  if (is_builtin && noError())
  {
    addBuiltinTerm(uni, in->builtin_name);
    for (i32 i=0; i < uni->ctor_count; i++)
    {
      addBuiltinTerm(uni->constructors[i]);
    }
  }

  NULL_WHEN_ERROR(uni);
  return uni;
}

internal Function *
buildGlobalFunction(Typer *typer, FunctionAst *in)
{
  i32 unused_var serial = DEBUG_SERIAL;
  pushContext(in->token.string, true);
  Function *out = 0;
  if (Term *type = buildTerm(typer, in->signature, hole))
  {
    type = copyToGlobalArena(type);
    if (Arrow *signature = castTerm(type, Arrow))
    {
      out = buildFunctionGivenSignature(typer, signature, in->body, &in->token, in);
      if (out)
      {
        // :persistent-global-function
        if (checkFlag(in->function_flags, FunctionFlag_is_global_hint))
        {
          addGlobalHint(out);
        }
        if (checkFlag(in->flags, AstFlag_IsBuiltin))
        {
          addBuiltinTerm(out, in->builtin_name);
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
interpretTopLevel(EngineState *state)
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
    i32 unused_var serial = DEBUG_SERIAL++;

    // NOTE: We don't wanna persist the typer across top-level forms, even if it
    // happens to work.
    Typer  typer_ = {};
    Typer *typer  = &typer_;
    if (should_fail_active)
    {
      setFlag(&typer->expected_errors, ExpectError_WrongType);
    }

    switch (token_.kind)
    {
      case Token_Directive:
      {
        if (equal(token, "load"))
        {
          pushContext("load");
          Token file = nextToken();
          if (file.kind != Token_StringLiteral)
            tokenError("expect \"FILENAME\"");
          else
          {
            String load_path = print(arena, TK->directory);
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
        else if (equal(token, "print"))
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
          else if (optionalString("full_scope"))
          {
            print_full_scope = !optionalString("off");
          }
          else if (optionalString("full_list"))
          {
            print_full_list = !optionalString("off");
          }
        }
        else if (equal(token, "should_fail"))
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
        else if (equal(token, "debug"))
        {
          b32 value = !optionalString("off");
          global_state.top_level_debug_mode = value;
          DEBUG_LOG_compare = value;
        }
      } break;

      case Token_Keyword_test_eval:
      {
        if (Term *expr = parseAndBuildTemp(typer))
        {
          normalize(expr);
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
          Term *norm = normalize(expr);
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
        Term *expected_type = hole;
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
              Term *lhs = normalize(eq->args[1]);
              Term *rhs = normalize(eq->args[2]);
              if (!equal(lhs, rhs))
              {
                tokenError(token, "equality cannot be proven by computation");
                Term *lhs = normalize(eq->args[1]);
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
          const i32 function_count = 8;
          Term **functions[function_count] = {
            &algebra->add, &algebra->addCommutative, &algebra->addAssociative,
            &algebra->mul, &algebra->mulCommutative, &algebra->mulAssociative,
            &algebra->mulDistributiveLeft, &algebra->mulDistributiveRight,
          };
          const char *function_names[function_count] = {
            "+", "addCommutative", "addAssociative",
            "*", "mulCommutative", "mulAssociative",
            "mulDistributive", "mulDistributive",
          };
          const char *function_tags[function_count] = {
            0, 0, 0,
            0, 0, 0,
            "left", "right"
          };

          for (i32 fun_i=0; fun_i < function_count && noError(); fun_i++)
          {
            String function_name = toString(function_names[fun_i]);
            if (GlobalBinding *lookup = lookupGlobalNameSlot(function_name, false))
            {
              assert(type->global_name);
              i32     tag_count = 0;
              String *tags      = 0;
              if (function_tags[fun_i])
              {
                tag_count = 2;
                pushItems(arena, tags, type->global_name->string, toString(function_tags[fun_i]));
              }
              else
              {
                tag_count = 1;
                pushItems(arena, tags, type->global_name->string);
              }

              if (Term *function = getOverloadFromTags(lookup, tag_count, tags))
              {
                *functions[fun_i] = function;
              }
              else
              {
                reportError(token, "cannot find necessary function for the algebra");
                attach("function_name", function_name);
              }
            }
          }
        }
      } break;

      case Token_Keyword_define:
      {
        pushContext("define IDENTIFIER PARAMETERS := EXPRESSION");
        FunctionAst *fun = newAst(arena, FunctionAst, token);
        setFlag(&fun->function_flags, FunctionFlag_no_expand);
        if (requireIdentifier())
        {
          Token name = *lastToken();
          if ((fun->signature = parseArrowType(true)))
          {
            if (requireKind(Token_ColonEqual))
            {
              if ((fun->body = parseExpression()))
              {
                if (Term *term = buildTerm(typer, fun, hole))
                {
                  term = copyToGlobalArena(term);
                  addGlobalBinding(&name, term);
                }
              }
            }
          }
        }
        popContext();
      } break;

      default:
      {
        if (isIdentifier(token))
        {
          Token after_name = nextToken();

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

    eatCharRepeatedly(';');
    token_ = nextToken();
  }
}

forward_declare internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  Arena *arena = state->top_level_arena;
  b32 success = true;
#define REA_PROFILE 1
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

    Tokenizer *tk_save = TK;
    Tokenizer  tk_ = {};
    Tokenizer *tk  = &tk_;
    initTokenizer(tk, read.content, input_path.directory);

    interpretTopLevel(state);
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

    TK = tk_save;
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
    interpretFile(&global_state, path, false);

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
  size_t  temp_arena_size = megaBytes(16);
  temp_arena_base = platformVirtualAlloc(temp_arena_base, top_level_arena_size);
  temp_arena_ = newArena(temp_arena_size, temp_arena_base);

  char *files[] = {
    "../data/test.rea",
    // "../data/natp.rea",
    "../data/z-slider.rea",
    "../data/frac.rea",
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

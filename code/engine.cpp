/*
  General Todos: 
  - #cleanup Replace all token <-> string comparison with keyword checks.
  - #tool defer
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"
#include "tokenization.cpp"

global_variable Builtins builtins;
global_variable Term dummy_function_being_built;
global_variable Term  holev_ = {.cat = Term_Hole};
global_variable Term *holev = &holev_;

inline String
globalNameOf(Term *term)
{
  if (term->global_name)
    return term->global_name->string;
  else
    return {};
}

inline void
print(MemoryArena *buffer, Stack *stack)
{
  print(buffer, "[");
  while (stack)
  {
    print(buffer, "[");
    for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
    {
      print(buffer, stack->items[arg_id], PrintOptions{PrintFlag_PrintType});
      if (arg_id != stack->count-1)
        print(buffer, ", ");
    }
    print(buffer, "]");
    stack = stack->outer;
    if (stack)
      print(buffer, ", ");
  }
  print(buffer, "]");
}

inline void dump(Stack *stack) {print(0, stack);}

internal Term *
fillHole(MemoryArena *arena, Typer *env, Term *goal)
{
  Term *out = 0;
  if (Composite *eq = castTerm(goal, Composite))
  {
    if (eq->op == &builtins.equal->t)
    {
      Term *lhs_norm = normalize(temp_arena, env, eq->args[1]);
      Term *rhs_norm = normalize(temp_arena, env, eq->args[2]);
      if (equal(env, lhs_norm, rhs_norm))
      {
        out = newComputation(arena, eq->args[1], eq->args[2]);
      }
    }
  }
  return out;
}

inline Term *
newEquality(MemoryArena *arena, Typer *env, Term *lhs, Term *rhs)
{
  Composite *eq = newTerm(arena, Composite, &builtins.Set->t);
  allocateArray(arena, 3, eq->args);
  eq->op        = &builtins.equal->t;
  eq->arg_count = 3;
  eq->args[0]   = getType(arena, env, lhs);
  eq->args[1]   = lhs;
  eq->args[2]   = rhs;
  return &eq->t;
}

// todo #typesafe error out when the sides don't match
forward_declare inline Term *
newComputation(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Computation *out = newTerm(arena, Computation, 0);
  out->lhs = lhs;
  out->rhs = rhs;
  return &out->t;
}

inline b32
isEquality(Term *eq0)
{
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == &builtins.equal->t)
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
    if (eq->op == &builtins.equal->t)
      out = TermPair{eq->args[1], eq->args[2]};
  }
  assert(!must_succeed || out)
  return out;
}

inline b32
isSequenced(Ast *ast)
{
  b32 out = false;
  switch (ast->cat)
  {
    case AC_RewriteAst:
    case AC_Let:
    case AC_ForkAst:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

inline b32
isSequenced(Term *term)
{
  b32 out = false;
  switch (term->cat)
  {
    case Term_Rewrite:
    case Term_Fork:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

#if 0
internal b32
isFree(Term *in0, i32 offset)
{
  b32 out = false;
  b32 debug = false;
  if (debug && global_debug_mode)
  {debugIndent(); dump("isFree: "); dump(in0); dump(" with offset: "); dump(offset); dump();}

  switch (in0->cat)
  {
    case Term_FakeTerm:
    {
      // FakeTerm *in = castTerm(in0, FakeTerm);
      todoIncomplete;
    } break;

    case Term_Variable:
    {
      Variable *in = castTerm(in0, Variable);
      out = in->stack_frame >= offset;
    } break;

    case Term_Composite:
    {
      Composite *in = castTerm(in0, Composite);
      if (isFree(in->op, offset)) out = true;
      else
      {
        for (s32 arg_id=0; arg_id < in->arg_count; arg_id++)
        {
          if (isFree(in->args[arg_id], offset))
          {
            out = true;
            break;
          }
        }
      }
    } break;

    case Term_Arrow:
    {
      Arrow *in = castTerm(in0, Arrow);
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        if (isFree(in->param_types[param_id], offset+1))
        {
          out = true;
          break;
        }
      }
      if (!out && in->output_type)
        out = isFree(in->output_type, offset+1);
    } break;

    case Term_Accessor:
    {
      Accessor *in = castTerm(in0, Accessor);
      out = isFree(in->record, offset);
    } break;

    case Term_Function:
    {
      Function *in = castTerm(in0, Function);
      // todo #hack
      out = in->id.v == 0 && in->stack == 0;
    } break;

    case Term_Computation:
    {
      Computation *in = castTerm(in0, Computation);
      out = isFree(in->lhs, offset);
      if (!out) out = isFree(in->rhs, offset);
    } break;

    case Term_Constant:
    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    {out = false;} break;

    case Term_Rewrite:
    {
      Rewrite *in = castTerm(in0, Rewrite);
      if (isFree(in->eq_proof, offset)) out = true;
      else if (isFree(in->body, offset)) out = true;
    } break;

    case Term_Fork:
    {out = true;} break;

    case Term_Hole:
    {todoIncomplete;}
  }

  if (debug && global_debug_mode) {debugDedent(); dump("=> "); dump(out); dump();}
  return out;
}

inline b32 isGround(Term *in0) {return !isFree(in0, 0);}
#endif

inline Term *
lookupStack(Stack *stack, i32 stack_delta, i32 id)
{
  Term *out0 = 0;
  for (i32 delta = 0; delta < stack_delta; delta++)
  {
    stack = stack->outer;
    if (!stack)
    {
      dump(stack); dump();
      invalidCodePath;
    }
  }
  if (id < stack->count)
    out0 = stack->items[id];
  else
  {
    dump(stack); dump();
    invalidCodePath;
  }
  assert(out0);
  return out0;
}

#if 0
inline Term *
lookupStack(Environment *env, Variable *var)
{
  lookupStack(env, var->stack_delta, var->id);
}
#endif

inline Composite *
makeFakeRecord(MemoryArena *arena, Term *parent, Constructor *ctor)
{
  Composite *record = 0;
  Arrow *ctor_sig = castTerm(ctor->type, Arrow);
  i32 param_count = ctor_sig->param_count;
  record = newTerm(arena, Composite, 0);
  record->op        = &ctor->t;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term*);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = ctor_sig->param_names[field_id].string;
    Accessor *accessor = newTerm(arena, Accessor, 0);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    record->args[field_id] = &accessor->t;
  }
  return record;
}

inline Composite *
castRecord(Term *term)
{
  Composite *out = 0;
  if (Composite *composite = castTerm(term, Composite))
    if (Constructor *ctor = castTerm(composite->op, Constructor))
      out = composite;
  return out;
}

internal b32
isPotentialRecord(Term *in)
{
  switch (in->cat)
  {
    case Term_Variable:
    case Term_Accessor:
    case Term_Composite:
    {return true;} break;

    case Term_Hole:
    case Term_Rewrite:
    case Term_Arrow:
    case Term_Computation:
    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Function:
    case Term_Fork:
    {return false;} break;
  }
}

inline i32 getStackDepth(Typer *env) {return (env->type_stack ? env->type_stack->depth : 0);}

internal Constructor *
getMappedConstructor(Typer *env, Term *in0)
{
  Constructor *ctor = 0;
  i32 serial = global_debug_serial++;
  b32 debug = true;
  if (debug && global_debug_mode)
  {debugIndent(); DUMP("getMappedConstructor(", serial, "): ", in0, "\n");}
  if (env && isPotentialRecord(in0))
  {
    for (ConstructorMap *map = env->map; map; map=map->next)
    {
      Term *rebased_term = rebase(temp_arena, map->term, getStackDepth(env) - map->depth);
      if (equal(0, in0, rebased_term))
      {
        ctor = map->ctor;
        break;
      }
    }
  }
  if (debug && global_debug_mode)
  {debugDedent(); DUMP("=> ", &ctor->t, "\n");}
  return ctor;
}

internal Constructor *
getConstructor(Typer *env, Term *in0)
{
  Constructor *ctor = 0;
  if (Composite *in = castTerm(in0, Composite))
    ctor = castTerm(in->op, Constructor);
  if (!ctor)
    ctor = getMappedConstructor(env, in0);
  return ctor;
}

internal Composite *
toRecord(MemoryArena *arena, Typer *env, Term *in0)
{
  Composite *out = 0;
  if (Composite *in = castRecord(in0))
    out = in;
  if (!out)
  {
    if (Constructor *ctor = getMappedConstructor(env, in0))
      out = makeFakeRecord(arena, in0, ctor);
  }
  return out;
}

internal Term *
rewriteTerm(MemoryArena *arena, Term *rhs, TreePath *path, Term *in0)
{
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyStruct(arena, in);
    if (path->first == -1)
    {
      out->op = rewriteTerm(arena, rhs, path->next, in->op);
    }
    else
    {
      assert(path->first >= 0 && path->first < out->arg_count);
      allocateArray(arena, out->arg_count, out->args);
      for (i32 arg_id=0; arg_id < out->arg_count; arg_id++)
      {
        if (arg_id == (i32)path->first)
        {
          out->args[arg_id] = rewriteTerm(arena, rhs, path->next, in->args[arg_id]);
        }
        else
          out->args[arg_id] = in->args[arg_id];
      }
    }
    return &out->t;
  }
  else
  {
#if 0
    if (!equalB32(in0, lhs))
    {
      dump("actual:   "); dump(in0); dump();
      dump("expected: "); dump(lhs); dump();
      invalidCodePath;
    }
#endif
    return rhs;
  }
}


forward_declare inline Term *
getType(MemoryArena *arena, Typer *env, Term *in0)
{
  Term *out0 = 0;
  if (in0->type)
    out0 = in0->type;
  else
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        out0 = lookupStack(env->type_stack, in->stack_delta, in->id);
        out0 = rebase(arena, out0, in->stack_delta);
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        Term *op_type0 = getType(arena, env, in->op);
        Arrow *op_type = castTerm(op_type0, Arrow);
        out0 = evaluateWithArgs(arena, env, in->arg_count, in->args, op_type->output_type);
      } break;

      case Term_Arrow:
      {
        out0 = &builtins.Type->t;
      } break;

      case Term_Function:
      {
        invalidCodePath;
      } break;

      case Term_Computation:
      {
        Computation *in = castTerm(in0, Computation);
        out0 = newEquality(arena, env, in->lhs, in->rhs);
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Composite *record    = toRecord(arena, env, in->record);
        Arrow     *signature = castTerm(getType(arena, env, record->op), Arrow);
        out0 = evaluateWithArgs(arena, env, signature->param_count, record->args, signature->param_types[in->field_id]);
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        auto [lhs, rhs] = getEqualitySides(getType(arena, env, in->eq_proof));
        Term *rewrite_to  = in->right_to_left ? rhs : lhs;
        out0 = rewriteTerm(arena, rewrite_to, in->path, getType(arena, env, in->body));
      } break;

      default: todoIncomplete
    }
  }
  assert(out0);
  return out0;
}

forward_declare inline Term *
getTypeNoEnv(MemoryArena *arena, Term *in0)
{
  Typer env = {};
  return getType(arena, &env, in0);
}

inline void setType(Term *term, Term *type) {term->type = type;}

// todo #cleanup a lot of the copies are unnecessary, we must think about where
// we can put stack values. and whether to have stack values at all.
//
// todo #cleanup I think this is now only for the global overloads typecheck for
// composites?  If so then just copy the composite, no need to deepcopy
internal Ast *
deepCopy(MemoryArena *arena, Ast *in0)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_Hole:
    case AC_Identifier:
    {out0 = in0;} break;

    case AC_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);
      CompositeAst *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, out->arg_count, out->args);
      for (s32 id=0; id < in->arg_count; id++)
      {
        out->args[id] = deepCopy(arena, in->args[id]);
      }
      out0 = &out->a;
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      ArrowAst *out = copyStruct(arena, in);
      out->output_type = deepCopy(arena, in->output_type);
      allocateArray(arena, out->param_count, out->param_types);
      for (s32 id=0; id < in->param_count; id++)
      {
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      }
      out0 = &out->a;
    } break;

    case AC_Let:
    {
      Let *in = castAst(in0, Let);
      Let *out = copyStruct(arena, in);
      out->rhs = deepCopy(arena, in->rhs);
      out0 = &out->a;
    } break;

    case AC_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      RewriteAst *out = copyStruct(arena, in);
      out->eq_proof_hint = deepCopy(arena, in->eq_proof_hint);
      out0 = &out->a;
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      AccessorAst *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->a;
    } break;

    invalidDefaultCase;
  }
  return out0;
}

internal Term *
deepCopy(MemoryArena *arena, Term *in0)
{
  Term *out0 = 0;
  switch (in0->cat)
  {
    case Term_Composite:
    {
      Composite *in  = castTerm(in0, Composite);
      Composite *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, in->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
        out->args[id] = deepCopy(arena, in->args[id]);
      out0 = &out->t;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      out->output_type = deepCopy(arena, in->output_type);
      out0 = &out->t;
    } break;

    case Term_Accessor:
    {
      Accessor *in  = castTerm(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->t;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Function:
    {out0 = in0;} break;

    default: todoIncomplete;
  }
  return out0;
}

inline LocalBindings *
extendBindings(MemoryArena *arena, Typer *env)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->next     = env->bindings;
  out->arena    = arena;
  out->count    = 0;
  env->bindings = out;
  return out;
}

inline LocalBindings * extendBindings(Typer *env) {return extendBindings(temp_arena, env);}

forward_declare inline void
dump(Trinary trinary)
{
  if (trinary == Trinary_True) dump("True");
  else if (trinary == Trinary_False) dump("False");
  else dump("Unknown");
}

forward_declare inline void unwindStack(Typer *env) {env->type_stack = env->type_stack->outer;}

forward_declare inline void
unwindBindingsAndStack(Typer *env)
{
  env->bindings = env->bindings->next;
  unwindStack(env);
}

forward_declare inline void dump(Term *in0) {print(0, in0, {});}
forward_declare inline void dump(Ast *in0)  {print(0, in0, {});}

inline void
dump(Typer *env)
{
  dump("stack: ");
  dump(env->type_stack);
}

s32 global_variable debug_indentation;
forward_declare inline void debugIndent()
{
  debug_indentation++;
  for (s32 id = 0; id < debug_indentation; id++)
    dump(" ");
}

forward_declare inline void debugDedent()
{
  for (s32 id = 0; id < debug_indentation; id++)
    dump(" ");
  debug_indentation--;
}

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

inline b32
isHiddenParameter(ArrowAst *arrow, s32 param_id)
{
  return arrow->param_names[param_id].string.chars[0] == '_';
}

inline b32
isHiddenParameter(Arrow *arrow, s32 param_id)
{
  return arrow->param_names[param_id].string.chars[0] == '_';
}

inline s32
precedenceOf(String op)
{
  int out = 0;

  // TODO: implement for real
  if (equal(op, "->"))
    out = 40;
  if (equal(op, "=") || equal(op, "!="))
    out = 50;
  else if (equal(op, "&")
           || equal(op, "*"))
    out = 70;
  else if (equal(op, "|")
           || equal(op, "+")
           || equal(op, "-"))
    out = 60;
  else
    out = 100;

  return out;
}

inline void
printComposite(MemoryArena *buffer, void *in0, b32 is_term, PrintOptions opt)
{
  int    precedence = 0;        // todo: no idea what the default should be
  void  *op         = 0;
  s32    arg_count  = 0;
  void **raw_args   = 0;

  Ast  *ast   = (Ast *)in0;
  Term *value = (Term *)in0;
  Arrow *op_signature = 0;
  if (is_term)
  {
    Composite *in = castTerm(value, Composite);
    op           = in->op;
    op_signature = 0;
    raw_args     = (void **)in->args;
    arg_count    = in->arg_count;

    if (in->op && in->op->cat != Term_Variable)
    {
      op_signature = castTerm((getTypeNoEnv(temp_arena, in->op)), Arrow);
      assert(op_signature);
      if (Token *global_name = in->op->global_name)
        precedence = precedenceOf(global_name->string);
    }
  }
  else
  {
    CompositeAst *in = castAst(ast, CompositeAst);
    op       = in->op;
    raw_args = (void **)in->args;
    arg_count = in->arg_count;

    precedence = precedenceOf(in->op->token.string);
  }

  void **printed_args;
  if (op_signature)
  {// print out unignored args only
    arg_count = 0;
    printed_args = pushArray(temp_arena, op_signature->param_count, void*);
    for (s32 param_id = 0; param_id < op_signature->param_count; param_id++)
    {
      if (!isHiddenParameter(op_signature, param_id))
        printed_args[arg_count++] = raw_args[param_id];
    }
  }
  else
    printed_args = raw_args;

  if (arg_count == 2)
  {// special path for infix operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    arg_opt.no_paren_precedence = precedence+1;
    print(buffer, printed_args[0], is_term, arg_opt);

    print(buffer, " ");
    print(buffer, op, is_term, opt);
    print(buffer, " ");

    arg_opt.no_paren_precedence = precedence;
    print(buffer, printed_args[1], is_term, arg_opt);
    if (precedence < opt.no_paren_precedence)
      print(buffer, ")");
  }
  else
  {// normal prefix path
    print(buffer, op, is_term, opt);
    if (arg_count != 0)
    {
      print(buffer, "(");
      PrintOptions arg_opt        = opt;
      arg_opt.no_paren_precedence = 0;
      for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
      {
        print(buffer, printed_args[arg_id], is_term, arg_opt);
        if (arg_id < arg_count-1)
          print(buffer, ", ");
      }
      print(buffer, ")");
    }
  }
}

inline void
print(MemoryArena *buffer, TreePath *tree_path)
{
  print(buffer, "[");
  for (TreePath *path=tree_path; path; path=path->next)
  {
    print(buffer, "%d", path->first);
    if (path->next)
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

inline void indent(MemoryArena *buffer, s32 indentation)
{
  for (int id=0; id < indentation; id++)
    print(buffer, " ");
}

inline void newlineAndIndent(MemoryArena *buffer, s32 indentation)
{
  print(buffer, "\n");
  indent(buffer, indentation);
}

forward_declare internal char *
print(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{// printAst
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    new_opt.indentation += 1;

    switch (in0->cat)
    {
      case AC_Hole:
      {print(buffer, "_");} break;

      case AC_SyntheticAst:
      {
        SyntheticAst *in = castAst(in0, SyntheticAst);
        print(buffer, in->term);
      } break;

      case AC_Identifier:
      {print(buffer, in0->token.string);} break;

      case AC_RewriteAst:
      {
        RewriteAst *in = castAst(in0, RewriteAst);
        print(buffer, "rewrite");
        print(buffer, in->path);
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof_hint, new_opt);
      } break;

      case AC_CompositeAst:
      {
        printComposite(buffer, in0, false, new_opt);
      } break;

      case AC_ForkAst:
      {
        ForkAst *in = castAst(in0, ForkAst);
        print(buffer, "fork ");
        print(buffer, in->subject, new_opt);
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, "{");
        i32 case_count = in->case_count;
        for (s32 ctor_id = 0;
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

      case AC_ArrowAst:
      {
        ArrowAst *in = castAst(in0, ArrowAst);
        print(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          print(buffer, in->param_names[param_id].string);
          print(buffer, ": ");
          print(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ") -> ");

        print(buffer, in->output_type, new_opt);
      } break;

      case AC_AccessorAst:
      {
        AccessorAst *in = castAst(in0, AccessorAst);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name.string);
      } break;

      case AC_FunctionDecl: {print(buffer, "function decl");} break;

      case AC_Lambda: {print(buffer, "lambda");} break;

      case AC_Let:
      {
        Let *in = castAst(in0, Let);
        print(buffer, in->lhs.string);
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

      case AC_ComputationAst:
      {
        ComputationAst *computation = castAst(in0, ComputationAst);
        print(buffer, "computation: (");
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, ")");
      } break;
    }
  }
  else
    print(buffer, "<NULL>");
  return out;
}

forward_declare internal char *
print(MemoryArena *buffer, Ast *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal char *
print(MemoryArena *buffer, Term *in0, PrintOptions opt)
{// mark: printTerm
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    if (!flagIsSet(opt.flags, PrintFlag_LockDetailed))
      unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    unsetFlag(&new_opt.flags, PrintFlag_PrintType);
    new_opt.indentation = opt.indentation + 1;
    b32 skip_print_type = false;

    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        print(buffer, in->name.string);
        if (global_debug_mode)
          print(buffer, "[%d,%d]", in->stack_delta, in->id);
      } break;

      case Term_Hole:
      {print(buffer, "_");} break;

      case Term_Composite:
      {printComposite(buffer, in0, true, new_opt);} break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        print(buffer, in0->global_name->string);
        if (flagIsSet(opt.flags, PrintFlag_Detailed))
        {
          if (in->ctor_count)
          {
            print(buffer, " {");
            unsetFlag(&new_opt.flags, PrintFlag_Detailed);
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Constructor *ctor = in->ctors + ctor_id;
              print(buffer, globalNameOf(&ctor->t));
              print(buffer, ": ");
              print(buffer, getTypeNoEnv(temp_arena, &ctor->t), new_opt);
            }
            print(buffer, " }");
          }
        }
      } break;

      case Term_Function:
      {
        Function *in = castTerm(in0, Function);
        b32 is_anonymous = false;
        String name = globalNameOf(in0);
        if (name.chars)
          print(buffer, name);
        else
          is_anonymous = true;

        if (flagIsSet(opt.flags, PrintFlag_Detailed) || is_anonymous)
        {
          skip_print_type = true;
          if (in->type) print(buffer, in->type, new_opt);

          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          print(buffer, in->body, new_opt);
          print(buffer, "}");
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in = castTerm(in0, Arrow);
        print(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          print(buffer, in->param_names[param_id].string);
          print(buffer, ": ");
          print(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ") -> ");
        print(buffer, in->output_type, new_opt);
      } break;

      case Term_Builtin:
      {
        if (in0 == &builtins.equal->t)
          print(buffer, "=");
        else if (in0 == &builtins.Set->t)
          print(buffer, "Set");
        else if (in0 == &builtins.Type->t)
          print(buffer, "Type");
      } break;

      case Term_Constructor:
      {
        Constructor *in = castTerm(in0, Constructor);
        print(buffer, in->name.string);
      } break;

      case Term_Rewrite:
      {
        Rewrite *rewrite = castTerm(in0, Rewrite);
        print(buffer, getTypeNoEnv(temp_arena, &rewrite->t), new_opt);
        skip_print_type = true;
        print(buffer, " <=>");
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, getTypeNoEnv(temp_arena, rewrite->body), new_opt);
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "rewrite");
        if (rewrite->right_to_left) print(buffer, "<-");
        print(buffer, rewrite->path);
        if (rewrite->eq_proof->cat != Term_Computation)
        {
          print(buffer, " justification: ");
          newlineAndIndent(buffer, new_opt.indentation);
          print(buffer, rewrite->eq_proof, new_opt);
        }
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "body: ");
        print(buffer, getTypeNoEnv(temp_arena, rewrite->body), new_opt);
        newlineAndIndent(buffer, new_opt.indentation);
        print(buffer, rewrite->body, new_opt);
      } break;

      case Term_Computation:
      {
        print(buffer, "computation: (");
        Computation *computation = castTerm(in0, Computation);
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, ")");
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name);
      } break;

      case Term_Fork:
      {
        Fork *in = castTerm(in0, Fork);
        print(buffer, "fork ");
        print(buffer, in->subject, new_opt);
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, "{");
        Union *form = in->uni;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          Constructor *ctor = form->ctors + ctor_id;
          print(buffer, &ctor->t, new_opt);
          print(buffer, ": ");
          print(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != form->ctor_count-1)
          {
            print(buffer, ", ");
            newlineAndIndent(buffer, opt.indentation+1);
          }
        }
        print(buffer, "}");
      } break;

    }

    if (flagIsSet(opt.flags, PrintFlag_PrintType) && !skip_print_type)
    {
      print(buffer, ": ");
      print(buffer, getTypeNoEnv(temp_arena, in0), new_opt);
    }
  }
  else
    print(buffer, "<NULL>");

  return out;
}

forward_declare internal char *
print(MemoryArena *buffer, Term *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal char *
print(MemoryArena *buffer, void *in0, b32 is_absolute, PrintOptions opt)
{
  if (is_absolute)
    return print(buffer, (Term*)in0, opt);
  else
    return print(buffer, (Ast*)in0, opt);
}

forward_declare inline void
extendStack(Typer *env, i32 cap, Term **items)
{
  Stack *stack = pushStruct(temp_arena, Stack, true);
  stack->depth = getStackDepth(env) + 1;
  stack->outer = env->type_stack;
  stack->cap   = cap;
  if (items)
  {
    stack->count = cap;
    stack->items = items;
  }
  else
    allocateArray(temp_arena, cap, stack->items);
  env->type_stack = stack;
}

forward_declare inline void
addToStack(Typer *env, Term *item)
{
  i32 id = env->type_stack->count++;
  assert(id < env->type_stack->cap);
  env->type_stack->items[id] = item;
}

forward_declare inline b32
equal(Typer *env, Term *lhs, Term *rhs)
{
  return equalTrinary(env, lhs, rhs) == Trinary_True;
}

inline b32
isCompositeConstructor(Term *in0)
{
  if (Composite *in = castTerm(in0, Composite))
    return in->op->cat == Term_Constructor;
  else
    return false;
}

inline b32
isGlobalConstant(Term *in0)
{
  if (in0->global_name)
    return true;

  switch (in0->cat)
  {
    case Term_Hole:
    case Term_Variable:
    {return false;} break;

    case Term_Composite:
    {
      Composite *composite = castTerm(in0, Composite);
      if (!isGlobalConstant(composite->op))
        return false;

      for (int id=0; id < composite->arg_count; id++)
      {
        if (!isGlobalConstant(composite->args[id]))
          return false;
      }

      return true;
    } break;

    case Term_Arrow:
    case Term_Function:
    case Term_Fork:
    case Term_Accessor:
    case Term_Rewrite:
    case Term_Computation:
    {return false;} break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    {return true;} break;
  }
}

forward_declare internal Term *
rebaseMain(MemoryArena *arena, Term *in0, i32 delta, i32 offset)
{
  assert(delta >= 0);
  Term *out0 = in0;
  if (!isGlobalConstant(in0) && (delta > 0))
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in  = castTerm(in0, Variable);
        if (in->stack_delta >= offset)
        {
          Variable *out = copyStruct(arena, in);
          out->stack_delta += delta;
          out0 = &out->t;
        }
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        allocateArray(arena, out->arg_count, out->args);
        out->op = rebaseMain(arena, out->op, delta, offset);
        for (i32 id = 0; id < out->arg_count; id++)
          out->args[id] = rebaseMain(arena, in->args[id], delta, offset);
        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        allocateArray(arena, out->param_count, out->param_types);
        for (i32 id=0; id < out->param_count; id++)
          out->param_types[id] = rebaseMain(arena, in->param_types[id], delta, offset+1);
        out->output_type = rebaseMain(arena, out->output_type, delta, offset+1);
        out0 = &out->t;
      } break;

      default:
        todoIncomplete;
    }
  }
  return out0;
}

forward_declare internal Term *
rebase(MemoryArena *arena, Term *in0, i32 delta)
{
  return rebaseMain(arena, in0, delta, 0);
}

forward_declare internal Term *
evaluate(MemoryArena *arena, Stack *stack, Typer *env, Term *in0, i32 offset)
{
  Term *out0 = in0;
  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (debug && global_debug_mode)
  {debugIndent(); DUMP("evaluate(", serial, "): ", in0, "\n");}
  assert(offset >= 0);
  if (!isGlobalConstant(in0))
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->stack_delta == offset)
        {
          out0 = lookupStack(stack, in->stack_delta - offset, in->id);
          out0 = rebase(arena, out0, offset);
        }
        else if (in->stack_delta > offset)
        {
          // TODO this is rocket science in here...
          Variable *out = copyStruct(arena, in);
          out->stack_delta--;
          out0 = &out->t;
        }
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        allocateArray(arena, in->arg_count, out->args);
        for (i32 id=0; id < in->arg_count; id++)
          out->args[id] = evaluate(arena, stack, env, in->args[id], offset);
        out->op = evaluate(arena, stack, env, in->op, offset);

        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);

        allocateArray(arena, out->param_count, out->param_types);
        for (i32 id=0; id < out->param_count; id++)
        {
          out->param_types[id] = evaluate(arena, stack, env, in->param_types[id], offset+1);
        }
        out->output_type = evaluate(arena, stack, env, out->output_type, offset+1);

        out0 = &out->t;
      } break;

      case Term_Function:
      {
        if (offset)
          todoIncomplete;  // we can outlaw this, but possible to handle if we must
        Function *in = castTerm(in0, Function);
        Function *out = copyStruct(arena, in);
        out->stack = stack;
        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Term *record0 = evaluate(arena, stack, env, in->record, offset);
        if (Composite *record = castRecord(record0))
          out0 = record->args[in->field_id];
        else
        {
          Accessor *out = copyStruct(arena, in);
          out->record = record0;
          out0 = &out->t;
        }
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = copyStruct(arena, in);
        out->lhs  = evaluate(arena, stack, env, in->lhs, offset);
        out->rhs  = evaluate(arena, stack, env, in->rhs, offset);
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in  = castTerm(in0, Rewrite);
        out0 = in0;
        if (Term *eq_proof = evaluate(arena, stack, env, in->eq_proof, offset))
        {
          if (Term *body = evaluate(arena, stack, env, in->body, offset))
          {
            Rewrite *out = copyStruct(arena, in);
            out->eq_proof = eq_proof;
            out->body     = body;
            out0 = &out->t;
          }
        }
      } break;

      case Term_Fork:
      {
        Fork *in = castTerm(in0, Fork);
        Term *subject = evaluate(temp_arena, stack, env, in->subject, offset);
        if (Constructor *ctor = getConstructor(env, subject))
          out0 = evaluate(arena, stack, env, in->bodies[ctor->id], offset);
        else
          out0 = 0;
      } break;

      case Term_Builtin:
      case Term_Union:
      case Term_Constructor:
      case Term_Hole:
      {out0=in0;} break;
    }
  }

  assert(isSequenced(in0) || out0);
  if (debug && global_debug_mode)
  {debugDedent(); DUMP("=> ", out0, "\n");}
  return out0;
}

forward_declare inline Term *
evaluateWithArgs(MemoryArena *arena, Typer *env, i32 arg_count, Term **args, Term *in0)
{
  Stack *stack = pushStruct(temp_arena, Stack, true);
  stack->depth = 1;
  stack->cap   = stack->count = arg_count;
  stack->items = args;
  return evaluate(arena, stack, env, in0, 0);
}

inline Constructor *
getSoleConstructor(Term *type)
{
  if (Union *uni = castTerm(type, Union))
  {
    if (uni->ctor_count == 1)
      // sole constructor
      return uni->ctors + 0;
  }
  return 0;
}

forward_declare internal CompareTerms
compareTerms(MemoryArena *arena, Typer *env, Term *lhs0, Term *rhs0)
{
  CompareTerms out = {};
  out.result = Trinary_Unknown;

  b32 debug = false;
  i32 serial = global_debug_serial++;
  if (debug && global_debug_mode)
  {
    debugIndent(); dump("comparing("); dump(serial); dump("): ");
    dump(lhs0); dump(" and "); dump(rhs0); dump();
  }

  if (!lhs0 | !rhs0)
    out.result = {Trinary_False};
  else if (lhs0 == rhs0)
    out.result = {Trinary_True};
  else if (lhs0->cat == rhs0->cat)
  {
    switch (lhs0->cat)
    {
      case Term_Variable:
      {
        Variable *lhs = castTerm(lhs0, Variable);
        Variable *rhs = castTerm(rhs0, Variable);
        if ((lhs->stack_delta == rhs->stack_delta) && (lhs->id == rhs->id))
          out.result = Trinary_True;
      } break;

      case Term_Arrow:
      {
        Arrow* lhs = castTerm(lhs0, Arrow);
        Arrow* rhs = castTerm(rhs0, Arrow);
        s32 param_count = lhs->param_count;
        if (rhs->param_count == param_count)
        {
          b32 type_mismatch = false;
          for (s32 id = 0; id < param_count; id++)
          {
            if (!equal(env, lhs->param_types[id], rhs->param_types[id]))
            {
              type_mismatch = true;
              break;
            }
          }
          if (!type_mismatch)
            out.result = equalTrinary(env, lhs->output_type, rhs->output_type);
        }
        else
          out.result = Trinary_False;
      } break;

      case Term_Composite:
      {
        Composite *lhs = castTerm(lhs0, Composite);
        Composite *rhs = castTerm(rhs0, Composite);

        Trinary op_compare = equalTrinary(env, lhs->op, rhs->op);
        if ((op_compare == Trinary_False) &&
            (lhs->op->cat == Term_Constructor) &&
            (rhs->op->cat == Term_Constructor))
        {
          out.result = Trinary_False;
        }
        else if (op_compare == Trinary_True)
        {
          s32 count = lhs->arg_count;
          assert(lhs->arg_count == rhs->arg_count);

          int mismatch_count = 0;
          int       unique_diff_id   = 0;
          TreePath *unique_diff_path = 0;
          out.result = Trinary_True;
          for (i32 id=0; id < count; id++)
          {
            CompareTerms recurse = compareTerms(arena, env, lhs->args[id], rhs->args[id]);
            if (recurse.result != Trinary_True)
            {
              mismatch_count++;
              if (mismatch_count == 1)
              {
                unique_diff_id   = id;
                unique_diff_path = recurse.diff_path;
              }
            }
          }
          if (mismatch_count > 0)
            out.result = Trinary_Unknown;
          if ((mismatch_count == 1) && arena)
          {
            allocate(arena, out.diff_path);
            out.diff_path->first = unique_diff_id;
            out.diff_path->next  = unique_diff_path;
          }
        }
      } break;

      case Term_Constructor:
      {
        Constructor *lhs = castTerm(lhs0, Constructor);
        Constructor *rhs = castTerm(rhs0, Constructor);
        out.result = toTrinary(lhs->id == rhs->id);
      } break;

      case Term_Accessor:
      {
        Accessor *lhs = castTerm(lhs0, Accessor);
        Accessor *rhs = castTerm(rhs0, Accessor);
        out.result = compareTerms(arena, env, lhs->record, rhs->record).result;
      } break;

      case Term_Builtin:
      {
        out.result = toTrinary(lhs0 == rhs0);
      } break;

      case Term_Function:
      case Term_Hole:
      case Term_Union:
      case Term_Rewrite:
      case Term_Computation:
      case Term_Fork:
      {} break;
    }
  }
  else
  {
    if (isPotentialRecord(lhs0) || isPotentialRecord(rhs0))
    {
      Composite *new_lhs0 = toRecord(temp_arena, env, lhs0);
      Composite *new_rhs0 = toRecord(temp_arena, env, rhs0);
      if (new_lhs0 && new_rhs0)
        out = compareTerms(arena, env, &new_lhs0->t, &new_rhs0->t);
    }
  }

  if (debug && global_debug_mode)
  {debugDedent(); dump("=> "); dump(out.result); dump();}
  return out;
}

forward_declare internal Trinary
equalTrinary(Typer *env, Term *lhs0, Term *rhs0)
{
  return compareTerms(0, env, lhs0, rhs0).result;
}

global_variable GlobalBindings *global_bindings;

internal GlobalBinding *
lookupGlobalNameSlot(String key, b32 add_new)
{
  // :global-bindings-zero-at-startup
  GlobalBinding *slot = 0;
  u32 hash = stringHash(key) % arrayCount(global_bindings->table);
  slot = global_bindings->table + hash;
  b32 first_slot_valid = slot->key.length == 0;
  if (first_slot_valid)
  {
    while (true)
    {
      if (equal(slot->key, key))
        break;
      else if (slot->next_hash_slot)
        slot = slot->next_hash_slot;
      else
      {
        if (add_new)
        {
          slot->next_hash_slot = pushStruct(global_arena, GlobalBinding, true);
          slot = slot->next_hash_slot;
          slot->key = key;
        }
        else slot = 0;
        break;
      }
    }
  }
  else if (add_new) slot->key = key;
  else slot = 0;

  if (slot && !add_new) assert(slot->count != 0);

  return slot;
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
      else if (slot->next)
        slot = slot->next;
      else
      {
        stop = true;
        if (add_if_missing)
        {
          allocate(bindings->arena, slot->next);
          slot = slot->next;
          slot->key  = key;
          slot->next = 0;
        }
      }
    }
  }
  else if (add_if_missing)
  {
    slot->key   = key;
    slot->value = {};
  }

  LookupCurrentFrame out = { slot, found };
  return out;
}

// todo #cleanup #mem don't allocate too soon
forward_declare internal Term *
normalize(MemoryArena *arena, Typer *env, Term *in0) 
{
  Term *out0 = {};

  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (debug && global_debug_mode)
  {debugIndent(); DUMP("normalize(", serial, "): ", in0, "\n");}

  switch (in0->cat)
  {
    case Term_Composite:
    {
      Composite *in = castTerm(in0, Composite);
      b32 progressed = false;

      Term **norm_args = pushArray(arena, in->arg_count, Term*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        norm_args[arg_id] = normalize(arena, env, in->args[arg_id]);
        progressed = progressed || (norm_args[arg_id] != in->args[arg_id]);
      }

      Term *norm_op = normalize(arena, env, in->op);
      progressed = progressed || (norm_op != in->op);
      if (norm_op->cat == Term_Function)
      {// Function application
        Function *fun = castTerm(norm_op, Function);
        if (fun->body != &dummy_function_being_built)
        {
          Term *eval = evaluateWithArgs(arena, env, in->arg_count, norm_args, fun->body);
          if (eval)
            out0 = normalize(arena, env, eval);
        }
      }
      else
      {
        assert((norm_op == &builtins.equal->t) || (norm_op->cat == Term_Constructor));
        // special casing for equality
        if (norm_op == &builtins.equal->t)
        {// special case for equality
          Term *lhs = norm_args[1];
          Term *rhs = norm_args[2];
          Trinary compare = equalTrinary(env, lhs, rhs);
          // #hack to handle inconsistency
          if (compare == Trinary_False)
            out0 = &builtins.False->t;
        }
      }

      if (!out0)
      {
        if (progressed)
        {
          Composite *out = newTerm(arena, Composite, 0);
          out->arg_count = in->arg_count;
          out->op        = norm_op;
          out->args      = norm_args;
          out0 = &out->t;
        }
        else
          out0 = in0;
      }
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);

      allocateArray(arena, out->param_count, out->param_types);
      for (i32 id=0; id < out->param_count; id++)
      {
        out->param_types[id] = normalize(arena, env, in->param_types[id]);
      }
      out->output_type = normalize(arena, env, out->output_type);

      out0 = &out->t;
    } break;

    case Term_Rewrite:
    {
      Rewrite *in   = castTerm(in0, Rewrite);
      Term *body     = normalize(arena, env, in->body);
      Term *eq_proof = normalize(arena, env, in->eq_proof);
      if ((body != in->body) || (eq_proof != in->eq_proof))
      {
        Rewrite *out = copyStruct(arena, in);
        out->eq_proof = eq_proof;
        out->body     = body;
        out0 = &out->t;
      }
      else out0 = in0;
    } break;

    case Term_Accessor:
    {
      out0 = in0;
      Accessor *in = castTerm(in0, Accessor);
      Term *record0 = normalize(arena, env, in->record);
      if (Composite *record = castRecord(record0))
        out0 = record->args[in->field_id];
    } break;

    case Term_Fork:
    {invalidCodePath;} break;

    case Term_Variable:
    case Term_Hole:
    case Term_Constructor:
    case Term_Builtin:
    case Term_Function:
    case Term_Union:
    case Term_Computation:
    {out0 = in0;} break;
  }

  if (debug && global_debug_mode)
  {debugDedent(); dump("=> "); dump(out0); dump();}

  assert(isSequenced(in0) || out0);
  return out0;
}

#if 0
// this has to work on both values and terms
internal Term *
toAbstractTerm(MemoryArena *arena, Term *in0, i32 zero_depth)
{
  Term *out0 = 0;

  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (global_debug_mode && debug)
  {debugIndent(); DUMP("toAbstractTerm(", serial, "): ", in0, " with zero_depth: ", zero_depth, "\n");}

  if (in0->anchor)
  {
    out0 = toAbstractTerm(arena, in0->anchor, zero_depth);
  }
  else
  {
    switch (in0->cat)
    {
      case Term_Constant:
      {out0 = in0;} break;

      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->is_absolute)
        {
          Variable *out = copyStruct(arena, in);
          out->is_absolute = false;
          out->stack_frame = zero_depth - in->stack_frame;
          assert(out->stack_frame >= 0);
          out0 = &out->t;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        out->op        = toAbstractTerm(arena, in->op, zero_depth);
        allocateArray(arena, out->arg_count, out->args);
        for (i32 id=0; id < out->arg_count; id++)
          out->args[id] = toAbstractTerm(arena, in->args[id], zero_depth);
        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        out->stack = 0;
        out0 = &out->t;
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = newTerm(arena, Computation, 0);
        out->lhs  = toAbstractTerm(arena, in->lhs, zero_depth);
        out->rhs  = toAbstractTerm(arena, in->rhs, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyStruct(arena, in);
        out->record = toAbstractTerm(arena, in->record, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in   = castTerm(in0, Rewrite);
        Rewrite *out  = copyStruct(arena, in);
        out->eq_proof = toAbstractTerm(arena, in->eq_proof, zero_depth);
        out->body     = toAbstractTerm(arena, in->body, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Fork:
      {todoIncomplete;} break;

      // global values (and functions) should have anchors.
      case Term_Constructor:
      case Term_Builtin:
      case Term_Union:
      case Term_Function:
      case Term_Hole:
        invalidCodePath;
    }
  }

  assert(out0);
  if (global_debug_mode && debug)
  {debugDedent(); dump("=>("); dump(serial); dump(") "); dump(out0); dump();}
  return out0;
} 

forward_declare inline Term *
toAbstractTerm(MemoryArena *arena, Environment *env, Term *in0)
{
  return toAbstractTerm(arena, in0, getStackDepth(env));
}

forward_declare internal Term *
evaluateAndNormalize(MemoryArena *arena, Environment *env, Term *in0)
{
  Term *eval = evaluate(arena, env, in0);
  Term *norm = normalize(arena, env, eval);
  return norm;
}
#endif

inline void
addLocalBinding(Typer *env, Token *key)
{
  if (equal(key->string, "x_positive"))
    breakhere;
  auto lookup = lookupCurrentFrame(env->bindings, key->string, true);
  lookup.slot->value = env->bindings->count++;
}

forward_declare inline void
introduceSignature(Typer *env, Arrow *signature, b32 add_bindings)
{
  i32 param_count = signature->param_count;
  extendStack(env, param_count, signature->param_types);
  if (add_bindings)
  {
    extendBindings(temp_arena, env);
    for (s32 id=0; id < param_count; id++)
    {
      Token *name = signature->param_names+id;
      addLocalBinding(env, name);
    }
  }
  assert(noError());
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
    parseError(token, "identifier not found");
    attach("identifier", token);
    return 0;
  }
}

inline Term *
lookupBuiltinGlobalName(char *name)
{
  Token token = newToken(name);
  GlobalBinding *slot = lookupGlobalName(&token);
  assert(slot->count == 1);
  return slot->items[0];
}

inline void
addGlobalBinding(Token *name, Term *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(name->string, true);
  // TODO #cleanup check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));
  Token *name_copy = copyStruct(global_arena, name);
  value->global_name = name_copy;
}

inline void
addBuiltinGlobalBinding(char *key, Term *value)
{
  Token token = newToken(key);
  addGlobalBinding(&token, value);
}

struct LookupLocalName {
  b32 found;
  s32 stack_delta;
  s32 var_id;
  operator bool() {return found;}
};

inline LookupLocalName
lookupLocalName(Typer *env, Token *token)
{
  LocalBindings *bindings = env->bindings;
  LookupLocalName out = {};
  for (s32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupCurrentFrame lookup = lookupCurrentFrame(bindings, token->string, false);
    if (lookup.found)
    {
      out.found       = true;
      out.var_id          = lookup.slot->value;
      out.stack_delta = stack_delta;
      break;
    }
    else
      bindings = bindings->next;
  }

  return out;
}

inline b32
requireChar(char c, char *reason = 0, Tokenizer *tk=global_tokenizer)
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
      parseError(tk, &token, "expected character '%c' (%s)", c, reason);
  }
  return out;
}

inline b32
requireCategory(TokenCategory tc, char *message=0, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    if (nextToken(tk).cat == tc) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
requireIdentifier(char *message, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = nextToken(tk);
    if (isIdentifier(&token)) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
optionalCategory(TokenCategory tc, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (hasMore())
    if (peekToken(tk).cat == tc)
    {
      out = true;
      nextToken();
    }

  return out;
}

inline b32
optionalChar(char c, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  Token token = peekToken(tk);
  if (equal(&token, c))
  {
    out = true;
    nextToken(tk);
  }
  return out;
}

inline b32
optionalString(char *str, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  Token token = peekToken(tk);
  if (equal(&token, str))
  {
    out = true;
    nextToken(tk);
  }
  return out;
}

struct OptionalU32 { b32 success; u32 value; };

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
  // IMPORTANT: Really want "." to be part of expresions.
  if (token->cat == TC_DoubleColon)
    return true;
  else if (token->cat == TC_ColonEqual)
    return true;
  else if (token->cat == TC_DoubleDash)
    return true;
  else if (token->cat == TC_StrongArrow)
    return true;
  else if (inString("{},);:", token))
    return true;
  else
    return false;
}

internal b32
addConstructorMap(Typer *env, Term *in0, Constructor *ctor)
{
  b32 added = false;
  if (isPotentialRecord(in0))
  {
    ConstructorMap *map = pushStruct(temp_arena, ConstructorMap, true);
    map->term  = in0;
    map->ctor  = ctor;
    map->next  = env->map;
    map->depth = getStackDepth(env);
    env->map = map;
    added= true;
  }
  return added;
}

inline s32
getExplicitParamCount(ArrowAst *in)
{
  s32 out = 0;
  for (s32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!isHiddenParameter(in, param_id))
      out++;
  }
  return out;
}

inline s32
getExplicitParamCount(Arrow *in)
{
  s32 out = 0;
  for (s32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!isHiddenParameter(in, param_id))
      out++;
  }
  return out;
}

inline b32
matchType(Typer *env, Term *actual, Term *expected)
{
  b32 out = false;
  if (expected->cat == Term_Hole)
    out = true;
  else if (equal(env, actual, expected))
    out = true;
  return out;
}

// todo check what am I passing in here?
internal b32
unify(Typer *env, Term **args, Term **types, Term *lhs0, Term *rhs0)
{
  b32 success = false;
  b32 debug = true;
  i32 serial = global_debug_serial++;
  if (global_debug_mode && debug)
  {
    debugIndent(); DUMP("unify(", serial, ") ", lhs0, " with ", rhs0, "\n");
  }
  switch (lhs0->cat)
  {
    case Term_Variable:
    {
      Variable *lhs = castTerm(lhs0, Variable);
      if (lhs->stack_delta != 0)
        todoUnknown;
      if (Term *replaced = args[lhs->id])
      {
        if (equal(env, replaced, rhs0))
          success = true;
      }
      else if (unify(env, args, types, types[lhs->id], getType(temp_arena, env, rhs0)))
      {
        args[lhs->id] = rhs0;
        success = true;
      }
    } break;

    case Term_Composite:
    {
      Composite *lhs = castTerm(lhs0, Composite);
      if (Composite *rhs = castTerm(rhs0, Composite))
      {
        if (unify(env, args, types, lhs->op, rhs->op))
        {
          success = true;
          for (int id=0; id < lhs->arg_count; id++)
          {
            if (!unify(env, args, types, lhs->args[id], rhs->args[id]))
            {
              success = false;
              break;
            }
          }
        }
      }
      else if (isPotentialRecord(rhs0))
      {
        if (Composite *new_rhs0 = toRecord(temp_arena, env, rhs0))
          success = unify(env, args, types, lhs0, &new_rhs0->t);
      }
    } break;

    case Term_Function:
    case Term_Union:
    case Term_Constructor:
    case Term_Builtin:
    {
      success = equal(env, lhs0, rhs0);
    } break;

    default:
    {
      todoIncomplete;
    } break;
  }
  if (global_debug_mode && debug)
  {
    debugDedent(); DUMP("=>(", serial, ") ");
    if (success) dump("true\n"); else dump("false\n");
  }
  return success;
}

inline TermArray
getFunctionOverloads(Typer *env, Identifier *ident, Term *output_type_goal)
{
  TermArray out = {};
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident->token.string, false))
  {
    if (output_type_goal->cat == Term_Hole)
    {
      out.items = slot->items;
      out.count = slot->count;
    }
    else
    {
      allocateArray(temp_arena, slot->count, out.items);
      for (int slot_id=0; slot_id < slot->count; slot_id++)
      {
        if (Arrow *signature = castTerm(getTypeNoEnv(temp_arena, slot->items[slot_id]), Arrow))
        {
          b32 output_type_mismatch = false;
          Term **args = pushArray(temp_arena, signature->param_count, Term*, true);
          if (!unify(env, args, signature->param_types, signature->output_type, output_type_goal))
            output_type_mismatch = true;

          if (!output_type_mismatch)
            out.items[out.count++] = slot->items[slot_id];
        }
      }
    }
  }
  return out;
}

internal SearchOutput
searchExpression(MemoryArena *arena, Typer *env, Term *lhs, Term* in0)
{
  SearchOutput out = {};
  if (equal(env, in0, lhs))
    out.found = true;
  else
  {
    switch (in0->cat)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        SearchOutput op = searchExpression(arena, env, lhs, in->op);
        if (op.found)
        {
          allocate(arena, out.path);
          out.found       = true;
          out.path->first = -1;
          out.path->next  = op.path;
        }
        else
        {
          for (int arg_id=0; arg_id < in->arg_count; arg_id++)
          {
            SearchOutput arg = searchExpression(arena, env, lhs, in->args[arg_id]);
            if (arg.found)
            {
              allocate(arena, out.path);
              out.found     = true;
              out.path->first = arg_id;
              out.path->next  = arg.path;
            }
          }
        }
      } break;

      case Term_Accessor:
      {
        Accessor* in = castTerm(in0, Accessor);
        out = searchExpression(arena, env, lhs, in->record);
      } break;

      case Term_Hole:
      case Term_Computation:
      case Term_Builtin:
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
  return out;
}

inline Ast *
parseSequence(MemoryArena *arena, b32 is_theorem, b32 auto_normalize)
{
  // NOTE: we mutate the crap out of this sequence.
  Ast *out = 0;
  Token first_token = global_tokenizer->last_token;
  s32 count = 0;
  AstList *list = 0;

  if (auto_normalize)
  {
    count++;
    list = pushStruct(temp_arena, AstList);
    list->first = &newAst(arena, RewriteAst, &first_token)->a;
    list->next  = 0;
  }

  b32 stop = false;
  while (noError() && !stop)
  {
    Tokenizer tk_save = *global_tokenizer;
    Token token = nextToken();
    Ast *ast = 0;
    switch (token.cat)
    {
      case TC_Keyword_norm:
      {
        pushContext("norm [LOCAL_VARIABLE]");
        if (optionalChar(';'))
        {// normalize goal
          RewriteAst *rewrite = newAst(arena, RewriteAst, &token);
          ast = &rewrite->a;
        }
        else
        {
          Token name = nextToken();
          if (isIdentifier(&name))
          {
            Let *let = newAst(arena, Let, &token);
            let->lhs  = name;
            let->rhs  = &newAst(arena, Identifier, &name)->a;
            let->type = LET_TYPE_NORMALIZE;
            ast = &let->a;
          }
          else
            parseError(&token, "syntax error");
        }
        popContext();
      } break;

      case TC_Keyword_rewrite:
      {
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);

        rewrite->right_to_left = false;
        Token next = peekToken();
        if (equal(next.string, "<-"))
        {
          nextToken();
          rewrite->right_to_left = true;
        }

        rewrite->eq_proof_hint = parseExpressionToAst(arena);
        ast = &rewrite->a;
      } break;

      case TC_StrongArrow:
      {
        pushContext("Full-rewrite: => TO_EXPRESSION [{ EQ_PROOF }]");
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);
        ast = &rewrite->a;
        {
          if (equal(peekToken().string, "_"))
          {// normlization
            nextToken();
          }
          else if ((rewrite->new_goal = parseExpressionToAst(arena)))
          {
            if (optionalChar('{'))
            {
              if (optionalString("<-"))  // todo: don't know whether to make a token type for this.
              {
                rewrite->right_to_left = true;
              }
              rewrite->eq_proof_hint = parseExpressionToAst(arena);
              requireChar('}');
            }
          }
        }
        popContext();
      } break;

      default:
      {
        if (isIdentifier(&token))
        {
          Token *name = &token;
          Token after_name = nextToken();
          switch (after_name.cat)
          {
            case TC_ColonEqual:
            {
              pushContext("let: NAME := VALUE");
              if (Ast *rhs = parseExpressionToAst(arena))
              {
                Let *let = newAst(arena, Let, name);
                ast = &let->a;
                let->lhs = *name;
                let->rhs = rhs;
              }
              popContext();
            } break;

            case TC_Colon:
            {
              pushContext("typed let: NAME : TYPE := VALUE");
              if (Ast *type = parseExpressionToAst(arena))
              {
                if (requireCategory(TC_ColonEqual, ""))
                {
                  if (Ast *rhs = parseExpressionToAst(arena))
                  {
                    Let *let = newAst(arena, Let, name);
                    ast = &let->a;
                    let->lhs  = *name;
                    let->rhs  = rhs;
                    let->type = type;
                  }
                }
              }
              popContext();
            } break;

            default: {};
          }
        }
        else if (isExpressionEndMarker(&token))
        {// synthetic hole
          *global_tokenizer = tk_save;
          ast  = &newAst(arena, Hole, &token)->a; // todo do we print this out correctly?
          stop = true;
        }
      } break;
    }

    if (noError() && !ast)
    {
      *global_tokenizer = tk_save;
      Token token = peekToken();
      if (token.cat == TC_Keyword_fork)
      {
        nextToken();
        ast = &parseFork(arena, is_theorem)->a;
        stop = true;
      }
      else
      {
        ast = parseExpressionToAst(arena);
        stop = true;
      }
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->first = ast;
      new_list->next  = list;
      list = new_list;
      // f.ex function definitions doesn't need to end with ';'
      optionalChar(';');
    }
  }

  if (noError())
  {
    assert(count > 0);
    Ast *previous = 0;
    for (i32 id = 0; id < count; id++)
    {
      Ast *item = list->first;
      if (id > 0)
      {
        if (Let *let = castAst(item, Let))
          let->body = previous;
        else if (RewriteAst *rewrite = castAst(item, RewriteAst))
          rewrite->body = previous;
      }
      previous = item;
      if (id != count-1)
        list = list->next;
    }
    out = list->first;
  }

  return out;
}

internal Term *
subExpressionAtPath(Term *in, TreePath *path)
{
  if (path)
  {
    switch (in->cat)
    {
      case Term_Composite:
      {
        Composite *composite = castTerm(in, Composite);
        Term *arg = composite->args[path->first];
        return subExpressionAtPath(arg, path->next); 
      } break;

      invalidDefaultCase;
    }
  }
  else return in;
}

inline Ast *
synthesizeAst(MemoryArena *arena, Term *term, Token *token)
{
  SyntheticAst *out = newAst(arena, SyntheticAst, token);
  out->term = term;
  return &out->a;
}

forward_declare internal BuildTerm
buildTerm(MemoryArena *arena, Typer *env, Ast *in0, Term *goal)
{
  // todo #cleanup limit the usage of toAbstractTerm
  // todo #cleanup #mem: sort out what we need and what we don't need to persist
  // todo #cleanup #speed: returning the value is just a waste of time most of the time. Just call evaluate whenever you need the value.
  // todo #cleanup don't return a value
  // todo return the type?
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 serial = global_debug_serial++;
  BuildTerm out0 = {};
  assert(goal);
  b32 should_check_type = true;
  b32 recursed = false;

  switch (in0->cat)
  {
    case AC_Hole:
    {
      Term *fill = fillHole(arena, env, goal);
      if (fill)
        out0.term  = fill;
      else
      {
        parseError(in0, "expression required");
        attach("goal", goal);
        MemoryArena buffer_ = subArena(temp_arena, 1024);
        MemoryArena *buffer = &buffer_;
        attach("proof_context", (char *)buffer->base);
        assert(buffer->used == 0);
        print(buffer, "stack: ");
        print(buffer, env->type_stack);
      }
    } break;

    case AC_SyntheticAst:
    {
      SyntheticAst *in = castAst(in0, SyntheticAst);
      out0.term = in->term;
    } break;

    case AC_Identifier:
    {
      // Identifier *in = castAst(in0, Identifier);
      Token *name = &in0->token;
      if (LookupLocalName local = lookupLocalName(env, name))
      {
        Variable *var = newTerm(arena, Variable, 0);
        var->name        = in0->token;
        var->id          = local.var_id;
        var->stack_delta = local.stack_delta;
        out0.term  = &var->t;
      }
      else
      {
        Term *value = 0;
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (s32 value_id = 0; value_id < globals->count; value_id++)
          {
            Term *slot_value = globals->items[value_id];
            if (matchType(0, getTypeNoEnv(temp_arena, slot_value), goal))
            {
              if (value)
              {// ambiguous
                parseError(name, "not enough type information to disambiguate global name");
                setErrorCode(ErrorAmbiguousName);
                break;
              }
              else
                value = slot_value;
            }
          }
          if (!value)
          {
            parseError(name, "global name does not match expected type");
            attach("name", name);
            attach("expected_type", goal);
            if (globals->count == 1)
              attach("actual_type", getTypeNoEnv(temp_arena, globals->items[0]));
          }
        }

        if (value)
        {
          should_check_type = false;
          out0.term = value;
        }
      }
    } break;

    case AC_CompositeAst:
    {
      CompositeAst *in  = castAst(in0, CompositeAst);
      Composite    *out = newTerm(arena, Composite, 0);

      // i32 serial = global_debug_serial++;
      TermArray op_overloads = {};
      b32 is_global = false;
      if (Identifier *op_ident = castAst(in->op, Identifier))
      {
        if (!lookupLocalName(env, &in->op->token))
        {
          op_overloads = getFunctionOverloads(env, op_ident, goal);
          if (op_overloads.count == 0)
            parseError(in->op, "found no suitable overload");
          else
            is_global = true;
        }
      }

      if (noError() && !is_global)
      {
        if (BuildTerm build_op = buildTerm(temp_arena, env, in->op, holev))
        {
          op_overloads.count = 1;
          allocateArray(temp_arena, 1, op_overloads.items);
          op_overloads.items[0] = build_op.term;
        }
      }

      for (i32 attempt=0; attempt < op_overloads.count; attempt++)
      {
        Term *op = op_overloads.items[attempt];
        out->op = op;
        if (Arrow *signature = castTerm(getType(temp_arena, env, op), Arrow))
        {
          if (signature->param_count != in->arg_count)
          {
            s32 explicit_param_count = getExplicitParamCount(signature);
            if (in->arg_count == explicit_param_count)
            {
              Ast **supplied_args = in->args;
              in->arg_count = signature->param_count;
              in->args      = pushArray(arena, signature->param_count, Ast*);
              for (s32 param_id = 0, arg_id = 0;
                   param_id < signature->param_count && noError();
                   param_id++)
              {
                if (isHiddenParameter(signature, param_id))
                {
                  in->args[param_id] = &newAst(arena, Hole, &in->op->token)->a;
                }
                else
                {
                  assert(arg_id < explicit_param_count);
                  in->args[param_id] = supplied_args[arg_id++];
                }
              }
            }
            else
              parseError(&in0->token, "argument count does not match the number of explicit parameters (expected: %d, got: %d)", explicit_param_count, in->arg_count);
          }

          if (noError())
          {
            Term **args = pushArray(arena, in->arg_count, Term *);
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {
              Term *param_type0 = signature->param_types[arg_id];
              if (serial == 5915)
              {
                DUMP("\n", &signature->t, "\n");
              }
              Term *expected_arg_type = evaluateWithArgs(temp_arena, env, signature->param_count, args, param_type0);

              // Typecheck & Inference for the arguments.
              if (in->args[arg_id]->cat == AC_Hole)
              {
                if (Term *fill = fillHole(arena, env, expected_arg_type))
                  args[arg_id] = fill;
                else
                {
                  Term *placeholder_arg = copyStruct(temp_arena, holev);
                  setType(placeholder_arg, expected_arg_type);
                  args[arg_id] = placeholder_arg;
                }
              }
              else
              {
                if (BuildTerm arg = buildTerm(arena, env, in->args[arg_id], expected_arg_type))
                {
                  args[arg_id] = arg.term;
                  if (expected_arg_type->cat == Term_Hole)
                  {
                    Variable *param_type = castTerm(param_type0, Variable);
                    assert(param_type->stack_delta == 0);
                    Term *placeholder_arg = args[param_type->id];
                    assert(placeholder_arg->cat == Term_Hole);
                    Term *arg_type = getType(arena, env, arg.term);
                    Term *arg_type_type = getType(arena, env, arg_type);
                    if (equal(env, placeholder_arg->type, arg_type_type))
                      args[param_type->id] = arg_type;
                    else
                    {
                      parseError(in->args[arg_id], "type of argument has wrong type");
                      attach("expected", placeholder_arg->type);
                      attach("got", arg_type_type);
                    }
                  }
                }
              }
            }

            if (noError())
            {
              for (s32 arg_id = 0;
                   arg_id < in->arg_count && noError();
                   arg_id++)
              {
                if (args[arg_id]->cat == Term_Hole)
                {
                  parseError(in->args[arg_id], "Cannot fill hole");
                  attach("argument number", arg_id);
                  attach("param type", signature->param_types[arg_id]);
                }
              }
            }

            if (noError())
            {
              out->arg_count = in->arg_count;
              allocateArray(arena, out->arg_count, out->args);
              for (i32 id = 0; id < out->arg_count; id++)
                out->args[id] = args[id];
              out0.term  = &out->t;
            }
          }
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          attach("operator type", getType(temp_arena, env, op));
        }

        if (op_overloads.count > 1)
        {
          if (hasError())
          {
            wipeError();
            if (attempt == op_overloads.count-1)
              parseError(in->op, "found no suitable overload");
          }
          else
            break;
        }
      }
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      Arrow *out = newTerm(arena, Arrow, &builtins.Type->t);
      i32 param_count = in->param_count;
      out->param_count = param_count;
      out->param_names = in->param_names;
      {
        extendStack(env, param_count, 0);
        extendBindings(temp_arena, env);
        allocateArray(arena, param_count, out->param_types);
        for (s32 id=0; id < param_count && noError(); id++)
        {
          BuildTerm param_type = buildTerm(arena, env, in->param_types[id], holev);
          if (param_type)
          {
            out->param_types[id] = param_type.term;
            if (out->param_types[id] == (Term*)0x2000002F462)
              __debugbreak();
            Token *name = in->param_names+id;
            addToStack(env, param_type.term);
            addLocalBinding(env, name);
          }
        }

        if (noError())
        {
          if (in->output_type)
          {
            if (BuildTerm output_type = buildTerm(arena, env, in->output_type, holev))
              out->output_type = output_type.term;
          }
        }
        unwindBindingsAndStack(env);
      }
      if (noError())
        out0.term  = &out->t;
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      Accessor *out = newTerm(arena, Accessor, 0);
      out->field_name = in->field_name.string;
      if (BuildTerm build_record = buildTerm(arena, env, in->record, holev))
      {
        if (Constructor *ctor = getConstructor(env, build_record.term))
        {
          out->record = build_record.term;
          Arrow *op_type = castTerm(ctor->type, Arrow);
          s32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          for (s32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->field_name.string, op_type->param_names[param_id].string))
            {
              out->field_id  = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
            out0.term = &out->t;
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", &ctor->t);
            attach("in type", op_type->output_type);
          }
        }
        else
          parseError(in->record, "cannot access a non-record");
      }
    } break;

    case AC_Lambda:
    {
      Lambda   *in  = castAst(in0, Lambda);
      should_check_type = false;
      Term *type = goal;
      if (in->signature)
      {
        if (BuildTerm build = buildTerm(arena, env, in->signature, holev))
          type = build.term;
      }

      if (noError())
      {
        if (Arrow *signature = castTerm(type, Arrow))
        {
          Function *fun = newTerm(arena, Function, 0);
          fun->type = &signature->t;

          introduceSignature(env, signature, true);
          if (BuildTerm body = buildTerm(arena, env, in->body, signature->output_type))
            fun->body = body.term;
          unwindBindingsAndStack(env);
          if (noError())
            out0.term  = &fun->t;
        }
        else
        {
          parseError(in0, "lambda has to have an arrow type");
          attach("goal", goal);
        }
      }
    } break;

    case AC_RewriteAst:
    {
      should_check_type = false;
      RewriteAst *in  = castAst(in0, RewriteAst);
      Rewrite    *out = newTerm(arena, Rewrite, 0);
      Term *new_goal = 0;
      if (!in->eq_proof_hint)
      {
        b32 skip_goal_comparison = false;
        if (!in->new_goal)
        {
          new_goal = normalize(arena, env, goal);
          skip_goal_comparison = true;
        }
        else if (BuildTerm build = buildTerm(arena, env, in->new_goal, holev))
          new_goal = build.term;

        if (noError())
        {
          if (equal(env, new_goal, goal))
          {// superfluous rewrite -> remove
            recursed = true;
            out0 = buildTerm(arena, env, in->body, goal);
          }
          else
          {
            if (!skip_goal_comparison)
            {
              Term *new_goal_norm = normalize(arena, env, new_goal);
              Term *goal_norm     = normalize(arena, env, goal);
              if (!equal(env, new_goal_norm, goal_norm))
              {
                parseError(in0, "new goal does not match original");
                equal(env, new_goal_norm, goal_norm);
                attach("new goal normalized", new_goal_norm);
                attach("current goal normalized", goal_norm);
              }
            }
            if (noError())
            {
              Term *com = newComputation(arena, goal, new_goal);
              out->eq_proof = com;
            }
          }
        }
      }
      else if (in->new_goal)
      {// diff
        if (BuildTerm build_new_goal = buildTerm(arena, env, in->new_goal, holev))
        {
          new_goal = build_new_goal.term;
          CompareTerms compare = compareTerms(arena, env, goal, new_goal);
          if (compare.result == Trinary_True)
            parseError(in0, "new goal same as current goal");
          else
          {
            out->path = compare.diff_path;
            Term *from = subExpressionAtPath(goal, compare.diff_path);
            Term *to   = subExpressionAtPath(new_goal, compare.diff_path);
            // Term *eq_proof = 0;
            Term *eq = 0;

            if (Identifier *op_ident = castAst(in->eq_proof_hint, Identifier))
            {// operator hint
              TermArray op_overloads = getFunctionOverloads(env, op_ident, holev);
              for (int attempt=0; attempt < op_overloads.count; attempt++)
              {
                Term *hint = op_overloads.items[attempt];
                b32 hint_is_valid = false;
                Term *hint_type = getType(temp_arena, env, hint);
                if (Arrow *signature = castTerm(hint_type, Arrow))
                {
                  hint_is_valid = true;
                  eq = newEquality(temp_arena, env, from, to);
                  Term **temp_args = pushArray(temp_arena, signature->param_count, Term *, true);
                  if (unify(env, temp_args, signature->param_types, signature->output_type, eq))
                  {
                    // todo #cleanup copyArray
                    Term **args = pushArray(arena, signature->param_count, Term *);
                    for (int id=0; id < signature->param_count; id++)
                      args[id] = temp_args[id];
                    Composite *eq_proof_composite = newTerm(arena, Composite, 0);
                    eq_proof_composite->op        = hint;
                    eq_proof_composite->arg_count = signature->param_count;
                    eq_proof_composite->args      = args;
                    out->eq_proof = &eq_proof_composite->t;
                  }
                  else
                  {
                    parseError(in->eq_proof_hint, "unification failed");
                    attach("lhs", signature->output_type);
                    attach("rhs", eq);
                    attach("goal", goal);
                    attach("serial", serial);
                  }
                }
                else if (isEquality(hint_type))
                {
                  eq = hint_type;
                  hint_is_valid = true;
                  out->eq_proof = hint;
                }

                if (!hint_is_valid)
                {
                  parseError(in->eq_proof_hint, "invalid proof pattern");
                  attach("type", hint_type);
                }

                if (op_overloads.count > 1)
                {
                  if (hasError())
                  {
                    wipeError();
                    if (attempt == op_overloads.count-1)
                      parseError(&op_ident->a, "found no suitable overload");
                  }
                  else break;
                }
              }
            }
            else if (BuildTerm build_eq_proof = buildTerm(arena, env, in->eq_proof_hint, holev))
            {// full proof of equality
              out->eq_proof = build_eq_proof.term;
              eq = getType(temp_arena, env, build_eq_proof.term);
              if (!isEquality(eq))
              {
                parseError(in->eq_proof_hint, "invalid proof pattern");
                attach("type", eq);
              }
            }

            if (noError())
            {
              auto [lhs,rhs] = getEqualitySides(eq);
              Term *from, *to;
              if (in->right_to_left) {from = rhs; to = lhs; out->right_to_left = true;}
              else                   {from = lhs; to = rhs;}
              Term *new_goal_check = rewriteTerm(arena, to, out->path, goal);
              if (!equal(env, new_goal, new_goal_check))
              {
                parseError(in0, "invalid full-rewrite");
                attach("original goal", goal);
                attach("expected rewrite result", new_goal);
                attach("actual rewrite result", new_goal_check);
                attach("rewrite from", from);
                attach("rewrite to", to);
              }
            }
          }
        }
      }
      else
      {// search
        if (BuildTerm eq_proof = buildTerm(arena, env, in->eq_proof_hint, holev))
        {
          out->eq_proof = eq_proof.term;
          Term *eq = getType(temp_arena, env, eq_proof.term);
          if (auto [from, to] = getEqualitySides(eq, false))
          {
            if (in->right_to_left) {auto tmp = from; from = to; to = tmp; out->right_to_left = true;}
            SearchOutput search = searchExpression(arena, env, from, goal);
            if (search.found)
            {
              out->path = search.path;
              new_goal = rewriteTerm(arena, to, out->path, goal);
            }
            else
            {
              parseError(in0, "substitution has no effect");
              attach("substitution", eq);
              attach("goal", goal);
            }
          }
          else
          {
            parseError(in->eq_proof_hint, "please provide a proof of equality that can be used for substitution");
            attach("got", eq);
            attach("goal", goal);
          }
        }
      }

      if (noError() && !recursed)
      {
        assert(new_goal);
        if (BuildTerm body = buildTerm(arena, env, in->body, new_goal))
        {
          out->body = body.term;
          out0.term = &out->t;
        }
      }
    } break;

    case AC_Let:
    {
      Let  *in = castAst(in0, Let);
      Term *type_hint = holev;
      if (in->type && in->type != LET_TYPE_NORMALIZE)
      {
        if (BuildTerm type = buildTerm(arena, env, in->type, holev))
          type_hint = type.term;
      }
      if (noError())
      {
        if (BuildTerm build_rhs = buildTerm(arena, env, in->rhs, type_hint))
        {
          Term *rhs = build_rhs.term;
          Term *rhs_type = getType(temp_arena, env, build_rhs.term);
          if (in->type == LET_TYPE_NORMALIZE)
          {// type coercion
            Term *norm_rhs_type = normalize(arena, env, rhs_type);
            Term *computation = newComputation(arena, norm_rhs_type, rhs_type);
            rhs_type = norm_rhs_type;
            rhs = newRewrite(arena, computation, build_rhs.term, 0, false);
            assert(equal(env, getType(temp_arena, env, rhs), rhs_type));
          }

          Token *token = &in0->token;
          Lambda *lambda = newAst(temp_arena, Lambda, token);
          lambda->body = in->body;
          ArrowAst *signature = newAst(temp_arena, ArrowAst, token);
          allocateArray(temp_arena, 1, signature->param_names);
          allocateArray(temp_arena, 1, signature->param_types);
          signature->param_count    = 1;
          signature->param_names[0] = in->lhs;
          signature->param_types[0] = synthesizeAst(temp_arena, rebase(temp_arena, rhs_type, 1), token);
          signature->output_type    = synthesizeAst(temp_arena, rebase(temp_arena, goal, 1), token);
          lambda->signature = &signature->a;

          Ast *rhs_ast = synthesizeAst(temp_arena, rhs, token);

          CompositeAst *com = newAst(arena, CompositeAst, token);
          allocateArray(temp_arena, 1, com->args);
          com->op        = &lambda->a;
          com->arg_count = 1;
          com->args[0]   = rhs_ast;

          recursed = true;
          out0 = buildTerm(arena, env, &com->a, goal);
        }
      }
    } break;

    case AC_ForkAst:
    {// no need to return value since nobody uses the value of a fork
      ForkAst *fork = castAst(in0, ForkAst);
      out0.term = buildFork(arena, env, fork, goal);
      recursed = true;
    } break;

    invalidDefaultCase;
  }

  if (noError() && (goal != holev) && should_check_type && !recursed)
  {// typecheck if needed
    Term *actual = getType(temp_arena, env, out0.term);
    if (!matchType(env, actual, goal))
    {
      parseError(in0, "actual type differs from expected type");
      attach("got", actual);
      attach("expected", goal);
      attach("serial", serial);
    }
  }

  if (ParseError *error = getError())
  {
    error->code = ErrorWrongType;
    out0 = {};
  }
  else
  {
    assert(out0);
  }
  return out0;
}

forward_declare internal Term *
buildFork(MemoryArena *arena, Typer *env, ForkAst *in, Term *goal)
{
  Fork *out = newTerm(arena, Fork, 0);
  out->case_count = in->case_count;
  i32 unused_variable serial = global_debug_serial++;
  // TODO don't allow users to fork something they obviously can't (like a
  // function).
  assert(goal);
  if (BuildTerm subject = buildTerm(arena, env, in->subject, holev))
  {
    out->subject = subject.term;
    s32 case_count = in->case_count;

    Term *subject_type = getType(arena, env, subject.term);
    if (Union *uni = castTerm(subject_type, Union))
    {
      if (uni->ctor_count == case_count)
      {
        Term **ordered_bodies = pushArray(arena, case_count, Term *, true);
        Typer *outer_env = env;

        for (s32 input_case_id = 0;
             input_case_id < case_count && noError();
             input_case_id++)
        {
          Typer env_ = *outer_env;
          Typer *env = &env_;
          Token *ctor_name = in->ctors + input_case_id;

          Constructor *ctor = 0;
          for (i32 id = 0; id < uni->ctor_count; id++)
          {
            if (equal(uni->ctors[id].name.string, ctor_name->string))
            {
              ctor = uni->ctors+id;
              break;
            }
          }

          if (ctor)
          {
            if (addConstructorMap(env, subject.term, ctor))
            {
              if (ordered_bodies[ctor->id])
              {
                parseError(in->bodies[input_case_id], "fork case handled twice");
                attach("constructor", &ctor->t);
              }
              else
              {
                if (BuildTerm body = buildTerm(arena, env, in->bodies[input_case_id], goal))
                {
                  ordered_bodies[ctor->id] = body.term;
                }
              }
            }
            else
              parseError(in->subject, "cannot fork this term");
          }
          else
            parseError(ctor_name, "expected a constructor");
        }

        if (noError())
        {
          out->uni    = uni;
          out->bodies = ordered_bodies;
        }
      }
      else
        parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                   uni->ctor_count, in->case_count);
    }
    else
    {
      parseError(in->subject, "cannot fork expression of type");
      attach("type", subject_type);
    }
  }
  if (noError())
  {
    for (i32 id=0; id < in->case_count; id++)
      assert(in->bodies[id]);
  }
  NULL_WHEN_ERROR(out);
  return &out->t;
}

#if 0
forward_declare inline void
doubleCheckType(Term *in0)
{
  switch (in0->cat)
  {
    case Term_Rewrite:
    {
      Rewrite *in = castTerm(in0, Rewrite);
      auto [lhs, rhs] = getEqualitySides(in->eq_proof->type);
      Term *rewrite_to = in->right_to_left ? rhs : lhs;
      Term *expected_type = rewriteTerm(temp_arena, rewrite_to, in->path, in->body->type);
      assert(equal(expected_type, in0->type));
    } break;

    default:
    {todoIncomplete;} break;
  }
}
#endif

forward_declare inline Term *
newRewrite(MemoryArena *arena, Term *eq_proof, Term *body, TreePath *path, b32 right_to_left)
{
  Rewrite *out = newTerm(arena, Rewrite, 0);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return &out->t;
}

inline BuildTerm
parseExpression(MemoryArena *arena, LocalBindings *bindings, Term *expected_type)
{
  BuildTerm out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Typer env = {};
    env.bindings = bindings;
    out = buildTerm(arena, &env, ast, expected_type);
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline BuildTerm
parseExpressionFull(MemoryArena *arena)
{
  return parseExpression(arena, 0, holev);
}

forward_declare internal FunctionDecl *
parseFunction(MemoryArena *arena, Token *name, b32 is_theorem)
{
  FunctionDecl *out = newAst(arena, FunctionDecl, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpressionToAst(arena))
  {
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      // NOTE: rebuild the function's local bindings from the signature

      if (requireChar('{', "open function body"))
      {
        if (Ast *body = parseSequence(arena, is_theorem, false))
        {
          if (requireChar('}'))
          {
            out->body      = body;
            out->signature = signature;
          }
        }
      }
    }
    else
      parseError(signature0, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare internal ForkAst *
parseFork(MemoryArena *arena, b32 is_theorem)
{
  ForkAst *out = 0;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpressionToAst(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *global_tokenizer;
    s32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      Token *ctors = pushArray(temp_arena, case_count, Token);
      Ast **bodies = pushArray(temp_arena, case_count, Ast*);

      s32 actual_case_count = 0;
      for (b32 stop = false;
           !stop && hasMore();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContext("fork case");
          i32 input_case_id = actual_case_count++;
          Token ctor = nextToken();
          if (isIdentifier(&ctor))
            ctors[input_case_id] = ctor;
          else
            parseError(&ctor, "expected a constructor name");

          if (requireChar(':', "syntax: CASE: BODY"))
          {
            b32 auto_normalize = is_theorem ? true : false;
            if (Ast *body = parseSequence(arena, is_theorem, auto_normalize))
            {
              bodies[input_case_id] = body;
              if (!optionalChar(','))
              {
                requireChar('}', "to end fork expression; or use ',' to end the fork case");
                stop = true;
              }
            }
          }
          popContext();
        }
      }

      if (noError())
      {
        assert(case_count == actual_case_count);
        out = newAst(arena, ForkAst, &token);
        out->a.token    = token;
        out->subject    = subject;
        out->case_count = case_count;
        out->bodies     = bodies;
        out->ctors      = ctors;
      }
    }
  }

  return out;
}

internal ArrowAst *
parseArrowType(MemoryArena *arena, b32 is_struct)
{
  ArrowAst *out = 0;

  s32     param_count;
  Token  *param_names;
  Ast   **param_types;
  Token marking_token = peekToken();
  char begin_arg_char = is_struct ? '{' : '(';
  char end_arg_char   = is_struct ? '}' : ')';
  if (requireChar(begin_arg_char))
  {
    Tokenizer tk_copy = *global_tokenizer;
    param_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      param_names   = pushArray(arena, param_count, Token);
      param_types   = pushArray(arena, param_count, Ast*);

      s32 parsed_param_count = 0;
      s32 typeless_run = 0;
      Token typeless_token;
      for (b32 stop = false;
           !stop && hasMore();
           )
      {
        Token param_name_token = nextToken();
        if (equal(&param_name_token, end_arg_char))
          stop = true;

        else if (isIdentifier(&param_name_token))
        {
          s32 param_id = parsed_param_count++;
          param_names[param_id] = param_name_token;

          if (optionalChar(':'))
          {
            if (Ast *param_type = parseExpressionToAst(arena))
            {
              param_types[param_id] = param_type;
              if (typeless_run)
              {
                for (s32 offset = 1;
                     offset <= typeless_run;
                     offset++)
                {
                  param_types[param_id - offset]  = param_type;
                }
                typeless_run = 0;
              }

              Token delimiter = nextToken();
              if (equal(&delimiter, end_arg_char))
                stop = true;
              else if (!equal(&delimiter, ','))
                tokenError("unexpected token after parameter type");
            }
          }
          else if (requireChar(',', "delimit after typeless parameter name"))
          {
            typeless_run++;
            typeless_token = param_name_token;
          }
          else
            stop = true;
        }
        else
          tokenError("expected parameter name");
      }
      if (noError())
      {
        assert(parsed_param_count == param_count);
        if (typeless_run)
        {
          parseError(&typeless_token, "please provide types for all parameters");
        }
      }
    }
  }

  if (noError())
  {
    out = newAst(arena, ArrowAst, &marking_token);
    out->param_count = param_count;
    out->param_names = param_names;
    out->param_types = param_types;
    if (!is_struct)  // structs don't need return type
    {
      if (requireCategory(TC_Arrow, "syntax: (param: type, ...) -> ReturnType"))
      {
        if (Ast *return_type = parseExpressionToAst(arena))
          out->output_type = return_type;
      }
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline s32
parseInt32()
{
  Token token = nextToken();
  s32 out = 0;
  char first_char = token.string.chars[0];
  if ('0' <= first_char && first_char <= '9')
  {
    for (int char_id=0; char_id < token.string.length; char_id++)
    {
      char c = token.string.chars[char_id];
      if ('0' <= c && c <= '9')
      {
        out += out*10 + (c - '0');
      }
      else
        invalidCodePath;
    }
  }
  else
    tokenError("expected a 32-bit integer");
  return out;
}

inline b32
areSequential(Token *first, Token *next)
{
  return next->string.chars == first->string.chars + first->string.length;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  Ast *operand = 0;
  Token token = nextToken();
  if (equal(&token, '_'))
  {
    operand = &newAst(arena, Hole, &token)->a;
  }
  else if (isIdentifier(&token))
  {// token combination. TODO combine more than 2, allow combination in local
   // scope.
    Token next = peekToken();
    Token *tokenp = &token;
    Token combined_token = token;
    if (isIdentifier(&next) &&
        areSequential(&token, &next))
    {
      combined_token.string.length += next.string.length;
      if (lookupGlobalNameSlot(combined_token.string, false))
      {
        nextToken();
        tokenp = &combined_token;
      }
    }

    operand = &newAst(arena, Identifier, tokenp)->a;
  }
  else if (equal(&token, '('))
  {
    operand = parseExpressionToAst(arena);
    requireChar(')');
  }
  else
    tokenError("expected start of expression");

  while (hasMore())
  {
    if (optionalChar('('))
    {// function call syntax, let's keep going
      Ast *op = operand;

      Tokenizer tk_copy = *global_tokenizer;
      s32 expected_arg_count = getCommaSeparatedListLength(&tk_copy);
      if (noError(&tk_copy))
      {
        Ast **args = pushArray(arena, expected_arg_count, Ast*);
        CompositeAst *branch = newAst(arena, CompositeAst, &op->token);
        branch->op        = op;
        branch->arg_count = expected_arg_count;
        branch->args      = args;
        operand = &branch->a;
        s32 parsed_arg_count = 0;
        for (s32 stop = false;
             hasMore () && !stop;
             )
        {
          if (optionalChar(')'))
            stop = true;
          else
          {
            s32 arg_id = parsed_arg_count++;
            Ast *arg = parseExpressionToAst(arena);
            if (hasMore())
            {
              args[arg_id] = arg;
              if (!optionalChar(','))
              {
                requireChar(')', "expected ',' or ')'");
                stop = true;
              }
            }
          }
        }
        if (hasMore())
        {
          assert(parsed_arg_count == expected_arg_count);
        }
      }
    }
    else if (optionalChar('.'))
    {// member accessor
      AccessorAst *accessor = newAst(arena, AccessorAst, &global_tokenizer->last_token);
      accessor->record      = operand;
      if (requireIdentifier("expected identifier as field name"))
      {
        accessor->field_name = global_tokenizer->last_token;
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
  if (requireChar('(', "", tk))
    if (eatUntilMatchingPair(tk))
      out = nextToken(tk).cat == TC_Arrow;
  return out;
}

inline b32 seesLambda()
{// todo we don't allow naming parameters in here yet
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (requireChar('_', 0, tk))
  {
    if (requireCategory(TC_StrongArrow, 0, tk))
      out = true;
  }
  return out;
}

internal Lambda *
parseLambda(MemoryArena *arena)
{
  pushContext("lambda: _ => {SEQUENCE}");
  nextToken(); nextToken();
  Lambda *out = newAst(arena, Lambda, &global_tokenizer->last_token);
  if (requireChar('{'))
  {
    out->body = parseSequence(arena, true, false);
    requireChar('}');
  }
  popContext();
  return out;
}

internal Ast *
parseExpressionToAstMain(MemoryArena *arena, ParseExpressionOptions opt)
{
  Ast *out = 0;
  if (seesArrowExpression())
    out = &parseArrowType(arena, false)->a;
  else if (seesLambda())
    out = &parseLambda(arena)->a;
  else
  {
    if (Ast *operand = parseOperand(arena))
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
          s32 precedence = precedenceOf(op_token.string);
          if (precedence >= opt.min_precedence)
          {
            // recurse
            nextToken();
            // a + b * c
            //      ^
            ParseExpressionOptions opt1 = opt;
            opt1.min_precedence = precedence;
            if (Ast *recurse = parseExpressionToAstMain(arena, opt1))
            {
              s32 arg_count = 2;
              Ast **args    = pushArray(arena, arg_count, Ast*);
              args[0] = operand;
              args[1] = recurse;

              CompositeAst *new_operand = newAst(arena, CompositeAst, &op_token);
              new_operand->op        = &op->a;
              new_operand->arg_count = arg_count;
              new_operand->args      = args;
              operand = &new_operand->a;
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
          stop = true;
        else
          tokenError(&op_token, "expected operator token");
      }
      if (noError())
        out = operand;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare inline Ast *
parseExpressionToAst(MemoryArena *arena)
{
  return parseExpressionToAstMain(arena, ParseExpressionOptions{});
}

internal void
parseConstructor(MemoryArena *arena, Union *uni)
{
  s32 ctor_id = uni->ctor_count++;

  Constructor *ctor = uni->ctors + ctor_id;
  initTerm(&ctor->t, Term_Constructor, 0);
  ctor->uni  = uni;
  ctor->name = nextToken();
  ctor->id   = ctor_id;

  if (isIdentifier(&ctor->name))
  {
    if (optionalChar(':'))
    {// subtype
      Arrow *struct_;
      pushContext("struct {FIELD: TYPE ...}");
      if (requireCategory(TC_Keyword_struct))
      {
        ArrowAst *ast = parseArrowType(arena, true);
        Typer env_ = {}; Typer *env = &env_;
        // todo there are hacks we have to do to accept arrow type without
        // output type, which is dumb since the output type exists.
        if (BuildTerm build = buildTerm(arena, env, &ast->a, holev))
          struct_ = castTerm(build.term, Arrow);
      }
      popContext();

      if (noError())
      {
        struct_->output_type = &uni->t;
        ctor->type = &struct_->t;
        addGlobalBinding(&ctor->name, &ctor->t);
      }
    }
    else
    {// atomic constructor
      if (uni->type == &builtins.Set->t)
      {
        Arrow *signature = newTerm(arena, Arrow, 0);
        signature->output_type = &uni->t;
        ctor->type = &signature->t;
        Composite *record = newTerm(arena, Composite, 0);
        record->op = &ctor->t;
        addGlobalBinding(&ctor->name, &record->t);
      }
      else
        parseError(&ctor->name, "constructors must construct a set member");
    }
  }
  else
    tokenError("expected an identifier as constructor name");
}

internal void
parseUnion(MemoryArena *arena, Token *name)
{
  // NOTE: the type is in scope of its own constructor.
  Term *type = &builtins.Set->t;
  if (optionalChar(':'))
  {// type override
    Token type_token = global_tokenizer->last_token;
    b32 valid_type = false;
    if (BuildTerm type = parseExpressionFull(arena))
    {
      if (Arrow *arrow = castTerm(type.term, Arrow))
      {
        if (arrow->output_type == &builtins.Set->t)
          valid_type = true;
      }
      else if (type.term == &builtins.Set->t)
        valid_type = true;

      if (!valid_type)
      {
        parseError(&type_token, "form has invalid type");
        attach("type", type.term);
      }
    }
  }

  if (noError())
  {
    Union *uni = newTerm(arena, Union, type);
    addGlobalBinding(name, &uni->t);

    if (requireChar('{', "open typedef body"))
    {
      Tokenizer tk_copy = *global_tokenizer;
      s32 expected_ctor_count = getCommaSeparatedListLength(&tk_copy);
      // NOTE: init here for recursive definition
      if (noError(&tk_copy))
      {
        uni->ctors = pushArray(arena, expected_ctor_count, Constructor);
        while (noError())
        {
          if (optionalChar('}'))
            break;
          else
          {
            parseConstructor(arena, uni);
            if (!optionalChar(','))
            {
              requireChar('}', "to end the typedef; or you might want a comma ',' to delimit constructors");
              break;
            }
          }
        }

        if (noError())
          assert(uni->ctor_count == expected_ctor_count);
      }
    }
  }
}

internal Function *
buildGlobalFunction(MemoryArena *arena, Typer *env, FunctionDecl *decl)
{
  Function *funv = 0;
  if (BuildTerm build_signature = buildTerm(arena, env, &decl->signature->a, holev))
  {
    Arrow *signature = castTerm(build_signature.term, Arrow);
    funv = newTerm(arena, Function, build_signature.term);
    funv->body = &dummy_function_being_built;

    // note: add binding first to support recursion
    addGlobalBinding(&decl->a.token, &funv->t);

    if (noError())
    {
      introduceSignature(env, signature, true);
      // Term *expected_body_type = evaluateArrow(temp_arena, env, signature, env->stack->items, signature->output_type);
      if (BuildTerm body = buildTerm(arena, env, decl->body, signature->output_type))
        funv->body = body.term;
      unwindBindingsAndStack(env);
    }
  }
  return funv;
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  MemoryArena *arena = state->arena;
  b32 should_fail_active = false;
  Typer empty_env_ = {}; Typer *empty_env = &empty_env_;

  Token token = nextToken(); 
  while (hasMore())
  {
    if (global_tokenizer->context == (ParseContext*)0x37)
      breakhere;

#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
#endif

    if (equal(&token, '#'))
    {// compile directive
      token = nextToken();
      switch (MetaDirective directive = matchMetaDirective(&token))
      {
        case MetaDirective_NULL:
        {
          tokenError("unknown meta directive");
        } break;

        case MetaDirective_load:
        {
          pushContext("#load");
          Token file = nextToken();
          if (file.cat != TC_StringLiteral)
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
                 file_list = file_list->next)
            {
              if (equal(file_list->first_path, load_path))
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
        } break;

        case MetaDirective_should_fail:
        {
          if (optionalString("off"))
            should_fail_active = false;
          else
          {
            should_fail_active = true;
            tokenError(&token, "#should_fail activated");
            getError()->code = ErrorWrongType;
          }
        } break;

        case MetaDirective_debug:
        {
          if (optionalString("off"))
            global_debug_mode = false;
          else
            global_debug_mode = true;
        } break;

        invalidDefaultCase;
      }
    }
    else
    {
      switch (token.cat)
      {
        case TC_Keyword_test_eval:
        {
          if (BuildTerm expr = parseExpressionFull(temp_arena))
            normalize(arena, 0, expr.term);
        } break;

        case TC_Keyword_print:
        {
          u32 flags = PrintFlag_Detailed|PrintFlag_PrintType;
          if (optionalString("lock_detailed"))
            setFlag(&flags, PrintFlag_LockDetailed);
          if (BuildTerm expr = parseExpressionFull(temp_arena))
          {
            Term *norm = normalize(arena, 0, expr.term);
            print(0, norm, {.flags=flags});
            print(0, "\n");
          }
        } break;

        case TC_Keyword_print_raw:
        {
          if (auto parsing = parseExpressionFull(temp_arena))
            print(0, parsing.term, {.flags = (PrintFlag_Detailed     |
                                              PrintFlag_LockDetailed |
                                              PrintFlag_PrintType)});
          print(0, "\n");
        } break;

        case TC_Keyword_print_ast:
        {
          if (Ast *exp = parseExpressionToAst(temp_arena))
            print(0, exp, {.flags = PrintFlag_Detailed});
        } break;

        case TC_Keyword_check:
        {
          Term *expected_type = 0;
          if (Ast *ast = parseExpressionToAst(temp_arena))
          {
            if (optionalChar(':'))
            {
              if (BuildTerm type = parseExpressionFull(temp_arena))
                expected_type = type.term;
            }
            if (noError())
              buildTerm(temp_arena, empty_env, ast, expected_type);
          }
        } break;

        case TC_Keyword_check_truth:
        {
          pushContext("check_truth EQUALITY");
          if (Term *goal = parseExpressionFull(temp_arena).term)
          {
            if (Composite *eq = castTerm(goal, Composite))
            {
              b32 goal_valid = false;
              if (eq->op == &builtins.equal->t)
              {
                goal_valid = true;
                Term *lhs = normalize(temp_arena, 0, eq->args[1]);
                Term *rhs = normalize(temp_arena, 0, eq->args[2]);
                if (!equal(0, lhs, rhs))
                {
                  parseError(&token, "equality cannot be proven by computation");
                  setErrorCode(ErrorWrongType);
                  Term *lhs = normalize(temp_arena, 0, eq->args[1]);
                  attach("lhs", lhs);
                  attach("rhs", rhs);
                }
              }
              if (!goal_valid)
              {
                parseError(&token, "computation can only prove equality");
                attach("got", goal);
              }
            }
          }
          popContext();
        } break;

        default:
        {
          if (isIdentifier(&token))
          {
            Token after_name = nextToken();
            if (isIdentifier(&after_name) &&
                areSequential(&token, &after_name))
            {// token combination
              token.string.length += after_name.string.length;
              after_name = nextToken();
            }

            switch (after_name.cat)
            {
              case TC_ColonEqual:
              {
                pushContext("constant definition: CONSTANT := VALUE;");
                if (BuildTerm rhs = parseExpressionFull(arena))
                {
                  addGlobalBinding(&token, rhs.term);
                  requireChar(';');
                }
                popContext();
              } break;

              case TC_DoubleColon:
              {
                Token after_dcolon = peekToken();
                if (equal(after_dcolon.string, "union"))
                {
                  nextToken();
                  parseUnion(arena, &token);
                }
                else
                {
                  b32 is_theorem;
                  if (equal(after_dcolon.string, "fn"))
                  {
                    is_theorem = false;
                    nextToken();
                  }
                  else is_theorem = true;
                  if (FunctionDecl *fun = parseFunction(arena, &token, is_theorem))
                    buildGlobalFunction(arena, empty_env, fun);
                }
              } break;

              case ':':
              {
                if (BuildTerm type = parseExpressionFull(arena))
                {
                  if (requireCategory(TC_ColonEqual, "require :=, syntax: name : type := value"))
                  {
                    if (BuildTerm rhs = parseExpression(arena, 0, type.term))
                      addGlobalBinding(&token, rhs.term);
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
    }

#if CLEAN_TEMPORARY_MEMORY
    endTemporaryMemory(top_level_temp);
#endif

    if (should_fail_active)
    {
      if (noError())
        tokenError(&token, "#should_fail active but didn't fail");
      else if (getError()->code == ErrorWrongType)
        wipeError(global_tokenizer);
    }

    token = nextToken();
    while (equal(token.string, ";"))
    {// todo: should we do "eat all semicolons after the first one?"
      token = nextToken();
    }
  }
}

forward_declare internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  MemoryArena *arena = state->arena;
  b32 success = true;
#define REA_PROFILE 0
#if REA_PROFILE
  auto begin_time = platformGetWallClock(arena);
#endif

  ReadFileResult read = platformReadEntireFile(input_path.path);
  if (read.content)
  {
    auto new_file_list           = pushStruct(arena, FileList);
    new_file_list->first_path    = input_path.path;
    new_file_list->first_content = read.content;
    new_file_list->next          = state->file_list;
    state->file_list             = new_file_list;

    Tokenizer  tk_ = newTokenizer(input_path.directory, read.content);
    Tokenizer *tk  = &tk_;

    Tokenizer *old_tokenizer = global_tokenizer;
    global_tokenizer         = tk;

    if (is_root_file)
    {
      printf("Interpreting file %s...\n", input_path.file);
    }
    parseTopLevel(state);
    if (ParseError *error = tk->error)
    {
      success = false;
      printf("%s:%d:%d: [%s] ",
             input_path.path,

             error->line,
             error->column,

             error->context ? error->context : "");
      print(0, error->message);

      if (error->attachment_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attachment_count;
             attached_id++)
        {
          auto attachment = error->attachments[attached_id];
          printf("%s: %s", attachment.key, attachment.value);
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
      printf("----------------\n");
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

  return success;
}

forward_declare inline BuildTerm
parseExpressionFromString(MemoryArena *arena, char *string)
{
  Tokenizer tk = newTokenizer(String{}, 0);
  Tokenizer *tk_save = global_tokenizer;
  global_tokenizer = &tk;
  tk.at = string;
  BuildTerm out = parseExpressionFull(arena);
  global_tokenizer = tk_save;
  return out;
}

internal b32
beginInterpreterSession(MemoryArena *arena, char *initial_file)
{
  global_debug_mode = false;
  EngineState *state = pushStruct(arena, EngineState);
  state->arena = arena;

  {
    global_bindings = pushStruct(arena, GlobalBindings);  // :global-bindings-zero-at-startup

    builtins = {};
    {// Type and Set
      // Token superset_name = newToken("Type");
      builtins.Type = newTerm(arena, Builtin, 0);
      builtins.Type->type = &builtins.Type->t; // NOTE: circular types
      addBuiltinGlobalBinding("Type", &builtins.Type->t);

      builtins.Set = newTerm(arena, Builtin, &builtins.Type->t);
      addBuiltinGlobalBinding("Set", &builtins.Set->t);
    }

    {// more builtins
      Tokenizer builtin_tk = newTokenizer(print(temp_arena, "<builtin>"), 0);
      global_tokenizer = &builtin_tk;
      builtin_tk.at = "(_A: Set, a, b: _A) -> Set";
      BuildTerm equal_type = parseExpressionFull(arena); 
      builtins.equal = newTerm(arena, Builtin, equal_type.term);
      addBuiltinGlobalBinding("=", &builtins.equal->t);

      EngineState builtin_engine_state = EngineState{.arena=arena};
      builtin_tk.at = "True :: union { truth }";
      parseTopLevel(&builtin_engine_state);
      assert(noError());
      builtins.True  = castTerm(lookupBuiltinGlobalName("True"), Union);
      builtins.truth = castTerm(lookupBuiltinGlobalName("truth"), Constructor);
      builtin_tk.at = "False :: union { }";
      parseTopLevel(&builtin_engine_state);
      builtins.False = castTerm(lookupBuiltinGlobalName("False"), Union);
    }
    resetArena(temp_arena);
  }

  FilePath input_path = platformGetFileFullPath(arena, initial_file);
  b32 success = interpretFile(state, input_path, true);

  for (FileList *file_list = state->file_list;
       file_list;
       file_list = file_list->next)
  {
    platformFreeFileMemory(file_list->first_content);
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

  assert(arrayCount(keywords)       == TC_Keyword_END - TC_Keyword_START);
  assert(arrayCount(metaDirectives) == MetaDirective_COUNT);

  void   *permanent_memory_base = (void*)teraBytes(2);
  size_t  permanent_memory_size = megaBytes(256);
  permanent_memory_base = platformVirtualAlloc(permanent_memory_base, permanent_memory_size);
  MemoryArena  permanent_arena_ = newArena(permanent_memory_size, permanent_memory_base);
  global_arena  = &permanent_arena_;

  void   *temp_memory_base = (void*)teraBytes(3);
  size_t  temp_memory_size = megaBytes(2);
  temp_memory_base = platformVirtualAlloc(temp_memory_base, permanent_memory_size);
  MemoryArena temp_arena_ = newArena(temp_memory_size, temp_memory_base);
  temp_arena              = &temp_arena_;

#if 1
  if (!beginInterpreterSession(global_arena, "../data/basics.rea"))
    success = false;
  resetArena(global_arena, true);
#endif

#if 1
  if (!beginInterpreterSession(global_arena, "../data/test.rea"))
    success = false;
  resetArena(global_arena, true);
#endif

  return success;
}

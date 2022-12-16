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

#if 0
global_variable i32 last_global_id;
inline GlobalId nextGlobalId()
{
  i32 id = ++last_global_id;
  return GlobalId{id};
}
#endif

inline Value *
newEquality(MemoryArena *arena, Value *lhs, Value *rhs)
{
  Composite *eq = newTerm(arena, Composite, &builtins.Set->t);
  allocateArray(arena, 3, eq->args);
  eq->op        = &builtins.equal->t;
  eq->arg_count = 3;
  eq->args[0]   = lhs->type;
  eq->args[1]   = lhs;
  eq->args[2]   = rhs;
  return &eq->t;
}

// todo #typesafe error out when the sides don't match
inline Term *
newComputation(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Term *type = newEquality(arena, lhs, rhs);
  Computation *out = newTerm(arena, Computation, type);
  out->lhs = lhs;
  out->rhs = rhs;
  return &out->t;
}

inline ValuePair
getEqualitySides(Value *eq0, b32 must_succeed=true)
{
  ValuePair out = {};
  Composite *eq = castTerm(eq0, Composite);
  if (eq->op == &builtins.equal->t)
    out = ValuePair{eq->args[1], eq->args[2]};
  else if (must_succeed)
  {
    invalidCodePath;
  }
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
    case Term_FakeValue:
    {
      // FakeValue *in = castTerm(in0, FakeValue);
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
getType(Term *term)
{
#if 0
  if (isFree(term, 0))
  {
    dump(); print(0, term, PrintOptions{.detailed=true}); dump();
    global_debug_mode = true;
    isFree(term, 0);
    invalidCodePath;
  }
#endif
  return term->type;
}

// todo #cleanup straighten out this "ok" situation
inline Term * getTypeOk(Term *term) {return term->type;}

inline void
setType(Term *term, Term *type)
{
  // assert(!isFree(term, 0));
  term->type = type;
}

inline void setTypeOk(Term *term, Term *type) {term->type = type;}

inline i32
getStackDepth(Environment *env)
{
  return (env->stack ? env->stack->depth : 0);
}

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
  // todo #copy-paranoia
  if (out0 != in0)
    setType(out0, deepCopy(arena, getTypeOk(out0)));
  return out0;
}

inline LocalBindings *
extendBindings(MemoryArena *arena, Environment *env)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->next     = env->bindings;
  out->arena    = arena;
  out->count    = 0;
  env->bindings = out;
  return out;
}

inline LocalBindings * extendBindings(Environment *env) {return extendBindings(temp_arena, env);}

forward_declare inline void
dump(Trinary trinary)
{
  if (trinary.v == Trinary_True) dump("True");
  else if (trinary.v == Trinary_False) dump("False");
  else dump("Unknown");
}

inline OverwriteRules *
newOverwriteRule(Environment *env, Term *lhs, Term *rhs)
{
  OverwriteRules *out = pushStruct(temp_arena, OverwriteRules);
  out->lhs  = lhs;
  out->rhs  = rhs;
  out->next = env->overwrite;
  return out;
}

inline void
unwindStack(Environment *env)
{
  env->stack = env->stack->outer;
}

inline void
unwindBindingsAndStack(Environment *env)
{
  env->bindings = env->bindings->next;
  unwindStack(env);
}

inline void
dump(OverwriteRules *rewrite)
{
  for (; rewrite; rewrite = rewrite->next)
  {
    print(0, rewrite->lhs, {});
    print(0, " => ");
    print(0, rewrite->rhs, {});
    if (rewrite->next)
      print(0, ", ");
  }
}

forward_declare inline void dump(Term *in0) {print(0, in0, {});}
forward_declare inline void dump(Ast *in0) {print(0, in0, {});}

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

inline void checkStack(Stack *stack)
{
  TemporaryMemory tmp = beginTemporaryMemory(temp_arena);
  MemoryArena buffer = subArena(temp_arena, 1024);
  print(&buffer, stack);
  endTemporaryMemory(tmp);
}

inline void checkStack(Environment *env) { checkStack(env->stack); }

inline void
dump(Environment *env)
{
  dump("stack: ");
  dump(env->stack);
  dump(", rewrites: ");
  dump(env->overwrite);
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
    Value *op_value = in->op;

    if (Constant *op_constant = castTerm(in->op, Constant))
      op_value = op_constant->value;

    if (op_value)
    {
      op_signature = castTerm(op_value->type, Arrow);
      assert(op_signature);
      if (Value *anchor = op_value->anchor)
        if (Constant *op_constant = castTerm(anchor, Constant))
          precedence = precedenceOf(op_constant->name);
    }
  }
  else
  {
    CompositeAst *in = castAst(ast, CompositeAst);
    op       = in->op;
    raw_args = (void **)in->args;
    arg_count = in->arg_count;

    precedence = precedenceOf(in->op->token);
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
      case AC_Null:
      {print(buffer, "<NULL>");} break;

      case AC_Hole:
      {print(buffer, "_");} break;

      case AC_Identifier:
      {print(buffer, in0->token);} break;

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
          print(buffer, in->param_names[param_id]);
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
        print(buffer, in->field_name);
      } break;

      case AC_FunctionDecl: {print(buffer, "function decl");} break;

      case AC_Lambda: {print(buffer, "lambda");} break;

      case AC_Let:
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

inline String
globalNameOf(Value *value)
{
  if (Term *anchor = value->anchor)
    if (Constant *constant = castTerm(anchor, Constant))
      return constant->name.string;
  return {};
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
        print(buffer, in->name);
        if (global_debug_mode)
          print(buffer, "[%d]", in->stack_frame);
      } break;

      case Term_Constant:
      {
        Constant *in = castTerm(in0, Constant);
        print(buffer, in->name);
      } break;

      case Term_Hole:
      {print(buffer, "_");} break;

      case Term_Composite:
      {printComposite(buffer, in0, true, new_opt);} break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        print(buffer, globalNameOf(in0));
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
              print(buffer, getTypeOk(&ctor->t), new_opt);
            }
            print(buffer, " }");
          }
        }
      } break;

      case Term_Function:
      {
        Function *in = castTerm(in0, Function);
        b32 is_anonymous = false;
        if (String name = globalNameOf(in0))
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
          print(buffer, in->param_names[param_id]);
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
        // Constructor *in = castTerm(in0, Constructor);
        print(buffer, globalNameOf(in0));
      } break;

      case Term_Rewrite:
      {
        Rewrite *rewrite = castTerm(in0, Rewrite);
        print(buffer, rewrite->type, new_opt);
        skip_print_type = true;
        print(buffer, " <=>");
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, rewrite->body->type, new_opt);
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
        print(buffer, getTypeOk(rewrite->body), new_opt);
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
      print(buffer, getTypeOk(in0), new_opt);
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

inline void
extendStack(Environment *env, i32 cap, Value **items)
{
  Stack *stack = pushStruct(temp_arena, Stack, true);
  stack->depth = getStackDepth(env) + 1;
  stack->outer = env->stack;
  stack->cap   = cap;
  if (items)
  {
    stack->count = cap;
    stack->items = items;
  }
  else
    allocateArray(temp_arena, cap, stack->items);
  env->stack = stack;
}

inline void
addToStack(Environment *env, Value *value)
{
  i32 id = env->stack->count++;
  assert(id < env->stack->cap);
  env->stack->items[id] = value;
}

inline b32
equal(Term *lhs, Term *rhs)
{
  return equalTrinary(lhs, rhs).v == Trinary_True;
}

inline b32
isCompositeConstructor(Term *in0)
{
  if (Composite *in = castTerm(in0, Composite))
    return in->op->cat == Term_Constructor;
  else
    return false;
}

internal Value *
evaluateWithArgs(MemoryArena *arena, Environment *env, i32 arg_count, Value **args, Term *in0)
{
  extendStack(env, arg_count, args);
  Value *out = evaluate(arena, env, in0);
  unwindStack(env);
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

internal b32
isOverwritable(Term *in)
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
    case Term_Constant:
    {return false;} break;
  }
}

internal Term *
overwriteTerm(Environment *env, Term *in)
{
  Term *out = in;
  if (true || isOverwritable(in))
  {
    for (OverwriteRules *rewrite = env->overwrite;
         rewrite;
         rewrite = rewrite->next)
    {
      if (equal(in, rewrite->lhs))
      {
        out = rewrite->rhs;
        break;
      }
    }
  }
  return out;
}

forward_declare internal Value *
evaluate(MemoryArena *arena, Environment *env, Term *in0, i32 offset)
{
  Value *out0 = 0;
  i32 serial = global_debug_serial++;
  b32 debug = true;
  if (serial == 17176)
    breakhere;
  if (debug && global_debug_mode)
  {debugIndent(); DUMP("evaluate(", serial, "): ", in0, "\n");}
  switch (in0->cat)
  {
    case Term_Variable:
    {
      Variable *in = castTerm(in0, Variable);
      assert(in->stack_frame >= 0 && in->id >= 0);
      Stack *stack = env->stack;
      out0 = in0;
      if (!in->is_absolute)
      {
        i32 stack_delta = in->stack_frame - offset;
        if (stack_delta >= 0)
        {
          for (i32 delta = 0; delta < stack_delta; delta++)
          {
            stack = stack->outer;
            if (!stack)
            {
              dump(env->stack); dump();
              invalidCodePath;
            }
          }
          if (in->id < stack->count)
            out0 = stack->items[in->id];
          else
          {
            dump(env->stack); dump();
            invalidCodePath;
          }
        }
      }
    } break;

    case Term_Composite:
    {
      Composite *in  = castTerm(in0, Composite);
      Composite *out = newTerm(arena, Composite, 0);
      i32 arg_count = in->arg_count;
      allocateArray(arena, arg_count, out->args);
      out->arg_count = in->arg_count;
      for (i32 id=0; id < in->arg_count; id++)
        out->args[id] = evaluate(arena, env, in->args[id], offset);
      out->op = evaluate(arena, env, in->op, offset);

      Arrow *signature = castTerm(out->op->type, Arrow);
      if (!signature)
      {
        dump(); dump(env->stack); dump();
      }
      extendStack(env, arg_count, out->args);
      out->type = evaluate(arena, env, signature->output_type, offset);
      unwindStack(env);

      out0 = &out->t;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, out->param_count, out->param_types);
      for (int id=0; id < out->param_count; id++)
      {
        out->param_types[id] = evaluate(arena, env, in->param_types[id], offset+1);
      }
      out->output_type = evaluate(arena, env, out->output_type, offset+1);
      out0 = &out->t;
    } break;

    case Term_Accessor:
    {
      Accessor *in  = castTerm(in0, Accessor);
      Term *record0 = evaluate(arena, env, in->record, offset);
      record0 = overwriteTerm(env, record0);
      Composite *record = castTerm(record0, Composite);
      out0 = record->args[in->field_id];
    } break;

    case Term_Function:
    {
      Function *in = castTerm(in0, Function);
      Function *out = copyStruct(arena, in);
      out->type  = evaluate(arena, env, in->type, offset);
      Stack *stack = env->stack;
      for (i32 delta=0; delta < out->stack_delta; delta++)
        stack = stack->outer;
      out->stack = stack;
      out0 = &out->t;
    } break;

    case Term_Computation:
    {
      Computation *in  = castTerm(in0, Computation);
      Computation *out = copyStruct(arena, in);
      out->lhs  = evaluate(arena, env, in->lhs, offset);
      out->rhs  = evaluate(arena, env, in->rhs, offset);
      out->type = newEquality(arena, out->lhs, out->rhs);
      out0 = &out->t;
    } break;

    case Term_Rewrite:
    {
      Rewrite *in  = castTerm(in0, Rewrite);
      out0 = in0;
      if (Term *eq_proof = evaluate(arena, env, in->eq_proof, offset))
      {
        if (Term *body = evaluate(arena, env, in->body, offset))
        {
          auto [lhs, rhs] = getEqualitySides(getType(eq_proof));
          Term *rewrite_to  = in->right_to_left ? rhs : lhs;
          Term *type = rewriteTerm(arena, rewrite_to, in->path, getType(body));
          Rewrite *out = copyStruct(arena, in);
          out->type     = type;
          out->eq_proof = eq_proof;
          out->body     = body;
          doubleCheckType(&out->t);
          out0 = &out->t;
        }
      }
    } break;

    case Term_Fork:
    {
      Fork *in = castTerm(in0, Fork);
      Value *subject = evaluateAndNormalize(arena, env, in->subject, offset);
      switch (subject->cat)
      {// note: we fail if the fork is undetermined
        case Term_Constructor:
        {
          Constructor *ctor = castTerm(subject, Constructor);
          out0 = evaluate(arena, env, in->bodies[ctor->id], offset);
        } break;

        case Term_Composite:
        {
          Composite *record = castTerm(subject, Composite);
          if (Constructor *ctor = castTerm(record->op, Constructor))
            out0 = evaluate(arena, env, in->bodies[ctor->id], offset);
        } break;

        default:
        {
          // todo fork objects have to be returned
        } break;
      }
    } break;

    case Term_Constant:
    {
      Constant *in = castTerm(in0, Constant);
      out0 = in->value;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Hole:
    {out0=in0;} break;
  }
  if (!isSequenced(in0))
    assert(out0);
  if (debug && global_debug_mode)
  {debugDedent(); DUMP("=> ", out0, "\n");}
  return out0;
}

// todo #cleanup add offset to the environment
forward_declare inline Term *
evaluate(MemoryArena *arena, Environment *env, Term *in0)
{
  return evaluate(arena, env, in0, 0);
}

forward_declare internal CompareTerms
compareTerms(MemoryArena *arena, Term *lhs0, Term *rhs0)
{
  CompareTerms out = {};
  out.result.v = Trinary_Unknown;

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
        if ((lhs->stack_frame == rhs->stack_frame) && (lhs->id == rhs->id))
          out.result.v = Trinary_True;
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
            if (!equal(lhs->param_types[id], rhs->param_types[id]))
            {
              type_mismatch = true;
              break;
            }
          }
          if (!type_mismatch)
            out.result = equalTrinary(lhs->output_type, rhs->output_type);
        }
        else out.result.v = Trinary_False;
      } break;

      case Term_Composite:
      {
        Composite *lhs = castTerm(lhs0, Composite);
        Composite *rhs = castTerm(rhs0, Composite);

        Trinary op_compare = equalTrinary(lhs->op, rhs->op);
        if ((op_compare.v == Trinary_False) &&
            (lhs->op->cat == Term_Constructor) &&
            (rhs->op->cat == Term_Constructor))
        {
          out.result.v = Trinary_False;
        }
        else if (op_compare.v == Trinary_True)
        {
          Arrow *op_type = castTerm(getType(lhs->op), Arrow);
          s32 count = lhs->arg_count;
          assert(lhs->arg_count == rhs->arg_count);

          int mismatch_count = 0;
          int       unique_diff_id   = 0;
          TreePath *unique_diff_path = 0;
          out.result.v = Trinary_True;
          for (i32 id=0; id < count; id++)
          {
            if (!isHiddenParameter(op_type, id))
              // NOTE: #theory hidden parameters don' factor into comparison
            {
              CompareTerms recurse = compareTerms(arena, lhs->args[id], rhs->args[id]);
              if (recurse.result.v != Trinary_True)
              {
                mismatch_count++;
                if (mismatch_count == 1)
                {
                  unique_diff_id   = id;
                  unique_diff_path = recurse.diff_path;
                }
              }
            }
          }
          if (mismatch_count > 0)
            out.result.v = Trinary_Unknown;
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
        out.result = compareTerms(arena, lhs->record, rhs->record).result;
      } break;

      case Term_Builtin:
      {
        out.result.v = Trinary_True;
      } break;

      case Term_Constant:
      {
        Constant *lhs = castTerm(lhs0, Constant);
        Constant *rhs = castTerm(rhs0, Constant);
        // todo: are we supposed to be comparing terms or values?
        out = compareTerms(arena, lhs->value, rhs->value);
      } break;

      // todo: just say don't change the address?
      case Term_Function:
#if 0
      {
        Function *lhs = castTerm(lhs0, Function);
        Function *rhs = castTerm(rhs0, Function);
        if (lhs->id.v == rhs->id.v)
          out.result.v = Trinary_True;
      } break;
#else
      {} break;
#endif

      case Term_Hole:
      case Term_Union:
      case Term_Rewrite:
      case Term_Computation:
      case Term_Fork:
      {} break;
    }
  }
  else if (((lhs0->cat == Term_Constructor) && isCompositeConstructor(rhs0)) ||
           ((rhs0->cat == Term_Constructor) && isCompositeConstructor(lhs0)))
  {
    out.result.v = Trinary_False;
  }

  if (debug && global_debug_mode)
  {debugDedent(); dump("=> "); dump(out.result); dump();}
  return out;
}

forward_declare internal Trinary
equalTrinary(Term *lhs0, Term *rhs0)
{
  return compareTerms(0, lhs0, rhs0).result;
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

struct RewriteChain {
  Rewrite      *first;
  RewriteChain *next;
};

// todo #cleanup #mem don't allocate too soon
// todo normalize value (or term under value settings)
forward_declare internal Value *
normalize(MemoryArena *arena, Environment *env, Value *in0) 
{
  Value *out0 = {};

  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (debug && global_debug_mode)
  {debugIndent(); DUMP("normalize(", serial, "): ", in0, "\n");}

  switch (in0->cat)
  {
    case Term_Composite:
    {
      Composite *in = castTerm(in0, Composite);

      Term **norm_args = pushArray(arena, in->arg_count, Term*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Term *in_arg = in->args[arg_id];
        norm_args[arg_id] = normalize(arena, env, in_arg);
      }

      Term *norm_op = normalize(arena, env, in->op);
      if (norm_op->cat == Term_Function)
      {// Function application
        Function *funv = castTerm(norm_op, Function);
        if (funv->body != &dummy_function_being_built)
        {
          Stack *original_stack = env->stack;
          env->stack = funv->stack;
          extendStack(env, in->arg_count, norm_args);
          // note: evaluation might fail, in which case we back out.
          out0 = evaluate(arena, env, funv->body);
          if (out0)
            out0 = normalize(arena, env, out0);
          env->stack = original_stack;
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
          Trinary compare = equalTrinary(lhs, rhs);
          // I don't know how to handle inconsistency otherwise
          if (compare.v == Trinary_False)
            out0 = &builtins.False->t;
        }
      }

      if (!out0)
      {
        Composite *out = newTerm(arena, Composite, getTypeOk(in0));
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->t;
      }
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, out->param_count, out->param_types);
      for (i32 id=0; id < out->param_count; id++)
        out->param_types[id] = normalize(arena, env, in->param_types[id]);
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

    // todo #verify Accessors in normalization are just stubs.
    case Term_Accessor:
#if 1
    {
      out0 = in0;
    } break;
#else
    {
      out0 = in0;
      Accessor *in = castTerm(in0, Accessor);
      Term *record = normalize(arena, env, in->record);
      if (Composite *composite = castTerm(record, Composite))
        out0 = composite->args[in->field_id];
      else if (record != in->record)
      {
        Accessor *out = copyStruct(arena, in);
        out->record = record;
        out0 = &out->t;
      }
    } break;
#endif

    // todo #speed most of these don't need rewriting.
    case Term_Constant:
    case Term_Variable:
    case Term_Hole:
    case Term_Constructor:
    case Term_Builtin:
    case Term_Function:
    case Term_Union:
    case Term_Computation:
    case Term_Fork:
    {out0 = in0;} break;
  }

  // todo: migrate out of this overwrite model.
  out0 = overwriteTerm(env, out0);

  if (debug && global_debug_mode)
  {debugDedent(); dump("=> "); dump(out0); dump();}

  assert(out0);
  return out0;
}

inline b32
isGlobalValue(Value *value)
{
  switch (value->cat)
  {
    case Term_Hole:
    case Term_Variable:
    {return false;} break;

    case Term_Composite:
    {
      Composite *composite = castTerm(value, Composite);
      if (!isGlobalValue(composite->op))
        return false;

      for (int id=0; id < composite->arg_count; id++)
      {
        if (!isGlobalValue(composite->args[id]))
          return false;
      }

      return true;
    } break;

    case Term_Arrow:
    case Term_Function:
    {
      return false;  // TODO: don't know what to do so let's just say false for now.
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Constant:
    {return true;} break;

    case Term_Accessor:
    case Term_Rewrite:
    case Term_Computation:
    case Term_Fork:
    {
      invalidCodePath;
      return false;
    } break;
  }
}

#if 0
inline Term *
newConstant(MemoryArena *arena, Value *value)
{
  Constant *out = newTerm(arena, Constant, 0);
  String name = {};
  switch (value->cat)
  {
    case Term_Function:
    {
      name = castTerm(value, Function)->name;
    } break;
    case Term_Union:
    {
      name = castTerm(value, Union)->name;
    } break;
    case Term_Constructor:
    {
      name = castTerm(value, Constructor)->name;
    } break;
    case Term_Builtin:
    {
      name = castTerm(value, Builtin)->name;
    } break;
    default: {} break; // nameless things: such as composites like "1", "2"
  }
  out->value = value;
  out->name  = name;
  return &out->t;
}
#endif

internal Term *
toAbstractTerm(MemoryArena *arena, i32 env_depth, Value *in0, i32 offset)
{
  Term *out0 = 0;

  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (global_debug_mode && debug)
  {debugIndent(); DUMP("toAbstractTerm(", serial, "): ", in0, " with offset: ", offset, "\n");}

  if (in0->anchor)
  {
    out0 = toAbstractTerm(arena, env_depth, in0->anchor, offset);
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
        if (in->is_absolute && in->stack_frame > env_depth)
        {
          Variable *out = copyStruct(arena, in);
          out->stack_frame = env_depth + offset - in->stack_frame;
          out->is_absolute = false;
          out0 = &out->t;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        out->op        = toAbstractTerm(arena, env_depth, in->op, offset);
        allocateArray(arena, out->arg_count, out->args);
        for (i32 id=0; id < out->arg_count; id++)
          out->args[id] = toAbstractTerm(arena, env_depth, in->args[id], offset);
        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        allocateArray(arena, out->param_count, out->param_types);
        for (i32 id=0; id < out->param_count; id++)
          out->param_types[id] = toAbstractTerm(arena, env_depth, in->param_types[id], offset+1);
        if (out->output_type)
          out->output_type = toAbstractTerm(arena, env_depth, in->output_type, offset+1);
        out0 = &out->t;
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = newTerm(arena, Computation, 0);
        out->lhs  = toAbstractTerm(arena, env_depth, in->lhs, offset);
        out->rhs  = toAbstractTerm(arena, env_depth, in->rhs, offset);
        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyStruct(arena, in);
        out->record = toAbstractTerm(arena, env_depth, in->record, offset);
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in   = castTerm(in0, Rewrite);
        Rewrite *out  = copyStruct(arena, in);
        out->eq_proof = toAbstractTerm(arena, env_depth, in->eq_proof, offset);
        out->body     = toAbstractTerm(arena, env_depth, in->body, offset);
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
toPartiallyAbstractTerm(MemoryArena *arena, Environment *env, Term *in0)
{
  return toAbstractTerm(arena, getStackDepth(env), in0, 0);
}

forward_declare inline Term *
toAbstractTerm(MemoryArena *arena, Environment *env, Term *in0)
{
  return toAbstractTerm(arena, 0, in0, getStackDepth(env));
}

forward_declare internal Term *
evaluateAndNormalize(MemoryArena *arena, Environment *env, Term *in0, i32 offset)
{
  Term *eval = evaluate(arena, env, in0, offset);
  Term *norm = normalize(arena, env, eval);
  return norm;
}

inline b32
normalized(Environment *env, Term *in)
{
  Term *norm = normalize(temp_arena, env, in);
  return equal(in, norm);
}

inline void
addLocalBinding(Environment *env, Token *key)
{
  auto lookup = lookupCurrentFrame(env->bindings, key->string, true);
  lookup.slot->value = env->bindings->count++;
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

inline Value *
introduceRecord(MemoryArena *arena, Environment *env, Value *parent, Constructor *ctor)
{
  Value *out = 0;
  if (Arrow *ctor_sig = castTerm(ctor->type, Arrow))
  {
    i32 param_count = ctor_sig->param_count;
    Value *record_type = &ctor->uni->t;
    Composite *record = newTerm(arena, Composite, record_type);
    record->op        = &ctor->t;
    record->arg_count = param_count;
    record->args      = pushArray(arena, param_count, Value*);
    for (i32 field_id=0; field_id < param_count; field_id++)
    {
      String field_name = ctor_sig->param_names[field_id].string;
      Value *member_type = evaluateWithArgs(arena, env, param_count, record->args, ctor_sig->param_types[field_id]);
      Accessor *accessor = newTerm(arena, Accessor, member_type);
      accessor->record     = parent;
      accessor->field_id   = field_id;
      accessor->field_name = field_name;

      if (Constructor *field_ctor = getSoleConstructor(member_type))
      {// recursive case
        Value *intro = introduceRecord(arena, env, &accessor->t, field_ctor);
        record->args[field_id] = intro;
      }
      else  // base case
        record->args[field_id] = &accessor->t;
    }
    out = &record->t;
  }
  else
  {
    assert(ctor->type->cat == Term_Union);
    out = &ctor->t;
  }
  return out;
}

inline Term *
freshVariable(MemoryArena *arena, Environment *env, Token *name, Value *type)
{
  Variable *var = newTerm(arena, Variable, type);
  var->name        = *name;
  var->id          = env->stack->count; // :stack-ref-id-has-significance
  var->stack_frame = getStackDepth(env);
  var->is_absolute = true;
  assert(var->stack_frame);
  return &var->t;
}

forward_declare inline void
introduceOnStack(MemoryArena* arena, Environment *env, Token *name, Value *type)
{
  Value *intro;
  Term *var = freshVariable(arena, env, name, type);
  if (Constructor *type_ctor = getSoleConstructor(type))
    intro = introduceRecord(arena, env, var, type_ctor);
  else
    intro = var;

  addToStack(env, intro);
}

inline void
bindToStack(MemoryArena* arena, Environment *env, Token *name, Value *value)
{
  Term *var = freshVariable(arena, env, name, value->type);
  value->anchor = var;
  addToStack(env, value);
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
addGlobalBinding(Token *name, Value *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(name->string, true);
  // TODO #cleanup check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));

  // note: kind of #hack because constants are terms, but it's harmless.
  Constant *constant = newTerm(global_arena, Constant, value->type);
  constant->name  = *name;
  constant->value = value;
  value->anchor   = &constant->t;
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
lookupLocalName(Environment *env, Token *token)
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
addOverwriteRule(Environment *env, Term *lhs0, Term *rhs0)
{
  b32 added = false;
  if (isOverwritable(lhs0))
  {
    if (!equal(lhs0, rhs0))
    {
      OverwriteRules *rewrite = newOverwriteRule(env, lhs0, rhs0);
      env->overwrite = rewrite;
      added= true;
    }
  }
  return added;
}

inline void
removeRewriteRule(Environment *env)
{
  env->overwrite = env->overwrite->next;
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
matchType(Environment *env, Term *actual, Term *expected)
{
  (void)env;
  b32 out = false;
  if (expected == holev) out = true;
  else
  {
    if (equal(actual, expected)) out = true;
  }
  return out;
}

internal b32
unify(Value **args, Term **types, Term *lhs0, Value *rhs0)
{
  b32 success = false;
  b32 debug = true;
  i32 debug_serial = global_debug_serial++;
  if (global_debug_mode && debug)
  {
    debugIndent(); dump("unify("); dump(debug_serial); dump(") ");
    dump(lhs0); dump(" with "); dump(rhs0); dump();
    breakhere;
  }
  switch (lhs0->cat)
  {
    case Term_Variable:
    {
      Variable *lhs = castTerm(lhs0, Variable);
      if (lhs->stack_frame != 0)
        todoIncomplete;
      if (Term *replaced = args[lhs->id])
      {
        if (equal(replaced, rhs0))
          success = true;
      }
      else if (unify(args, types, types[lhs->id], getType(rhs0)))
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
        if (unify(args, types, lhs->op, rhs->op))
        {
          success = true;
          for (int id=0; id < lhs->arg_count; id++)
          {
            if (!unify(args, types, lhs->args[id], rhs->args[id]))
            {
              success = false;
              break;
            }
          }
        }
      }
    } break;

    case Term_Constant:
    {
      Constant *lhs = castTerm(lhs0, Constant);
      success = equal(lhs->value, rhs0);
    } break;

    default:
    {
      todoIncomplete;
    } break;
  }
  if (global_debug_mode && debug)
  {
    debugDedent(); dump("=>("); dump(debug_serial); dump(") ");
    if (success) dump("true"); else dump("false"); dump();
  }
  return success;
}

inline ValueArray
getFunctionOverloads(Environment *env, Identifier *ident, Value *output_type_goal)
{
  ValueArray out = {};
  if (auto local = lookupLocalName(env, &ident->token))
  {
    Stack *stack = env->stack;
    for (i32 delta=0; delta < local.stack_delta; delta++)
    {
      stack = stack->outer;
      if (!stack)
      {
        dump(env->stack); dump();
        invalidCodePath;
      }
    }
    if (local.var_id < stack->count)
    {
      out.count = 1;
      allocateArray(temp_arena, 1, out.items);
      out.items[0] = stack->items[local.var_id];
    }
    else
    {
      dump(env->stack); dump();
      invalidCodePath;
    }
  }
  else
  {
    if (GlobalBinding *slot = lookupGlobalNameSlot(ident->token, false))
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
          if (Arrow *signature = castTerm(getType(slot->items[slot_id]), Arrow))
          {
            b32 output_type_mismatch = false;
            // if (!isFree(signature->output_type, 0))
            {
              Value **args = pushArray(temp_arena, signature->param_count, Value*, true);
              if (!unify(args, signature->param_types, signature->output_type, output_type_goal))
                output_type_mismatch = true;
            }

            if (!output_type_mismatch)
              out.items[out.count++] = slot->items[slot_id];
          }
        }
      }
    }
  }
  return out;
}

internal SearchOutput
searchExpression(MemoryArena *arena, Term *lhs, Term* in0)
{
  SearchOutput out = {};
  if (equal(in0, lhs))
    out.found = true;
  else
  {
    switch (in0->cat)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        SearchOutput op = searchExpression(arena, lhs, in->op);
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
            SearchOutput arg = searchExpression(arena, lhs, in->args[arg_id]);
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
        out = searchExpression(arena, lhs, in->record);
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
      case Term_Constant:
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

#if 1
  if (auto_normalize)
  {
    count++;
    list = pushStruct(temp_arena, AstList);
    list->first = &newAst(arena, RewriteAst, &first_token)->a;
    list->next  = 0;
  }
#else
  (void)auto_normalize;
#endif

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
        if (equal(next, "<-"))
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

forward_declare internal Term *
buildFork(MemoryArena *arena, Environment *env, ForkAst *in, Term *goal)
{
  Fork *out = newTerm(arena, Fork, 0);
  out->case_count = in->case_count;
  i32 unused_variable serial = global_debug_serial++;
  // todo #cleanup: don't allow users to fork something they obviously can't
  // (like a function).
  assert(goal);
  if (BuildExpression subject = buildExpression(arena, env, in->subject, holev))
  {
    out->subject = subject.term;
    s32 case_count = in->case_count;

    if (Union *uni = castTerm(getType(subject.value), Union))
    {
      if (uni->ctor_count == case_count)
      {
        Term **ordered_bodies = pushArray(arena, case_count, Term *, true);
        Term *subjectv = subject.value;
        Environment *outer_env = env;

        for (s32 input_case_id = 0;
             input_case_id < case_count && noError();
             input_case_id++)
        {
          Environment env_ = *outer_env;
          Environment *env = &env_;
          Token *ctor_name = in->ctors + input_case_id;

          Constructor *ctor = 0;
          for (i32 id = 0; id < uni->ctor_count; id++)
          {
            if (equal(globalNameOf(&uni->ctors[id].t), ctor_name->string))
            {
              ctor = uni->ctors+id;
              break;
            }
          }

          if (ctor)
          {
            Term *record = introduceRecord(temp_arena, env, subjectv, ctor);
            addOverwriteRule(env, subjectv, record);
            if (ordered_bodies[ctor->id])
            {
              parseError(in->bodies[input_case_id], "fork case handled twice");
              attach("constructor", &ctor->t);
            }
            else
            {
              if (BuildExpression body = buildExpression(arena, env, in->bodies[input_case_id], goal))
              {
                ordered_bodies[ctor->id] = body.term;
              }
            }
          }
          else parseError(ctor_name, "expected a constructor");
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
      attach("type", getType(subject.value));
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

internal Value *
fillHole(MemoryArena *arena, Environment *env, Value *goal)
{
  Value *out = 0;
  if (Composite *eq = castTerm(goal, Composite))
  {
    if (eq->op == &builtins.equal->t)
    {
      if (equal(normalize(temp_arena, env, eq->args[1]),
                normalize(temp_arena, env, eq->args[2])))
      {
        out = newComputation(arena, eq->args[1], eq->args[2]);
      }
    }
  }
  return out;
}

forward_declare inline void
doubleCheckType(Value *in0)
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

inline Value *
newComposite(MemoryArena *arena, Environment *env, Value *op, i32 arg_count, Value **args)
{
  Arrow *signature = castTerm(op->type, Arrow);
  Value *type = evaluateWithArgs(arena, env, arg_count, args, signature->output_type);
  Composite *out = newTerm(arena, Composite, type);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;
  return &out->t;
}

inline Value *
newRewrite(MemoryArena *arena, Value *eq_proof, Value *body, TreePath *path, b32 right_to_left)
{
  auto [lhs, rhs] = getEqualitySides(eq_proof->type);
  Value *rewrite_to = right_to_left ? rhs : lhs;
  Value *type = rewriteTerm(arena, rewrite_to, path, body->type);
  Rewrite *out = newTerm(arena, Rewrite, type);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return &out->t;
}

forward_declare internal BuildExpression
buildExpression(MemoryArena *arena, Environment *env, Ast *in0, Value *goal)
{
  // todo #cleanup #mem: sort out what we need and what we don't need to persist
  // todo #cleanup #speed: returning the value is just a waste of time most of the time. Just call evaluate whenever you need the value.
  // todo #cleanup don't return a value
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 serial = global_debug_serial++;
  BuildExpression out0 = {};
  assert(goal);
  b32 should_check_type = true;
  b32 recursed = false;

  switch (in0->cat)
  {
    case AC_Hole:
    {
      // Holes are awesome, flexible placeholders that you can feed to the
      // typechecker to get what you want
      Term *fill = fillHole(arena, env, goal);
      if (fill)
      {
        out0.term  = toAbstractTerm(arena, env, fill);
        out0.value = fill;
      }
      else
      {
        parseError(in0, "expression required");
        attach("goal", goal);
        MemoryArena buffer_ = subArena(temp_arena, 1024);
        MemoryArena *buffer = &buffer_;
        attach("proof_context", (char *)buffer->base);
        assert(buffer->used == 0);
        print(buffer, "stack: ");
        print(buffer, env->stack);
      }
    } break;

    case AC_Identifier:
    {
      // Identifier *in = castAst(in0, Identifier);
      Token *name = &in0->token;
      if (LookupLocalName local = lookupLocalName(env, name))
      {
        Variable *ptr = newTerm(arena, Variable, 0);
        ptr->name        = in0->token;
        ptr->id          = local.var_id;
        ptr->stack_frame = local.stack_delta;
        out0.term  = &ptr->t;
        out0.value = evaluate(arena, env, &ptr->t);
      }
      else
      {
        Term *value = 0;
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (s32 value_id = 0; value_id < globals->count; value_id++)
          {
            Term *slot_value = globals->items[value_id];
            if (matchType(env, slot_value->type, goal))
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
              attach("actual_type", globals->items[0]->type);
          }
        }

        if (value)
        {
          should_check_type = false;
          assert(value->anchor);
          out0.term  = value->anchor;
          out0.value = value;
        }
      }
    } break;

    case AC_CompositeAst:
    {
      // i32 serial = global_debug_serial++;
      CompositeAst *in  = castAst(in0, CompositeAst);
      Composite    *out = newTerm(arena, Composite, 0);

      ValueArray op_overloads = {};
      if (Identifier *op_ident = castAst(in->op, Identifier))
        op_overloads = getFunctionOverloads(env, op_ident, goal);
      if (op_overloads.count == 0)
        parseError(in->op, "found no suitable overload");

      for (i32 attempt=0; attempt < op_overloads.count; attempt++)
      {
        Value *op = op_overloads.items[attempt];
        out->op = toAbstractTerm(arena, env, op);
        if (Arrow *signature = castTerm(op->type, Arrow))
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
            Value **args = pushArray(arena, in->arg_count, Term*);
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {
              Term *param_type0 = signature->param_types[arg_id];
              Term *expected_arg_type = evaluateWithArgs(temp_arena, env, in->arg_count, args, param_type0);

              // Typecheck & Inference for the arguments. TODO: inference is
              // hard-coded only for the equality.
              if (in->args[arg_id]->cat == AC_Hole)
              {
                if (Term *fill = fillHole(arena, env, expected_arg_type))
                  args[arg_id] = fill;
                else
                  args[arg_id] = holev;
              }
              else
              {
                if (BuildExpression arg = buildExpression(arena, env, in->args[arg_id], expected_arg_type))
                {
                  args[arg_id]      = arg.value;
                  if (expected_arg_type == holev)
                  {
                    Variable *param_type = castTerm(param_type0, Variable);
                    assert(param_type->stack_frame == 0);
                    args[param_type->id] = arg.value->type;
                  }
                }
              }
            }

            for (s32 arg_id = 0;
                 arg_id < in->arg_count && noError();
                 arg_id++)
            {
              if (args[arg_id]->cat == Term_Hole)
                parseError(in->args[arg_id], "Cannot fill hole");
            }

            if (noError())
            {
              out->arg_count = in->arg_count;
              allocateArray(arena, out->arg_count, out->args);
              for (i32 id = 0; id < out->arg_count; id++)
                out->args[id] = toAbstractTerm(arena, env, args[id]);

              out0.term  = &out->t;
              out0.value = evaluate(arena, env, &out->t);
            }
          }
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          attach("operator type", op->type);
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
      Arrow *value = newTerm(arena, Arrow, &builtins.Type->t);
      i32 param_count = in->param_count;
      value->param_count = param_count;
      value->param_names = in->param_names;
      allocateArray(arena, param_count, value->param_types);
      extendStack(env, param_count, 0);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < param_count && noError(); id++)
      {
        BuildExpression param_type = buildExpression(arena, env, in->param_types[id], holev);
        if (param_type)
        {
          value->param_types[id] = param_type.value;
          Token *name = in->param_names+id;
          introduceOnStack(arena, env, name, param_type.value);
          addLocalBinding(env, name);
        }
      }

      if (noError())
      {
        if (in->output_type)
        {
          if (BuildExpression output_type = buildExpression(arena, env, in->output_type, holev))
            value->output_type = output_type.value;
        }
      }
      unwindBindingsAndStack(env);

      if (noError())
      {
        out0.term  = toAbstractTerm(arena, env, &value->t);
        out0.value = toPartiallyAbstractTerm(arena, env, &value->t);
      }
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      Accessor *value = newTerm(arena, Accessor, 0);
      value->field_name = in->field_name;
      if (BuildExpression build_record = buildExpression(arena, env, in->record, holev))
      {
        Term *record0 = overwriteTerm(env, build_record.value);
        if (Composite *record = castTerm(record0, Composite))
        {
          value->record = build_record.value;
          Arrow *op_type = castTerm(getType(record->op), Arrow);
          s32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          for (s32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->field_name, op_type->param_names[param_id]))
            {
              value->field_id  = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
          {
            out0.term  = toAbstractTerm(arena, env, &value->t);
            out0.value = evaluate(arena, env, out0.term);
          }
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", record->op);
            attach("in type", op_type->output_type);
          }
        }
        else
          parseError(in->record, "cannot access a non-record");
      }
    } break;

    case AC_Lambda:
    {
      should_check_type = false;
      if (Arrow *signature = castTerm(goal, Arrow))
      {
        Lambda   *in  = castAst(in0, Lambda);
        Function *fun = newTerm(arena, Function, 0);
        fun->stack_delta = 0;
        fun->type        = toAbstractTerm(arena, env, &signature->t);  // not a real type, we don't use that field anyway.

        i32 param_count = signature->param_count;
        extendStack(env, param_count, 0);
        extendBindings(temp_arena, env);
        for (s32 id=0; id < param_count; id++)
        {
          Token *name = signature->param_names+id;
          Term *param_type = evaluateWithArgs(arena, env, param_count, env->stack->items, signature->param_types[id]);
          introduceOnStack(arena, env, name, param_type);
          addLocalBinding(env, name);
        }
        assert(noError());

        Term *expected_body_type = evaluateWithArgs(arena, env, param_count, env->stack->items, signature->output_type);
        if (BuildExpression body = buildExpression(arena, env, in->body, expected_body_type))
          fun->body = body.term;
        unwindBindingsAndStack(env);
        if (noError())
        {
          Function *funv = copyStruct(temp_arena, fun);
          funv->stack = env->stack;
          funv->type  = goal;
          assert(funv->stack);

          out0.term  = &fun->t;
          out0.value = &funv->t;
        }
      }
      else
      {
        parseError(in0, "lambda has to have an arrow type");
        attach("goal", goal);
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
        else if (BuildExpression build = buildExpression(arena, env, in->new_goal, holev))
          new_goal = build.value;

        if (noError())
        {
          if (equal(new_goal, goal))
          {// superfluous rewrite -> remove
            recursed = true;
            out0 = buildExpression(arena, env, in->body, goal);
          }
          else
          {
            // todo #cleanup normalization is not needed if skip goal is true
            Term *new_goal_norm = normalize(arena, env, new_goal);
            Term *goal_norm = normalize(arena, env, goal);
            if (skip_goal_comparison || equal(new_goal_norm, goal_norm))
            {
              Term *com = newComputation(arena, goal, new_goal);
              out->eq_proof = toAbstractTerm(arena, env, com);
            }
            else
            {
              parseError(in0, "new goal does not match original");
              equal(new_goal_norm, goal_norm);
              attach("new goal normalized", new_goal_norm);
              attach("current goal normalized", goal_norm);
            }
          }
        }
      }
      else if (in->new_goal)
      {// diff
        if (BuildExpression build_new_goal = buildExpression(arena, env, in->new_goal, holev))
        {
          new_goal = build_new_goal.value;
          CompareTerms compare = compareTerms(arena, goal, new_goal);
          if (compare.result.v == Trinary_True)
            parseError(in0, "new goal same as current goal");
          else
          {
            out->path = compare.diff_path;
            Value *from = subExpressionAtPath(goal, compare.diff_path);
            Value *to   = subExpressionAtPath(new_goal, compare.diff_path);
            Value *eq_proof = 0;

            if (Identifier *op_ident = castAst(in->eq_proof_hint, Identifier))
            {
              ValueArray op_overloads = getFunctionOverloads(env, op_ident, holev);
              for (int attempt=0; attempt < op_overloads.count; attempt++)
              {
                Value *hint = op_overloads.items[attempt];
                b32 hint_is_valid = false;
                if (Arrow *arrowv = castTerm(hint->type, Arrow))
                {
                  hint_is_valid = true;
                  Value *eq = newEquality(temp_arena, from, to);
                  Value **temp_args = pushArray(temp_arena, arrowv->param_count, Value *, true);
                  if (unify(temp_args, arrowv->param_types, arrowv->output_type, eq))
                  {
                    // todo #cleanup copyArray
                    Value **args = pushArray(arena, arrowv->param_count, Value *);
                    for (int id=0; id < arrowv->param_count; id++)
                      args[id] = temp_args[id];
                    eq_proof = newComposite(arena, env, hint, arrowv->param_count, args);
                    out->eq_proof = toAbstractTerm(arena, env, eq_proof);
                  }
                  else
                  {
                    parseError(in->eq_proof_hint, "unification failed");
                    attach("lhs", arrowv->output_type);
                    attach("rhs", eq);
                    attach("goal", goal);
                    attach("serial", serial);
                  }
                }
                else if (Composite *composite = castTerm(hint->type, Composite))
                {
                  if (composite->op == &builtins.equal->t)
                  {
                    hint_is_valid = true;
                    eq_proof = hint;
                  }
                }

                if (!hint_is_valid)
                {
                  parseError(in->eq_proof_hint, "invalid proof pattern");
                  attach("type", getType(hint));
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
            else if (BuildExpression build_eq_proof = buildExpression(arena, env, in->eq_proof_hint, holev))
            {
              eq_proof = build_eq_proof.value;
              if (getEqualitySides(eq_proof->type, false))
                out->eq_proof = toAbstractTerm(arena, env, eq_proof);
              else
              {
                parseError(in->eq_proof_hint, "invalid proof pattern");
                attach("type", eq_proof->type);
              }
            }

            if (noError())
            {
              auto [lhs,rhs] = getEqualitySides(eq_proof->type);
              Value *from, *to;
              if (in->right_to_left) {from = rhs; to = lhs; out->right_to_left = true;}
              else                   {from = lhs; to = rhs;}
              Value *actual_new_goal = rewriteTerm(arena, to, out->path, goal);
              if (!equal(new_goal, actual_new_goal))
              {
                parseError(in0, "invalid full-rewrite");
                attach("original goal", goal);
                attach("expected rewrite result", new_goal);
                attach("actual rewrite result", actual_new_goal);
                attach("rewrite from", from);
                attach("rewrite to", to);
              }
            }
          }
        }
      }
      else
      {// search
        if (BuildExpression eq_proof = buildExpression(arena, env, in->eq_proof_hint, holev))
        {
          out->eq_proof = eq_proof.term;
          Value *eq = eq_proof.value->type;
          if (auto [from, to] = getEqualitySides(eq, false))
          {
            if (in->right_to_left) {auto tmp = from; from = to; to = tmp; out->right_to_left = true;}
            SearchOutput search = searchExpression(arena, from, goal);
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
        if (BuildExpression body = buildExpression(arena, env, in->body, new_goal))
        {
          out->body = body.term;
          out0.term = &out->t;
          // assert(isFree(&out->t, 0));
        }
      }
    } break;

    case AC_Let:
    {
      Let  *let = castAst(in0, Let);
      Term *type_hint = holev;
      if (let->type && let->type != LET_TYPE_NORMALIZE)
      {
        if (BuildExpression type = buildExpression(arena, env, let->type, holev))
          type_hint = type.value;
      }
      if (noError())
      {
        if (BuildExpression rhs = buildExpression(arena, env, let->rhs, type_hint))
        {
          Term  *rhs_term  = rhs.term;
          Value *rhs_value = rhs.value;
          Value *rhs_type  = rhs.value->type;
          if (let->type == LET_TYPE_NORMALIZE)
          {// type coercion
            rhs_type = normalize(arena, env, rhs.value->type);
            Value *computation = newComputation(arena, rhs_type, rhs.value->type);
            rhs_value = newRewrite(arena, computation, rhs.value, 0, false);
            rhs_term  = toAbstractTerm(arena, env, rhs_value);
            assert(equal(rhs_value->type, rhs_type));
          }

          extendBindings(env);
          addLocalBinding(env, &let->lhs);
          extendStack(env, 1, 0);
          Value *previous_rhs_anchor = rhs_value->anchor;
          bindToStack(arena, env, &let->lhs, rhs_value);

          // todo #cleanup #typesafe
          if (BuildExpression body = buildExpression(arena, env, let->body, goal))
          {
            Function *fun = newTerm(arena, Function, 0);
            fun->body     = body.term;
            // evaluate cares about the signature, since atm it produces the type.
            // todo here we don't care about the type at all since we can just get the body type.
            Arrow *signature = newTerm(arena, Arrow, &builtins.Type->t);
            allocateArray(arena, 1, signature->param_names);
            allocateArray(arena, 1, signature->param_types);
            signature->param_count    = 1;
            signature->param_names[0] = let->lhs;
            signature->param_types[0] = toAbstractTerm(arena, env, rhs_type);
            signature->output_type    = toAbstractTerm(arena, env, goal);
            fun->type = &signature->t;

            Composite *com = newTerm(arena, Composite, 0);
            allocateArray(arena, 1, com->args);
            com->op        = &fun->t;
            com->arg_count = 1;
            com->args[0]   = rhs_term;

            out0.term = &com->t;
            should_check_type = false;
          }
          unwindBindingsAndStack(env);
          rhs_value->anchor = previous_rhs_anchor;
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
  {// one last typecheck if needed
    Term *actual   = getType(out0.value);
    Term *expected = goal;
    if (!matchType(env, actual, expected))
    {
      parseError(in0, "actual type differs from expected type");
      attach("got", actual);
      attach("expected", expected);
      attach("serial", serial);
    }
  }

  if (ParseError *error = getError())
  {
    error->code = ErrorWrongType;
    out0 = {};
  }
  else
    assert(out0);
  return out0;
}

inline BuildExpression
parseExpression(MemoryArena *arena, LocalBindings *bindings, Term *expected_type)
{
  BuildExpression out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Environment env = {};
    env.bindings = bindings;
    out = buildExpression(arena, &env, ast, expected_type);
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline BuildExpression
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
  Ast *out = 0;
  Token token = nextToken();
  if (equal(&token, '_'))
  {
    out = &newAst(arena, Hole, &token)->a;
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

    out = &newAst(arena, Identifier, tokenp)->a;
  }
  else if (equal(&token, '('))
  {
    out = parseExpressionToAst(arena);
    requireChar(')');
  }
  else
    tokenError("expected start of expression");

  if (hasMore())
  {
    Token funcall = peekToken();
    if (equal(&funcall, '('))
    {// function call syntax, let's keep going
      nextToken();
      Ast *op = out;

      Tokenizer tk_copy = *global_tokenizer;
      s32 expected_arg_count = getCommaSeparatedListLength(&tk_copy);
      if (noError(&tk_copy))
      {
        Ast **args = pushArray(arena, expected_arg_count, Ast*);
        CompositeAst *branch = newAst(arena, CompositeAst, &op->token);
        branch->op        = op;
        branch->arg_count = expected_arg_count;
        branch->args      = args;
        out = &branch->a;
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
  }
  NULL_WHEN_ERROR(out);
  return out;
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
        if (equal(op_token, "."))
        {// member accessor
          nextToken();
          AccessorAst *new_operand = newAst(arena, AccessorAst, &op_token);
          new_operand->record   = operand; // todo: I guess it works?
          Token member = nextToken();
          if (isIdentifier(&member))
          {
            new_operand->field_name = member;
            operand             = &new_operand->a;
          }
          else
            parseError(&member, "expected identifier as member accessor");
        }
        else if (isIdentifier(&op_token))
        {// infix operator syntax
          // (a+b) * c
          //        ^
          Identifier *op = newAst(arena, Identifier, &op_token);
          s32 precedence = precedenceOf(op_token);
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
        {
          tokenError(&op_token, "expected operator token, got");
          // todo push token attachment omg
        }
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
  initValue(&ctor->t, Term_Constructor, 0);
  ctor->uni  = uni;
  Token ctor_name = nextToken();
  ctor->id   = ctor_id;

  if (isIdentifier(&ctor_name))
  {
    if (optionalChar(':'))
    {// subtype
      Arrow *struct_;
      pushContext("struct {FIELD: TYPE ...}");
      if (requireCategory(TC_Keyword_struct))
      {
        ArrowAst *ast = parseArrowType(arena, true);
        Environment env_ = {}; Environment *env = &env_;
        // todo there are hacks we have to do to accept arrow type without
        // output type, which is dumb since the output type exists.
        if (BuildExpression build = buildExpression(arena, env, &ast->a, holev))
          struct_ = castTerm(build.value, Arrow);
      }
      popContext();

      if (noError())
      {
        struct_->output_type = uni->anchor;
        ctor->type = &struct_->t;
      }
    }
    else
    {// enum constructor
      if (uni->type == &builtins.Set->t) ctor->type = &uni->t;
      else parseError(&ctor_name, "constructors must construct a set member");
    }

    if (noError())
      addGlobalBinding(&ctor_name, &ctor->t);
  }
  else tokenError("expected an identifier as constructor name");
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
    if (BuildExpression type = parseExpressionFull(arena))
    {
      if (Arrow *arrow = castTerm(type.value, Arrow))
      {
        if (arrow->output_type == &builtins.Set->t)
          valid_type = true;
      }
      else if (type.value == &builtins.Set->t)
        valid_type = true;

      if (!valid_type)
      {
        parseError(&type_token, "form has invalid type");
        attach("type", type.value);
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
buildGlobalFunction(MemoryArena *arena, Environment *env, FunctionDecl *decl)
{
  Function *funv = 0;
  if (BuildExpression build_signature = buildExpression(arena, env, &decl->signature->a, holev))
  {
    // note: store the built signature, maybe to display it later.
    Arrow *signature = castTerm(build_signature.term, Arrow);
    funv = newTerm(arena, Function, build_signature.value);
    funv->body = &dummy_function_being_built;

    // note: add binding first to support recursion
    addGlobalBinding(&decl->a.token, &funv->t);

    if (noError())
    {
      extendStack(env, signature->param_count, 0);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < signature->param_count; id++)
      {
        Token *name = signature->param_names+id;
        Term *type = evaluate(arena, env, signature->param_types[id]);
        introduceOnStack(arena, env, name, type);
        addLocalBinding(env, name);
      }
      assert(noError());

      Term *expected_body_type = evaluate(temp_arena, env, signature->output_type);
      if (BuildExpression body = buildExpression(arena, env, decl->body, expected_body_type))
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
  Environment empty_env_ = {}; Environment *empty_env = &empty_env_;

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
          if (BuildExpression expr = parseExpressionFull(temp_arena))
            normalize(arena, empty_env, expr.value);
        } break;

        case TC_Keyword_print:
        {
          u32 flags = PrintFlag_Detailed|PrintFlag_PrintType;
          if (optionalString("lock_detailed"))
            setFlag(&flags, PrintFlag_LockDetailed);
          if (BuildExpression expr = parseExpressionFull(temp_arena))
          {
            Term *norm = normalize(arena, empty_env, expr.value);
            print(0, norm, {.flags=flags});
            print(0, "\n");
          }
        } break;

        case TC_Keyword_print_raw:
        {
          if (auto parsing = parseExpressionFull(temp_arena))
            print(0, parsing.value, {.flags = (PrintFlag_Detailed     |
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
              if (BuildExpression type = parseExpressionFull(temp_arena))
                expected_type = type.value;
            }
            if (noError())
              buildExpression(temp_arena, empty_env, ast, expected_type);
          }
        } break;

        case TC_Keyword_check_truth:
        {
          pushContext("check_truth EQUALITY");
          if (Term *goal = parseExpressionFull(temp_arena).value)
          {
            if (Composite *eq = castTerm(goal, Composite))
            {
              b32 goal_valid = false;
              if (eq->op == &builtins.equal->t)
              {
                goal_valid = true;
                Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
                Term *rhs = normalize(temp_arena, empty_env, eq->args[2]);
                if (!equal(lhs, rhs))
                {
                  parseError(&token, "equality cannot be proven by computation");
                  setErrorCode(ErrorWrongType);
                  Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
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
                if (BuildExpression rhs = parseExpressionFull(arena))
                {
                  addGlobalBinding(&token, rhs.value);
                  requireChar(';');
                }
                popContext();
              } break;

              case TC_DoubleColon:
              {
                Token after_dcolon = peekToken();
                if (equal(after_dcolon, "union"))
                {
                  nextToken();
                  parseUnion(arena, &token);
                }
                else
                {
                  b32 is_theorem;
                  if (equal(after_dcolon, "fn"))
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
                if (BuildExpression type = parseExpressionFull(arena))
                {
                  if (requireCategory(TC_ColonEqual, "require :=, syntax: name : type := value"))
                  {
                    if (BuildExpression rhs = parseExpression(arena, 0, type.value))
                      addGlobalBinding(&token, rhs.value);
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
    while (equal(token, ";"))
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

forward_declare inline BuildExpression
parseExpressionFromString(MemoryArena *arena, char *string)
{
  Tokenizer tk = newTokenizer(String{}, 0);
  Tokenizer *tk_save = global_tokenizer;
  global_tokenizer = &tk;
  tk.at = string;
  BuildExpression out = parseExpressionFull(arena);
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
      BuildExpression equal_type = parseExpressionFull(arena); 
      builtins.equal = newTerm(arena, Builtin, equal_type.value);
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

/*
  General Todos: 
  - #cleanup Replace all token <-> string comparison with keyword checks.
  - #tool defer
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include <corecrt.h>

global_variable i32 debug_normalization_depth;
global_variable i32 global_debug_serial;

global_variable Builtins builtins;
global_variable Sequence dummy_function_under_construction;
global_variable Term  holev_ = {.cat = Term_Hole};
global_variable Term *holev = &holev_;

global_variable FunctionId next_function_id;
inline FunctionId getNextFunctionId()
{
  next_function_id.id++;  // :reserved-0-for-function-id
  return FunctionId{next_function_id.id};
}

inline i32
getStackDepth(Environment *env)
{
  return (env->stack ? env->stack->depth : 0);
}

// todo #cleanup a lot of the copies are unnecessary, we must think about where
// we can put stack values. and whether to have stack values at all.
internal Ast *
deepCopy(MemoryArena *arena, Ast *in0)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_Hole:
    case AC_Identifier:
    {
      out0 = in0;
    } break;

#if 0
    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Fork *out = copyStruct(arena, in);
      out->subject = deepCopy(arena, in->subject);
      allocateArray(arena, in->case_count, out->bodies);
      for (s32 id=0; id < in->case_count; id++)
      {
        out->bodies[id] = deepCopy(arena, in->bodies[id]);
      }
      out0 = &out->a;
    } break;
#endif

    case AC_Sequence:
    {
      Sequence *in = castAst(in0, Sequence);
      Sequence *out = copyStruct(arena, in);
      allocateArray(arena, out->count, out->items);
      for (s32 id=0; id < in->count; id++)
      {
        out->items[id] = deepCopy(arena, in->items[id]);
      }
      out0 = &out->a;
    } break;

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

#if 0
    case AC_FunctionDecl:
    {
      FunctionDecl *in = castAst(in0, FunctionDecl);
      FunctionDecl *out = copyStruct(arena, in);
      out->signature = castAst(deepCopy(arena, &in->signature->a), Arrow);
      out->body      = deepCopy(arena, in->body);
      out0 = &out->a;
    } break;
#endif

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
      out->eq_proof = deepCopy(arena, in->eq_proof);
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
    case Term_StackValue:
    {
      StackValue *in  = castTerm(in0, StackValue);
      StackValue *out = copyStruct(arena, in);
      out0 = &out->v;
    } break;

    case Term_Composite:
    {
      Composite *in  = castTerm(in0, Composite);
      Composite *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, in->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
        out->args[id] = deepCopy(arena, in->args[id]);
      out0 = &out->v;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      out->output_type = deepCopy(arena, in->output_type);
      out0 = &out->v;
    } break;

    case Term_Accessor:
    {
      Accessor *in  = castTerm(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->v;
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
    out0->type = deepCopy(arena, out0->type);
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

inline void
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

inline void
dump(Term *in0)
{
  print(0, in0, {});
}

inline void dump(Ast *in0) {print(0, in0, {});}

inline void
print(MemoryArena *buffer, Stack *stack)
{
  print(buffer, "[");
  while (stack)
  {
    print(buffer, "[");
    for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
    {
      print(buffer, stack->items[arg_id], PrintOptions{.print_type=true});
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
inline void
debugIndent()
{
  debug_indentation++;
  for (s32 id = 0; id < debug_indentation; id++)
    dump(" ");
}

inline void
debugDedent()
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
precedenceOf(Token *op)
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

inline Token *
getFunctionName(Function *fun)
{
  if (fun->name.string.chars) return &fun->name;
  else                        return 0;
}

// prints both Composite and CompositeV
inline void
printComposite(MemoryArena *buffer, void *in0, b32 is_value, PrintOptions opt)
{
  int    precedence = 0;  // todo: no idea what the default should be
  void  *op;
  s32    arg_count;
  void **raw_args;

  Ast   *ast   = (Ast *)in0;
  Term *value = (Term *)in0;
  Arrow *op_type = 0;
  if (is_value)
  {
    Composite *in = castTerm(value, Composite);
    op       = in->op;
    raw_args = (void **)in->args;
    op_type  = castTerm(in->op->type, Arrow);
    assert(op_type);

    if (Function *op_fun = castTerm(in->op, Function))
    {
      if (Token *name = getFunctionName(op_fun))
        precedence = precedenceOf(name);
    }
  }
  else
  {
    CompositeAst *in = castAst(ast, CompositeAst);
    op       = in->op;
    raw_args = (void **)in->args;
    if (Constant *op = castAst(in->op, Constant))
    {
      op_type = castTerm(op->value->type, Arrow);
      assert(op_type);
    }
    else arg_count = in->arg_count;

    precedence = precedenceOf(&in->op->token);
  }

  void **args;
  if (op_type)
  {// print out unignored args only
    args = pushArray(temp_arena, op_type->param_count, void*);
    arg_count = 0;
    for (s32 param_id = 0; param_id < op_type->param_count; param_id++)
    {
      if (!isHiddenParameter(op_type, param_id))
        args[arg_count++] = raw_args[param_id];
    }
  }
  else args = raw_args;

  if (arg_count == 2)
  {// special path for infix operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    arg_opt.no_paren_precedence = precedence+1;
    print(buffer, args[0], is_value, arg_opt);

    print(buffer, " ");
    print(buffer, op, is_value, opt);
    print(buffer, " ");

    arg_opt.no_paren_precedence = precedence;
    print(buffer, args[1], is_value, arg_opt);
    if (precedence < opt.no_paren_precedence)
      print(buffer, ")");
  }
  else
  {// normal prefix path
    print(buffer, op, is_value, opt);
    print(buffer, "(");
    PrintOptions arg_opt        = opt;
    arg_opt.no_paren_precedence = 0;
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {
      print(buffer, args[arg_id], is_value, arg_opt);
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
    new_opt.detailed    = false;
    new_opt.indentation = opt.indentation+1;

    switch (in0->cat)
    {
      case AC_Null:
      {
        print(buffer, "<NULL>");
      } break;

      case AC_Hole:
      {
        print(buffer, "_");
      } break;

      case AC_Identifier:
      {
        print(buffer, in0->token);
      } break;

      case AC_Constant:
      {
        Constant *in = castAst(in0, Constant);
        if (in->is_synthetic)
          print(buffer, in->value, opt);
        else
        {
          // print(buffer, "<c>");
          print(buffer, in->a.token);
        }
      } break;

      case AC_Variable:
      {
        Variable *in = castAst(in0, Variable);
        // print(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
        print(buffer, in->token);
      } break;

      case AC_Sequence:
      {
        Sequence *in = castAst(in0, Sequence);
        for (s32 id = 0; id < in->count; id++)
        {
          print(buffer, in->items[id], new_opt);
          if (id < in->count-1)
            print(buffer, "; ");
        }
      } break;

      case AC_RewriteAst:
      {
        RewriteAst *in = castAst(in0, RewriteAst);
        print(buffer, "rewrite");
        print(buffer, in->path);
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof, new_opt);
      } break;

      case AC_CompositeAst:
      {
        printComposite(buffer, in0, false, new_opt);
      } break;

      case AC_Fork:
      {
        Fork *in = castAst(in0, Fork);
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
          print(buffer, &ctor->v, new_opt);
          print(buffer, ": ");
          print(buffer, &in->bodies[ctor_id]->a, new_opt);
          if (ctor_id != form->ctor_count-1)
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
        print(buffer, "let");
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
{// mark: printValue
  i32 debug_print = true;
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed   = false;
    new_opt.print_type = false;
    new_opt.indentation = opt.indentation + 1;

    switch (in0->cat)
    {
      case Term_StackPointer:
      {
        StackPointer *in = castTerm(in0, StackPointer);
        print(buffer, in->name);
        if (debug_print) print(buffer, "[%d]", in->stack_delta);
      } break;

      case Term_Hole:
      {
        print(buffer, "_");
      } break;

      case Term_StackValue:
      {
        StackValue *in = castTerm(in0, StackValue);
        print(buffer, in->name);
        if (debug_print) print(buffer, "<%d>", in->stack_depth);
      } break;

      case Term_Composite:
      {
        printComposite(buffer, in0, true, new_opt);
      } break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        if (opt.detailed)
        {
          print(buffer, in->name);

          if (in->ctor_count)
          {
            print(buffer, " {");
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Constructor *subset = in->ctors + ctor_id;
              print(buffer, subset->name);
              print(buffer, ": ");
              print(buffer, subset->type, new_opt);
            }
            print(buffer, " }");
          }
        }
        else
          print(buffer, in->name);
      } break;

      case Term_Function:
      {
        Function *in = castTerm(in0, Function);
        if (Token *name = getFunctionName(in))
        {
          print(buffer, name->string);
        }
        if (opt.detailed)
        {
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          print(buffer, &in->body->a, new_opt);
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
        if (in0 == builtins.equal)
          print(buffer, "=");
        else if (in0 == builtins.Set)
          print(buffer, "Set");
        else if (in0 == builtins.Type)
          print(buffer, "Type");
      } break;

      case Term_Constructor:
      {
        Constructor *in = castTerm(in0, Constructor);
        print(buffer, in->name);
      } break;

      case Term_Rewrite:
      {
        Rewrite *rewrite = castTerm(in0, Rewrite);
        print(buffer, rewrite->type, new_opt);
        print(buffer, " <=>");
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, rewrite->body->type, new_opt);
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "rewrite");
        if (rewrite->right_to_left) print(buffer, "<-");
        print(buffer, rewrite->path);
        print(buffer, " justification: ");
        newlineAndIndent(buffer, new_opt.indentation);
        print(buffer, rewrite->eq_proof, new_opt);
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "body: ");
        print(buffer, rewrite->body->type, new_opt);
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
        print(buffer, "(");
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name);
      } break;
    }

    if (opt.print_type)
    {
      print(buffer, ": ");
      print(buffer, in0->type, new_opt);
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
print(MemoryArena *buffer, void *in0, b32 is_value, PrintOptions opt)
{
  if (is_value)
    return print(buffer, (Term*)in0, opt);
  else
    return print(buffer, (Ast*)in0, opt);
}

inline void
addStackFrame(Environment *env)
{
  Stack *stack = pushStruct(temp_arena, Stack);
  stack->depth = getStackDepth(env) + 1;
  stack->outer = env->stack;
  stack->count = 0;
  env->stack = stack;
}

inline void
addStackValue(Environment *env, Term *value)
{
  env->stack->items[env->stack->count++] = value;
}

inline void
extendStack(Environment *env, s32 count, Term **args)
{
  assert(count <= arrayCount(env->stack->items));
  addStackFrame(env);
  for (s32 arg_id = 0; arg_id < count; arg_id++)
  {// todo: #speed copying values around
    addStackValue(env, args[arg_id]);
  }
}

inline b32
equal(Term *lhs, Term *rhs)
{
  return equalTrinary(lhs, rhs).v == Trinary_True;
}

inline b32 equal(Ast *lhs, Ast *rhs)
{
  if (lhs == rhs)
    return true;
  if (lhs->cat == rhs->cat)
  {
    switch (lhs->cat)
    {
      case AC_Variable:
      {
        auto l = castAst(lhs, Variable);
        auto r = castAst(rhs, Variable);
        return (l->id == r->id && l->stack_delta == r->stack_delta);
      } break;

      case AC_CompositeAst:
      {
        auto l = castAst(lhs, CompositeAst);
        auto r = castAst(rhs, CompositeAst);
        if (l->op == r->op)
        {
          if (l->arg_count == r->arg_count)
          {
            for (int id=0; id < l->arg_count; id++)
            {
              if (l->args[id] != r->args[id])
                return false;
            }
            return true;
          }
        }
      } break;

      case AC_Constant:
      {
        auto l = castAst(lhs, Constant);
        auto r = castAst(rhs, Constant);
        return equal(l->value, r->value);
      } break;

      default:
      {
        // todo #incomplete
      } break;
    }
  }
  return false;
}

inline b32
isCompositeConstructor(Term *in0)
{
  if (Composite *in = castTerm(in0, Composite))
    return in->op->cat == Term_Constructor;
  else
    return false;
}

internal Term *
evaluateArrow(MemoryArena *arena, Term **args, Term *in0, i32 stack_offset)
{
  Term *out0 = 0;
  switch (in0->cat)
  {
    case Term_StackPointer:
    {
      StackPointer *in = castTerm(in0, StackPointer);
      assert(in->stack_delta >= 0 && in->id >= 0);
      if (in->stack_delta == stack_offset)
        out0 = args[in->id];
      else out0 = in0;
    } break;

    case Term_Composite:
    {
      Composite *in  = castTerm(in0, Composite);
      assert(in->type);
      Composite *out = copyStruct(arena, in);
      out->op = evaluateArrow(arena, args, in->op, stack_offset);
      allocateArray(arena, in->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
        out->args[id] = evaluateArrow(arena, args, in->args[id], stack_offset);
      out0 = &out->v;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, out->param_count, out->param_types);
      for (int id=0; id < out->param_count; id++)
      {
        out->param_types[id] = evaluateArrow(arena, args, out->param_types[id], stack_offset);
      }
      out->output_type = evaluateArrow(arena, args, out->output_type, stack_offset);
      out0 = &out->v;
    } break;

    case Term_Accessor:
    {
      Accessor *in  = castTerm(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = evaluateArrow(arena, args, in->record, stack_offset);
      out0 = &out->v;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Function:
    case Term_StackValue:
    case Term_Hole:
    {out0=in0;} break;

    case Term_Computation:
    case Term_Rewrite:
    {todoIncomplete;} break;
  }
  assert(out0);
  return out0;
}

forward_declare internal CompareExpressions
compareExpressions(MemoryArena *arena, Term *lhs0, Term *rhs0)
{
  CompareExpressions out = {};
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
      case Term_StackPointer:
      {
        StackPointer *lhs = castTerm(lhs0, StackPointer);
        StackPointer *rhs = castTerm(rhs0, StackPointer);
        if ((lhs->stack_delta == rhs->stack_delta) && (lhs->id == rhs->id))
          out.result.v = Trinary_True;
      } break;

      case Term_StackValue:
      {
        StackValue* lhs = castTerm(lhs0, StackValue);
        StackValue* rhs = castTerm(rhs0, StackValue);
        if ((lhs->stack_depth == rhs->stack_depth) && (lhs->id == rhs->id))
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
          Arrow *op_type = castTerm(lhs->op->type, Arrow);
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
              CompareExpressions recurse = compareExpressions(arena, lhs->args[id], rhs->args[id]);
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
        out.result = compareExpressions(arena, lhs->record, rhs->record).result;
      } break;

      case Term_Builtin:
      {
        out.result.v = Trinary_True;
      } break;

      case Term_Function:
      {
        Function *lhs = castTerm(lhs0, Function);
        Function *rhs = castTerm(rhs0, Function);
        if (lhs->id.id == rhs->id.id)
          out.result.v = Trinary_True;
      } break;

      case Term_Hole:
      case Term_Union:
      case Term_Rewrite:
      case Term_Computation:
      {
        out.result.v = Trinary_Unknown;
      } break;
    }
  }
  else if (((lhs0->cat == Term_Constructor) && isCompositeConstructor(rhs0)) ||
           ((rhs0->cat == Term_Constructor) && isCompositeConstructor(lhs0)))
  {
    out.result.v = Trinary_False;
  }

  if (debug && global_debug_mode)
  {
    debugDedent(); dump("=> "); dump(out.result);
    dump();
  }

  return out;
}

forward_declare internal Trinary
equalTrinary(Term *lhs0, Term *rhs0)
{
  return compareExpressions(0, lhs0, rhs0).result;
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
          slot->next_hash_slot = pushStruct(permanent_arena, GlobalBinding, true);
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

internal Term *
repeatedOverwrite(Environment *env, Term *in)
{
  Term *out = 0;
  // todo: find some way to early out in case expression can't be rewritten
  // if (canBeRewritten(in))
  // todo: #speed this is O(n)
  for (OverwriteRules *rewrite = env->overwrite;
       rewrite && !out;
       rewrite = rewrite->next)
  {
    if (equal(in, rewrite->lhs))
      out = rewrite->rhs;
  }
  if (!out)
    out = in;

  return out;
}

forward_declare internal Term *
evaluateFork(MemoryArena *arena, Environment *env, Fork *fork)
{
  Term *out;
  Term *subject = evaluateAndNormalize(arena, env, fork->subject);
  addStackFrame(env);
  switch (subject->cat)
  {// note: we fail if the fork is undetermined
    case Term_Constructor:
    {
      Constructor *ctor = castTerm(subject, Constructor);
      out = evaluateSequence(arena, env, fork->bodies[ctor->id]);
    } break;

    case Term_Composite:
    {
      Composite *record = castTerm(subject, Composite);
      if (Constructor *ctor = castTerm(record->op, Constructor))
        out = evaluateSequence(arena, env, fork->bodies[ctor->id]);
      else
        out = 0;
    } break;

    default:
      out = 0;
  }
  unwindStack(env);

  return out;
}

struct ValuePair {Term *lhs; Term *rhs;};

inline ValuePair getEqualitySides(Term *eq0)
{
  Composite *eq = castTerm(eq0, Composite);
  assert(eq->op == builtins.equal);
  return ValuePair{eq->args[1], eq->args[2]};
}

internal Term *
rewriteExpression(MemoryArena *arena, Term *rhs, TreePath *path, Term *in0)
{
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyStruct(arena, in);
    if (path->first == -1)
    {
      out->op = rewriteExpression(arena, rhs, path->next, in->op);
    }
    else
    {
      assert(path->first >= 0 && path->first < out->arg_count);
      allocateArray(arena, out->arg_count, out->args);
      for (i32 arg_id=0; arg_id < out->arg_count; arg_id++)
      {
        if (arg_id == (i32)path->first)
        {
          out->args[arg_id] = rewriteExpression(arena, rhs, path->next, in->args[arg_id]);
        }
        else
          out->args[arg_id] = in->args[arg_id];
      }
    }
    return &out->v;
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

struct RewriteChain {
  Rewrite     *first;
  RewriteChain *next;
};

forward_declare internal Term *
evaluateSequence(MemoryArena *arena, Environment *env, Sequence *sequence)
{
  // todo not sure what the normalization should be, but we're probably only
  // called from "normalize", so I guess it's ok to always normalize.
  Environment env_ = *env; env = &env_;
  RewriteChain *rewrite_chain = 0;
  for (s32 id = 0;  id < sequence->count-1;  id++)
  {
    Ast *item = sequence->items[id];
    switch (item->cat)
    {
      case AC_RewriteAst:
      {
        RewriteAst  *rewrite  = castAst(item, RewriteAst);
        Rewrite *rewritev = newTerm(arena, Rewrite, 0);
        Term *eq_proof = evaluateAndNormalize(arena, env, rewrite->eq_proof);
        rewritev->eq_proof      = eq_proof;
        rewritev->right_to_left = rewrite->right_to_left;
        rewritev->path          = rewrite->path;
        if (rewrite_chain)
        {
          Rewrite *outer_rewrite = rewrite_chain->first;
          outer_rewrite->body = &rewritev->v;
        }

        RewriteChain *new_rewrite_chain = pushStruct(temp_arena, RewriteChain);
        new_rewrite_chain->first = rewritev;
        new_rewrite_chain->next  = rewrite_chain;
        rewrite_chain            = new_rewrite_chain;
      } break;

      case AC_Let:
      {
        Let   *let = castAst(item, Let);
        Term *rhs = evaluateAndNormalize(arena, env, let->rhs);
        addStackValue(env, rhs);
      } break;

      invalidDefaultCase;
    }
  }

  if (global_debug_mode)
    breakhere;
  Term *last = 0;
  Ast *last_ast = sequence->items[sequence->count-1];
  if (Fork *fork = castAst(last_ast, Fork))
    last = evaluateFork(arena, env, fork);
  else
    last = evaluateAndNormalize(arena, env, last_ast);

  Term *out = 0;
  if (last)
  {
    if (rewrite_chain)
    {
      Rewrite *last_rewrite = rewrite_chain->first;
      last_rewrite->body = last;

      RewriteChain *chain = rewrite_chain;
      Term *debug_previous_type = 0;
      while (true)
      {
        Rewrite *rewrite = chain->first;
        auto [lhs, rhs] = getEqualitySides(rewrite->eq_proof->type);
        Term *rewrite_to   = rewrite->right_to_left ? rhs : lhs;
        if (debug_previous_type)
        {
          assert(equal(debug_previous_type, rewrite->body->type));
        }
#if 0
        if (global_debug_mode)
        {
          dump();
          if (rewrite->right_to_left) dump("<-");
          else                        dump("->");
          dump("body:          "); dump(rewrite->body)          ; dump();
          dump("body_type:     "); dump(rewrite->body->type)    ; dump();
          dump("rewrite->path: "); dump(rewrite->path)          ; dump();
          dump("equality:      "); dump(rewrite->eq_proof->type); dump();
          dump("eq_proof:      "); dump(rewrite->eq_proof)      ; dump();
        }
#endif
        Term *type = rewriteExpression(arena, rewrite_to, rewrite->path, rewrite->body->type);

        rewrite->type = type;
        debug_previous_type = rewrite->type;

        if (chain->next) chain=chain->next;
        else             break;
      }
      out = &chain->first->v;
    }
    else
      out = last;
  }

  return out;
}

forward_declare internal Term *
normalize(MemoryArena *arena, Environment *env, Term *in0) 
{
  debug_normalization_depth++;
  // NOTE: I'm kinda convinced that this is only gonna be a best-effort
  // thing. Handling all cases is a waste of time.
  Term *out0 = {};

  b32 debug = false;
  if (debug && global_debug_mode)
  {
    debugIndent(); dump("normalize: "); dump(in0); dump();
  }

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
      // todo: what about function stack dawg?
      if (norm_op->cat == Term_Function)
      {// Function application
        Function *funv = castTerm(norm_op, Function);
        if (funv->body != &dummy_function_under_construction)
        {
          extendStack(env, in->arg_count, norm_args);
          // note: evaluation might fail, in which case we back out.
          out0 = evaluateSequence(arena, env, funv->body);
          if (out0)
            out0 = normalize(arena, env, out0);
          unwindStack(env);
        }
      }
      else
      {
        assert((norm_op == builtins.equal) || (norm_op->cat == Term_Constructor) || (norm_op->cat == Term_StackValue));
#if 1  // special casing for equality
        if (norm_op == builtins.equal)
        {// special case for equality
          Term *lhs = norm_args[1];
          Term *rhs = norm_args[2];
          Trinary compare = equalTrinary(lhs, rhs);
#if 0
          if (compare == Trinary_True)
            out0 = &builtins.True->v;
#endif
          // I don't know how to handle inconsistency otherwise
          if (compare.v == Trinary_False)
            out0 = &builtins.False->v;
        }
#endif
      }

      if (!out0)
      {
        Composite *out = newTerm(arena, Composite, in->type);
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->v;
      }
      assert(out0->cat);
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, out->param_count, out->param_types);
      for (i32 id=0; id < out->param_count; id++)
        out->param_types[id] = normalize(arena, env, in->param_types[id]);
      out->output_type = normalize(arena, env, out->output_type);
      out0 = &out->v;
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
        out0 = &out->v;
      }
      else out0 = in0;
    } break;

    // todo #speed most of these don't need rewriting.
    case Term_StackPointer:
    case Term_Hole:
    case Term_Constructor:
    case Term_Builtin:
    case Term_Function:
    case Term_StackValue:
    case Term_Union:
    case Term_Computation:
    case Term_Accessor:
    {out0 = in0;} break;
  }

  Term *before_rewrite = out0;
  out0 = repeatedOverwrite(env, out0);

  if (out0 != before_rewrite)
  {
    if (debug_normalization_depth > 50)
    {
      dump("before_rewrite: "); dump(before_rewrite); dump();
      dump("after rewrite"); dump(out0); dump();
      dump("rewrite rules"); dump(env->overwrite); dump();
    }

    // normalize again, because there might be new information not present at
    // the time the rewrite rule was added (f.ex the op might be expanded now)
    out0 = normalize(arena, env, out0);
  }

  if (debug && global_debug_mode)
  {
    debugDedent(); dump("=> "); dump(out0); dump();
  }

  assert(out0);
  debug_normalization_depth--;
  return out0;
}

inline Ast *
replaceFreeVars(MemoryArena* arena, Environment *env, Ast *in0, s32 stack_offset)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      s32 stack_delta = in->stack_delta - stack_offset;
      if (stack_delta >= 0)
      {
        Stack *stack = env->stack;
        for (s32 delta = 0; delta < stack_delta ; delta++)
          stack = stack->outer;
        if (in->id >= stack->count)
        {
          dump(env->stack);
          invalidCodePath;
        }
        Term *norm_stack_value = normalize(arena, env, stack->items[in->id]);
        Constant *out = newSyntheticConstant(arena, norm_stack_value);
        out0 = &out->a;
      }
      else
        out0 = in0;
    } break;

    case AC_Constant:
    {
      out0 = in0;
    } break;

    case AC_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);
      CompositeAst *out = copyStruct(arena, in);
      out->op   = replaceFreeVars(arena, env, in->op, stack_offset);
      out->args = pushArray(arena, in->arg_count, Ast*);
      for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        out->args[arg_id] = replaceFreeVars(arena, env, in->args[arg_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      ArrowAst *out = copyStruct(arena, in);
      stack_offset++;
      out->output_type    = replaceFreeVars(arena, env, in->output_type, stack_offset);
      out->param_types = pushArray(arena, in->param_count, Ast*);
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        out->param_types[param_id] = replaceFreeVars(arena, env, in->param_types[param_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      AccessorAst *out = copyStruct(arena, in);
      out->record = replaceFreeVars(arena, env, in->record, stack_offset);
      out0 = &out->a;
    } break;

    case AC_RewriteAst:
    case AC_Let:
    case AC_FunctionDecl:
    case AC_Sequence:
    case AC_Fork:
    {
      todoIncomplete;
    } break;

    invalidDefaultCase;
  }
  assert(out0);
  return out0;
}

inline b32
isGlobalValue(Term *value)
{
  switch (value->cat)
  {
    case Term_Hole:
    case Term_StackPointer:
    case Term_StackValue:
    {
      return false;
    } break;

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
    {return true;} break;

    case Term_Accessor:
    case Term_Rewrite:
    case Term_Computation:
    {
      invalidCodePath;
      return false;
    } break;
  }
}

inline b32
isGlobalFunction(Term *in0)
{
  return (in0->cat == Term_Function && castTerm(in0, Function)->id.id);
}

internal Term *
toAbstractTerm(MemoryArena *arena, Term *in0, i32 zero_depth)
{// todo #mem #copy-festival: If this stays longer than 3 days, then we
 // gotta clean it up.
  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (debug)
  {
    debugIndent(); dump("toAbstractTerm("); dump(serial); dump("): "); dump(in0); dump();
  }
  Term *out0 = 0;
  if (in0->cat == Term_Builtin      ||
      in0->cat == Term_Union        ||
      in0->cat == Term_Constructor  ||
      in0->cat == Term_StackPointer ||
      isGlobalFunction(in0))
  {
    out0 = in0;
  }
  else
  {
    Term *type = toAbstractTerm(arena, in0->type, zero_depth);
    switch (in0->cat)
    {
      case Term_StackValue:
      {
        StackValue *in = castTerm(in0, StackValue);
        if (in->stack_depth >= zero_depth)
        {
          StackPointer *out = newTerm(arena, StackPointer, type);
          out->name        = in->name;
          out->id          = in->id;
          out->stack_delta = in->stack_depth - zero_depth;
          out0 = &out->v;
        }
        else out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        out->type      = type;
        out->op        = toAbstractTerm(arena, in->op, zero_depth);
        allocateArray(arena, out->arg_count, out->args);
        for (i32 id=0; id < out->arg_count; id++)
          out->args[id] = toAbstractTerm(arena, in->args[id], zero_depth);
        out0 = &out->v;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        allocateArray(arena, out->param_count, out->param_types);
        for (i32 id=0; id < out->param_count; id++)
          out->param_types[id] = toAbstractTerm(arena, in->param_types[id], zero_depth+1);
        if (out->output_type)
          out->output_type = toAbstractTerm(arena, in->output_type, zero_depth+1);
        out0 = &out->v;
      } break;

      case Term_Function:
      {
        if (type == in0->type) out0 = in0;
        else
        {
          Function *in  = castTerm(in0, Function);
          Function *out = copyStruct(arena, in);
          out->type = type;
          out0 = &out->v;
        }
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = newTerm(arena, Computation, type);
        out->lhs  = toAbstractTerm(arena, in->lhs, zero_depth);
        out->rhs  = toAbstractTerm(arena, in->rhs, zero_depth);
        out->type = type;
        out0 = &out->v;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyStruct(arena, in);
        out->type   = type;
        out->record = toAbstractTerm(arena, in->record, zero_depth);
        out0 = &out->v;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in   = castTerm(in0, Rewrite);
        Rewrite *out  = copyStruct(arena, in);
        out->eq_proof = toAbstractTerm(arena, in->eq_proof, zero_depth);
        out->body     = toAbstractTerm(arena, in->body, zero_depth);
        out0 = &out->v;
      } break;

      case Term_Union:
      case Term_Constructor:
      case Term_Builtin:
      case Term_Hole:
      case Term_StackPointer:
        invalidCodePath;
    }
  }
  assert(out0);
  if (debug)
  {
    debugDedent(); dump("=>("); dump(serial); dump(") "); dump(out0); dump();
  }
  return out0;
}

forward_declare internal Term *
evaluate(MemoryArena *arena, Environment *env, Ast *in0)
{
  Term *out0 = 0;

#define DEBUG_EVALUATE 0
#define DEBUG_EVALUATE_DEPTH 2

#if DEBUG_EVALUATE
  if (global_debug_mode)
  {
    debug_evaluation_depth++;
    if (debug_evaluation_depth < DEBUG_EVALUATE_DEPTH)
    {
      debugIndent(); dump("evaluate: "); dump(in0); dump();
    }
  }
#endif

  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      assert(in->stack_delta >= 0 && in->id >= 0);
      Stack *stack = env->stack;
      for (s32 delta = 0; delta < in->stack_delta; delta++)
        stack = stack->outer;

      if (in->id < stack->count)
        out0 = stack->items[in->id];
      else
      {
        dump(env->stack); dump();
        invalidCodePath;
      }
    } break;

    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = in->value;
    } break;

    case AC_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);

      Term **args = pushArray(arena, in->arg_count, Term*);
      for (int arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        Term *arg = evaluate(arena, env, in_arg);
        args[arg_id] = arg;
      }

      Term *op = evaluate(arena, env, in->op);
      Arrow *signature = castTerm(op->type, Arrow);
      Term *return_type = evaluateArrow(arena, args, signature->output_type, 0);
      Composite *out = newTerm(arena, Composite, return_type);
      out->arg_count = in->arg_count;
      out->op        = op;
      out->args      = args;
      out0 = &out->v;
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in  = castAst(in0, ArrowAst);
      Arrow    *out = newTerm(arena, Arrow, builtins.Type);
      out->param_count = in->param_count;
      out->param_names = in->param_names;

      addStackFrame(env);
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
      {
        out->param_types[id] = evaluate(arena, env, in->param_types[id]);
        introduceOnStack(arena, env, in->param_names+id, out->param_types[id]);
      }
      if (in->output_type)
        out->output_type = evaluate(arena, env, in->output_type);
      unwindStack(env);

      out0 = toAbstractTerm(arena, &out->v, getStackDepth(env));
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      Term *record0 = evaluate(arena, env, in->record);
      // note: it has to be a record, otw we wouldn't know what type to
      // return.
      Composite *record = castTerm(record0, Composite);
      out0 = record->args[in->field_id];
    } break;

    case AC_ComputationAst:
    {
      ComputationAst  *computation = castAst(in0, ComputationAst);
      Term *lhs = evaluate(arena, env, computation->lhs);
      Term *rhs = evaluate(arena, env, computation->rhs);

      // TODO: the "tactics" code proliferates too much
      Composite *eq = newTerm(arena, Composite, builtins.Set);
      eq->op        = builtins.equal;
      eq->arg_count = 3;
      allocateArray(arena, eq->arg_count, eq->args);
      eq->args[0] = lhs->type;
      eq->args[1] = lhs;
      eq->args[2] = rhs;

      Computation *out = newTerm(arena, Computation, &eq->v);
      out->lhs = lhs;
      out->rhs = rhs;
      out0 = &out->v;
    } break;

    case AC_Lambda:
    {
      Lambda *in = castAst(in0, Lambda);
      Term *type = evaluate(arena, env, &in->signature->a);
      Function *out = newTerm(arena, Function, type);
      out->body  = in->body;
      out->stack_depth = getStackDepth(env);
      out0 = &out->v;
    } break;

    invalidDefaultCase;
  }

  // note: overwriting doesn't count as normalization
  out0 = repeatedOverwrite(env, out0);

  assert(out0);

#if DEBUG_EVALUATE
  if (global_debug_mode)
  {
    if (debug_evaluation_depth < DEBUG_EVALUATE_DEPTH)
    {
      debugDedent(); dump("=> "); dump(out0); dump(": "); dump(out0->type); dump();
    }
    debug_evaluation_depth--;
  }
#endif

  return out0;
}

forward_declare internal Term *
evaluateAndNormalize(MemoryArena *arena, Environment *env, Ast *in0)
{
  Term *eval = evaluate(arena, env, in0);
  Term *norm = normalize(arena, env, eval);
  return norm;
}

internal Term *
evaluate(MemoryArena *arena, Ast *in0)
{
  Environment env = {};
  return evaluate(arena, &env, in0);
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

inline Term *
introduceRecord(MemoryArena *arena, Environment *env, Term *parent, Constructor *ctor)
{
  Term *out = 0;
  if (Arrow *ctor_sig = castTerm(ctor->type, Arrow))
  {
    s32 param_count = ctor_sig->param_count;
    Term *record_type = ctor_sig->output_type;
    Composite *record = newTerm(arena, Composite, record_type);
    record->op        = &ctor->v;
    record->arg_count = param_count;
    record->args      = pushArray(arena, param_count, Term*);
    for (s32 field_id=0; field_id < param_count; field_id++)
    {
      String field_name = ctor_sig->param_names[field_id].string;
      Term *member_type = evaluateArrow(arena, record->args, ctor_sig->param_types[field_id], 0);
      Accessor *accessor = newTerm(arena, Accessor, member_type);
      accessor->record     = parent;
      accessor->field_id   = field_id;
      accessor->field_name = field_name;
      if (Constructor *field_ctor = getSoleConstructor(member_type))
      {// recursive case
        Term *intro = introduceRecord(arena, env, &accessor->v, field_ctor);
        record->args[field_id] = intro;
      }
      else  // base case
        record->args[field_id] = &accessor->v;
    }
    out = &record->v;
  }
  else
  {
    assert(ctor->type->cat == Term_Union);
    out = &ctor->v;
  }
  return out;
}

forward_declare inline void
introduceOnStack(MemoryArena* arena, Environment *env, Token *name, Term *typev)
{
  Term *intro;

  StackValue *ref = newTerm(arena, StackValue, typev);
  ref->name        = *name;
  ref->id          = env->stack->count;  // :stack-ref-id-has-significance
  ref->stack_depth = env->stack->depth;

  if (Constructor *type_ctor = getSoleConstructor(typev))
    intro = introduceRecord(arena, env, &ref->v, type_ctor);
  else
    intro = &ref->v;

  addStackValue(env, intro);
}

forward_declare inline void
introduceOnStack(MemoryArena* arena, Environment *env, Token *name, Ast *type)
{
  Term *typev = evaluate(arena, env, type);
  introduceOnStack(arena, env, name, typev);
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
addGlobalBinding(Token *token, Term *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(token->string, true);
  // TODO: check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));
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
addRewriteRule(Environment *env, Term *lhs0, Term *rhs0)
{
  b32 added = false;
  if (!equal(lhs0, rhs0))
  {
    OverwriteRules *rewrite = newOverwriteRule(env, lhs0, rhs0);
    env->overwrite = rewrite;
    added= true;

#if 0
    print(0, "added rewrite: ");
    print(0, lhs, {});
    print(0, " -> ");
    print(0, rhs, {});
    printNewline();
#endif
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
  // todo: I feel like I can remove normalization
  if (expected == holev) return true;
  else
  {
    Term *norm_actual   = normalize(temp_arena, env, actual);
    Term *norm_expected = normalize(temp_arena, env, expected);
    if (equal(norm_actual, norm_expected)) return true;
  }
  return false;
}

inline b32
hasFreeVars(Term *in0, i32 stack_offset)
{
  switch (in0->cat)
  {
    case Term_StackPointer:
    {
      StackPointer *in = castTerm(in0, StackPointer);
      if (in->stack_delta >= stack_offset)
        return true;
    } break;

    case Term_Composite:
    {
      Composite *in = castTerm(in0, Composite);
      if (hasFreeVars(in->op, stack_offset))
        return true;
      for (s32 arg_id=0; arg_id < in->arg_count; arg_id++)
      {
        if (hasFreeVars(in->args[arg_id], stack_offset))
          return true;
      }
    } break;

    case Term_Arrow:
    {// todo: I suspect this recursion is done completely wrong.
      Arrow *in = castTerm(in0, Arrow);
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        if (hasFreeVars(in->param_types[param_id], stack_offset+1))
          return true;
      }
      if (hasFreeVars(in->output_type, stack_offset+1))
        return true;
    } break;

    case Term_Accessor:
    {
      Accessor *in = castTerm(in0, Accessor);
      return hasFreeVars(in->record, stack_offset);
    } break;

    case Term_StackValue:
    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    {return false;}

    case Term_Hole:
    case Term_Computation:
    case Term_Rewrite:
    case Term_Function:
    {todoIncomplete;}
  }
  return false;
}

inline ValueArray
getGlobalOverloads(Environment *env, Identifier *ident, Term *expected_type)
{
  ValueArray out = {};
  if (!lookupLocalName(env, &ident->token))
  {
    if (GlobalBinding *slot = lookupGlobalNameSlot(ident->token, false))
    {
      if (isGlobalValue(expected_type))
      {
        allocateArray(temp_arena, slot->count, out.items);
        for (int slot_id=0; slot_id < slot->count; slot_id++)
        {
          Arrow *signature = castTerm(slot->items[slot_id]->type, Arrow);
          b32 output_type_mismatch = false;
          if (!hasFreeVars(signature->output_type, 0))
          {
            if (!equal(signature->output_type, expected_type))
              output_type_mismatch = true;
          }

          if (!output_type_mismatch)
            out.items[out.count++] = slot->items[slot_id];
        }
      }
      else
      {
        out.count = slot->count;
        out.items = (Term **)slot->items;
      }
    }
  }
  return out;
}

internal Function *
buildFunction(MemoryArena *arena, Environment *env, FunctionDecl *fun)
{
  Function *funv = 0;
  if (Expression signature = buildExpression(arena, env, &fun->signature->a, holev))
  {
    // note: store the built signature, maybe to display it later.
    fun->signature = castAst(signature.ast, ArrowAst);
    funv = newTerm(arena, Function, signature.value);
    funv->name = fun->a.token;
    funv->body = &dummy_function_under_construction;

    // note: add binding first to support recursion
    addGlobalBinding(&fun->a.token, &funv->v);

    if (noError())
    {
      addStackFrame(env);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < fun->signature->param_count; id++)
      {
        Token *name = fun->signature->param_names+id;
        introduceOnStack(arena, env, name, fun->signature->param_types[id]);
        addLocalBinding(env, name);
      }
      assert(noError());

      Term *expected_body_type = evaluate(temp_arena, env, fun->signature->output_type);
      buildSequence(arena, env, fun->body, expected_body_type);
      unwindBindingsAndStack(env);
    }

    funv->body        = fun->body;
    funv->stack_depth = getStackDepth(env);
    funv->id          = getNextFunctionId();
  }
  return funv;
}

internal Ast *
valueToAst(MemoryArena *arena, Environment *env, Term* value)
{
  Ast *out0 = 0;
  Token token = newToken("<synthetic>");
  switch (value->cat)
  {
    case Term_StackValue:
    {
      StackValue *val = castTerm(value, StackValue);
      Variable   *var = newAst(arena, Variable, &val->name);
      out0 = &var->a;
      var->stack_delta = env->stack->depth - val->stack_depth;
      var->id          = val->id;  // :stack-ref-id-has-significance
    } break;

    case Term_StackPointer:
    {
      StackPointer *ptr = castTerm(value, StackPointer);
      Variable     *var = newAst(arena, Variable, &ptr->name);
      out0 = &var->a;
      var->stack_delta = ptr->stack_delta;
      var->id          = ptr->id;  // :stack-ref-id-has-significance
    } break;

    case Term_Composite:
    {
      Composite *compositev = castTerm(value, Composite);
      CompositeAst  *composite  = newAst(arena, CompositeAst, &token);
      composite->op        = valueToAst(arena, env, compositev->op);
      composite->arg_count = compositev->arg_count;
      allocateArray(arena, composite->arg_count, composite->args);
      for (int id=0; id < composite->arg_count; id++)
      {
        composite->args[id] = valueToAst(arena, env, compositev->args[id]);
      }
      out0 = &composite->a;
    } break;

    case Term_Accessor:
    {
      Accessor *accessorv = castTerm(value, Accessor);
      AccessorAst  *accessor  = newAst(arena, AccessorAst, &token);
      accessor->record      = valueToAst(arena, env, accessorv->record);
      accessor->field_id    = accessorv->field_id;
      accessor->field_name  = newToken(accessorv->field_name);
      out0 = &accessor->a;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(value, Arrow);
      ArrowAst  *out = newAst(arena, ArrowAst, &token);
      out->param_count = in->param_count;
      out->param_names = in->param_names;
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
        out->param_types[id] = valueToAst(arena, env, in->param_types[id]);
      out->output_type = valueToAst(arena, env, in->output_type);
      out0 = &out->a;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Function:
    case Term_Constructor:
    {
      Constant *synthetic = newSyntheticConstant(arena, value);
      out0 = &synthetic->a;
    } break;

    case Term_Rewrite:
    {
      dump(); dump("-------------------"); dump(value);
      todoIncomplete;  // really we don't need it tho?
    } break;

    case Term_Hole:
    case Term_Computation:
    {todoIncomplete;}
  }

  assert(out0);

  return out0;
}
 
internal SearchOutput
searchExpression(MemoryArena *arena, Term *lhs, Term* in0)
{// todo #cleanup don't like the early returns
  SearchOutput out = {};
  if (equal(in0, lhs))
  {
    out.found = true;
    return out;
  }
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
          out.found     = true;
          out.path->first = -1;
          out.path->next  = op.path;
          return out;
        }
        for (int arg_id=0; arg_id < in->arg_count; arg_id++)
        {
          SearchOutput arg = searchExpression(arena, lhs, in->args[arg_id]);
          if (arg.found)
          {
            allocate(arena, out.path);
            out.found     = true;
            out.path->first = arg_id;
            out.path->next  = arg.path;
            return out;
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
      case Term_StackValue:
      case Term_Builtin:
      case Term_Union:
      case Term_Function:
      case Term_Constructor:
      case Term_StackPointer:
      case Term_Arrow:
      case Term_Rewrite:
      {} break;
    }
    return out;
  }
}

inline Sequence *
parseSequence(MemoryArena *arena, b32 is_theorem, b32 auto_normalize)
{
  // NOTE: we mutate the crap out of this sequence.
  Sequence *out = 0;
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
      case TC_KeywordNorm:
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

      case TC_KeywordRewrite:
      {
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);

        rewrite->right_to_left = false;
        Token next = peekToken();
        if (equal(next, "<-"))
        {
          nextToken();
          rewrite->right_to_left = true;
        }

        rewrite->eq_proof = parseExpressionToAst(arena);
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
          else if ((rewrite->to_expression = parseExpressionToAst(arena)))
          {
            if (optionalChar('{'))
            {
              if (optionalString("<-"))  // todo: don't know whether to make a token type for this.
              {
                rewrite->right_to_left = true;
              }
              rewrite->eq_proof = parseExpressionToAst(arena);
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
            case TC_DoubleColon:
            {
              Token after_dcolon = peekToken();
              b32 is_theorem;
              if (equal(after_dcolon, "fn"))
              {
                is_theorem = false;
                nextToken();
              }
              else is_theorem = true;
              FunctionDecl *fun = parseFunction(arena, name, is_theorem);
              ast = &fun->a;
            } break;

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
      if (token.cat == TC_KeywordFork)
      {
        nextToken();
        ast = &parseFork(arena, is_theorem)->a;
        stop = true;
      }
      else if (token.cat == TC_KeywordComputation)
      {
        // NOTE: Nothing to do here before typechecking. The command has to be
        // in sequence, even though it is an expression, since the expression
        // that users can supply isn't fully-formed
        nextToken();
        ast = &newAst(arena, ComputationAst, &token)->a;
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
    assert(count != 0);
    Ast **items = pushArray(arena, count, Ast*);
    for (s32 id = count-1; id >= 0; id--)
    {
      items[id] = list->first;
      list = list->next;
    }
    out = newAst(arena, Sequence, &first_token);
    out->count = count;
    out->items = items;
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

internal b32
unify(Term **values, Term *lhs, Term *rhs)
{
  b32 success = false;
  b32 debug_print = false;
  i32 debug_serial = global_debug_serial++;
  if (global_debug_mode && debug_print)
  {
    debugIndent(); dump("unify("); dump(debug_serial); dump(") ");
    dump(lhs); dump(" with "); dump(rhs); dump();
  }
  switch (lhs->cat)
  {
    case Term_StackPointer:
    {
      StackPointer *lhs_pointer = castTerm(lhs, StackPointer);
      if (lhs_pointer->stack_delta != 0)
        todoIncomplete;
      if (Term *replaced = values[lhs_pointer->id])
      {
        if (equal(replaced, rhs))
          success = true;
      }
      else if (equal(lhs->type, rhs->type))  // todo: shouldn't we unify instead
      {
        values[lhs_pointer->id] = rhs;
        success = true;
      }
    } break;

    case Term_Composite:
    {
      Composite *lhs_composite = castTerm(lhs, Composite);
      if (Composite *rhs_composite = castTerm(rhs, Composite))
      {
        if (unify(values, lhs_composite->op, rhs_composite->op))
        {
          success = true;
          for (int id=0; id < lhs_composite->arg_count; id++)
          {
            if (!unify(values, lhs_composite->args[id], rhs_composite->args[id]))
            {
              success = false;
              break;
            }
          }
        }
      }
    } break;

    default:
    {
      success = equal(lhs, rhs);
    } break;
  }
  if (global_debug_mode && debug_print)
  {
    debugDedent(); dump("=>("); dump(debug_serial); dump(") ");
    if (success) dump("true"); else dump("false"); dump();
  }
  return success;
}

forward_declare internal b32
buildSequence(MemoryArena *arena, Environment *env, Sequence *sequence, Term *goal)
{
  Environment *outer_env = env; env = outer_env;
  i32 serial = global_debug_serial++;
  if (serial == 998) {
    global_debug_mode = true;
  }

  for (s32 item_id = 0;
       (item_id < sequence->count-1) && noError();
       item_id++)
  {
    Ast *item = sequence->items[item_id];
    switch (item->cat)
    {
      case AC_Let:
      {
        Let  *let = castAst(item, Let);
        Term *type_hint = holev;
        if (let->type && let->type != LET_TYPE_NORMALIZE)
        {
          if (Expression type = buildExpression(arena, env, let->type, holev))
            type_hint = type.value;
        }
        if (noError())
        {
          if (Expression rhs = buildExpression(arena, env, let->rhs, type_hint))
          {
            addLocalBinding(env, &let->lhs);
            let->rhs = rhs.ast;
            Term *value0 = 0;
            if (let->type == LET_TYPE_NORMALIZE)
            {// type manipulation (TODO: not sure if this is legal when we actually "run the proof")
              switch (rhs.value->cat)
              {
                case Term_StackValue:
                {
                  StackValue *in    = castTerm(rhs.value, StackValue);
                  StackValue *value = copyStruct(arena, in);
                  value0 = &value->v;
                } break;
                case Term_Composite: {value0 = rhs.value;} break;
                default: {todoIncomplete;}
              }
              value0->type = normalize(arena, env, rhs.value->type);
            }
            else value0 = rhs.value;
            addStackValue(env, value0);
          }
        }
      } break;

      case AC_FunctionDecl:
      {// NOTE: common builder for both local and global function.
        buildFunction(arena, env, castAst(item, FunctionDecl));
      } break;

      case AC_RewriteAst:
      {
        RewriteAst *rewrite = castAst(item, RewriteAst);
        if (!rewrite->eq_proof)
        {
          Term *new_goal = 0;
          if (!rewrite->to_expression)
          {
            new_goal = normalize(arena, env, goal);
            rewrite->to_expression = valueToAst(arena, env, new_goal);
            if (global_debug_mode)
              breakhere;
          }
          else if (Expression build = buildExpression(arena, env, rewrite->to_expression, holev))
          {
            rewrite->to_expression = build.ast;
            new_goal               = build.value;
          }

          if (noError())
          {
            if (equal(new_goal, goal))
            {// superfluous rewrite -> remove
              for (int src_id=item_id+1; src_id < sequence->count; src_id++)
              {
                sequence->items[src_id-1] = sequence->items[src_id];
              }
              sequence->count--;
              item_id--;
            }
            else
            {
              Term *new_goal_norm = normalize(arena, env, new_goal);
              Term *goal_norm = normalize(arena, env, goal);
              if (equal(new_goal_norm, goal_norm))
              {
                ComputationAst *computation = newAst(arena, ComputationAst, &item->token);
                computation->lhs = valueToAst(arena, env, goal);
                computation->rhs = valueToAst(arena, env, new_goal);
                rewrite->eq_proof = &computation->a;
                goal = new_goal;
              }
              else
              {
                parseError(item, "new goal does not match original");
                equal(new_goal_norm, goal_norm);
                attach("new goal normalized", new_goal_norm);
                attach("current goal normalized", goal_norm);
              }
            }
          }
        }
        else if (rewrite->to_expression)
        {// diff
          if (Expression to_expression = buildExpression(arena, env, rewrite->to_expression, holev))
          {
            Term *expected_result = to_expression.value;
            CompareExpressions compare = compareExpressions(arena, goal, expected_result);
            if (compare.result.v == Trinary_True)
              parseError(item, "new goal same as current goal");
            else
            {
              rewrite->path = compare.diff_path;
              Term *from = subExpressionAtPath(goal, compare.diff_path);
              Term *to   = subExpressionAtPath(to_expression.value, compare.diff_path);

              int retry_count = 1;
              ValueArray global_overloads = {};
              Identifier *op_ident = 0;
              if ((op_ident = castAst(rewrite->eq_proof, Identifier)))
              {
                global_overloads = getGlobalOverloads(env, op_ident, holev);
                if (global_overloads.count > 1)
                  retry_count = global_overloads.count;
              }

              for (int attempt=0; attempt < retry_count; attempt++)
              {
                Term *hint = 0;
                if (retry_count > 1)
                {
                  Constant *constant = newAst(arena, Constant, &op_ident->token);
                  constant->value    = global_overloads.items[attempt];
                  hint = constant->value;
                }
                else if (Expression build_hint = buildExpression(arena, env, rewrite->eq_proof, holev))
                {
                  rewrite->eq_proof = build_hint.ast;
                  hint              = build_hint.value;
                }

                if (noError())
                {
                  Term *eq_proof = 0;
                  if (Arrow *arrowv = castTerm(hint->type, Arrow))
                  {
                    Term *output_type = arrowv->output_type;

                    Composite *eq = newTerm(temp_arena, Composite, builtins.Set);
                    eq->op        = builtins.equal;
                    eq->arg_count = 3;
                    allocateArray(temp_arena, 3, eq->args);
                    eq->args[0]   = from->type;
                    eq->args[1]   = from;
                    eq->args[2]   = to;

                    Term **values = pushArray(temp_arena, arrowv->param_count, Term *, true);
                    if (unify(values, output_type, &eq->v))
                    {
                      // todo: make a standalone typecheck function, to check type of these things
                      Composite *eq_proofc = newTerm(arena, Composite, &eq->v);
                      eq_proofc->op        = hint;
                      eq_proofc->arg_count = arrowv->param_count;
                      allocateArray(arena, arrowv->param_count, eq_proofc->args);
                      for (int id=0; id < arrowv->param_count; id++)
                      {
                        eq_proofc->args[id] = values[id];
                      }
                      eq_proof = &eq_proofc->v;
                      rewrite->eq_proof = valueToAst(arena, env, eq_proof);
                    }
                    else
                    {
                      parseError(rewrite->eq_proof, "unification failed");
                      attach("lhs", output_type);
                      attach("rhs", &eq->v);
                      attach("goal", goal);
                      attach("serial", serial);
                    }
                  }
                  else if (Composite *composite = castTerm(hint->type, Composite))
                  {
                    if (composite->op == builtins.equal)
                      eq_proof = hint;
                    else
                    {
                      parseError(rewrite->eq_proof, "invalid proof pattern");
                      attach("type", hint->type);
                    }
                  }
                  else
                  {
                    parseError(rewrite->eq_proof, "invalid proof pattern");
                    attach("type", hint->type);
                  }

                  if (noError())
                  {
                    if (Composite *eq = castTerm(eq_proof->type, Composite))
                    {
                      if (eq->op == builtins.equal)
                      {
                        Term *from, *to;
                        if (rewrite->right_to_left) {from = eq->args[2]; to = eq->args[1];}
                        else                        {from = eq->args[1]; to = eq->args[2];}
                        Term *actual_result = rewriteExpression(arena, to, rewrite->path, goal);
                        if (equal(actual_result, expected_result))
                          goal = actual_result;
                        else
                        {
                          parseError(item, "invalid full-rewrite");
                          dump("rewrite path"); print(0, rewrite->path); dump();
                          attach("original goal", goal);
                          attach("expected rewrite result", expected_result);
                          attach("actual rewrite result", actual_result);
                          attach("rewrite from", from);
                          attach("rewrite to", to);
                        }
                      }
                    }
                  }
                }

                if (retry_count > 1)
                {
                  if (hasError())
                  {
                    wipeError();
                    if (attempt == retry_count-1)
                      parseError(&op_ident->a, "found no suitable overload");
                  }
                  else break;
                }
              }
            }
          }
        }
        else
        {// search
          if (Expression eq_proof = buildExpression(arena, env, rewrite->eq_proof, holev))
          {
            b32 rule_valid = false;
            rewrite->eq_proof = eq_proof.ast;
            if (Composite *eq = castTerm(eq_proof.value->type, Composite))
            {
              if (eq->op == builtins.equal)
              {
                Term *from, *to;
                rule_valid = true;
                if (rewrite->right_to_left) {from = eq->args[2]; to = eq->args[1];}
                else                        {from = eq->args[1]; to = eq->args[2];}

                SearchOutput search = searchExpression(arena, from, goal);
                if (search.found)
                {
                  rewrite->path = search.path;
                  goal = rewriteExpression(arena, to, rewrite->path, goal);
                }
                else
                {
                  parseError(item, "substitution has no effect");
                  attach("substitution", eq_proof.value->type);
                  attach("goal", goal);
                }
              }
            }

            if (!rule_valid)
            {
              parseError(eq_proof.ast, "please provide a proof of equality that can be used for substitution");
              attach("got", eq_proof.value->type);
              attach("goal", goal);
            }
          }
        }
      } break;

      invalidDefaultCase;
    }
  }

  if (noError())
  {
    Ast *last = sequence->items[sequence->count-1];
    if (Fork *fork = castAst(last, Fork))
      buildFork(arena, env, fork, goal);

    else if (ComputationAst *computation = castAst(last, ComputationAst))
    {
      b32 goal_valid = false;
      if (Composite *eq = castTerm(goal, Composite))
      {
        if (eq->op == builtins.equal)
        {
          goal_valid = true;
          Term *lhs = normalize(temp_arena, env, eq->args[1]);
          Term *rhs = normalize(temp_arena, env, eq->args[2]);
          if (equal(lhs, rhs))
          {
            computation->lhs = valueToAst(arena, env, eq->args[1]);
            computation->rhs = valueToAst(arena, env, eq->args[2]);
          }
          else
          {
            parseError(last, "equality cannot be proven by computation");
            attach("lhs", lhs);
            attach("rhs", rhs);
          }
        }
      }
      if (!goal_valid)
      {
        parseError(last, "computation can only prove equality");
        attach("got", goal);
      }
    }
    else if (Expression build_last = buildExpression(arena, env, sequence->items[sequence->count-1], goal))
    {
      sequence->items[sequence->count-1] = build_last.ast;
    }
  }
  return noError();
}

forward_declare internal void
buildFork(MemoryArena *arena, Environment *env, Fork *fork, Term *expected_type)
{
  assert(expected_type);
  if (Expression subject = buildExpression(arena, env, fork->subject, holev))
  {
    fork->subject = subject.ast;
    s32 case_count = fork->case_count;

    if (Union *uni = castTerm(subject.value->type, Union))
    {
      if (uni->ctor_count == case_count)
      {
        Sequence **correct_bodies = pushArray(arena, case_count, Sequence *, true);
        Term *subjectv = subject.value;
        Environment *outer_env = env;

        for (s32 input_case_id = 0;
             input_case_id < case_count && noError();
             input_case_id++)
        {
          Environment env_ = *outer_env;
          Environment *env = &env_;
          extendBindings(temp_arena, env);
          addStackFrame(env);
          Token *ctor_name = &fork->parsing->ctors[input_case_id].token;

          Constructor *ctor = 0;
          for (i32 id = 0; id < uni->ctor_count; id++)
          {
            if (equal((uni->ctors+id)->name.string, ctor_name->string))
            {
              ctor = uni->ctors+id;
              break;
            }
          }

          if (ctor)
          {
            Term *record = introduceRecord(temp_arena, env, subjectv, ctor);
            addRewriteRule(env, subjectv, record);
            if (correct_bodies[ctor->id])
            {
              parseError(&fork->bodies[input_case_id]->a, "fork case handled twice");
              attach("constructor", &ctor->v);
            }
            else
            {
              buildSequence(arena, env, fork->bodies[input_case_id], expected_type);
              correct_bodies[ctor->id] = fork->bodies[input_case_id];
            }
          }
          else parseError(ctor_name, "expected a constructor");

          unwindBindingsAndStack(env);
        }

        if (noError())
        {
          fork->a.cat  = AC_Fork;
          fork->uni    = uni;
          fork->bodies = correct_bodies;
        }
      }
      else
        parseError(&fork->a, "wrong number of cases, expected: %d, got: %d",
                   uni->ctor_count, fork->case_count);
    }
    else
    {
      parseError(fork->subject, "cannot fork expression of type");
      attach("type", subject.value->type);
    }
  }
}

internal Ast *
fillHole(MemoryArena *arena, Environment *env, Token *token, Term *goal)
{
  Ast *out = 0;
  if (matchType(env, goal, &builtins.True->v))
  {
    Constant *truth = newSyntheticConstant(arena, &builtins.truth->v, token);
    out = &truth->a;
  }
  else if (Composite *eq = castTerm(goal, Composite))
  {
    if (eq->op == builtins.equal)
    {
      if (equal(normalize(temp_arena, env, eq->args[1]),
                   normalize(temp_arena, env, eq->args[2])))
      {
        ComputationAst *computation = newAst(arena, ComputationAst, token);
        computation->lhs = valueToAst(arena, env, eq->args[1]);
        computation->rhs = valueToAst(arena, env, eq->args[2]);
        out = &computation->a;
      }
    }
  }
  return out;
}

forward_declare internal Expression
buildExpression(MemoryArena *arena, Environment *env, Ast *in0, Term *goal)
{
  // todo #mem: we just put everything in the arena, including scope values.
  // todo #speed: normalizing expected_type.
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 serial = global_debug_serial++;
  Expression out = {};
  assert(goal);
  b32 should_check_type = (goal != holev);

  switch (in0->cat) check_switch(expression)
  {
    case AC_Hole:
    {
      // Holes are awesome, flexible placeholders that you can feed to the
      // typechecker to get what you want
      Ast *fill = fillHole(arena, env, &in0->token, goal);
      if (fill)
      {
        return buildExpression(arena, env, fill, goal);
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

    case AC_Variable:
    {
      out.ast   = in0;
      out.value = evaluate(arena, env, in0);
    } break;

    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out.ast   = in0;
      out.value = in->value;
    } break;

    case AC_Identifier:
    {
      // NOTE: do not mutate input since we wanna retry on failure.
      Token *name = &in0->token;
      if (LookupLocalName local = lookupLocalName(env, name))
      {
        Variable *var    = newAst(arena, Variable, &in0->token);
        var->id          = local.var_id;
        var->stack_delta = local.stack_delta;

        out.ast   = &var->a;
        out.value = evaluate(arena, env, out.ast);
      }
      else
      {
        Constant *constant = newAst(arena, Constant, name);

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
            attach("expected_type", normalize(temp_arena, env, goal));
          }
        }

        if (value)
        {
          should_check_type = false;
          constant->value = value;
          out.ast   = &constant->a;
          out.value = constant->value;
        }
      }
    } break;

    case AC_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);

      b32 has_multiple_overloads;
      if (Identifier *op_ident = castAst(in->op, Identifier))
      {
        ValueArray global_overloads = getGlobalOverloads(env, op_ident, goal);
        has_multiple_overloads = global_overloads.count > 1;
        if (has_multiple_overloads)
        {
          // NOTE: pre-empt operator overloads.
          // play with op.globals to figure out the output type;
          // we'd have to pretty much build, typecheck and evaluate the whole thing.
          // todo #mem
          for (s32 candidate_id=0; candidate_id < global_overloads.count; candidate_id++)
          {
            Constant *constant = newAst(arena, Constant, &in->op->token);
            constant->value    = global_overloads.items[candidate_id];

            CompositeAst *in_copy = castAst(deepCopy(arena, in0), CompositeAst);
            in_copy->op        = &constant->a;
            out = buildExpression(arena, env, &in_copy->a, goal);

            if (out) break;
            else     wipeError();
          }
          if (!out)
            parseError(in->op, "there is no suitable function overload");
        }
        else if (global_overloads.count == 1)
        {
          Constant *constant = newAst(arena, Constant, &in->op->token);
          constant->value    = global_overloads.items[0];
          in->op = &constant->a;
        }
      }
      else
        has_multiple_overloads = false;

      if (!has_multiple_overloads)
      {
        local_persist i32 serial = 0;
        serial++;
        if (serial == 137)
        {
          global_debug_mode = true;
        }
        if (Expression op = buildExpression(arena, env, in->op, holev))
        {
          in->op = op.ast;

          if (Arrow *signature = castTerm(op.value->type, Arrow))
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
                    in->args[param_id] = &newAst(arena, Hole, &op.ast->token)->a;
                  }
                  else
                  {
                    assert(arg_id < explicit_param_count);
                    in->args[param_id] = supplied_args[arg_id++];
                  }
                }
              }
              else
              {// note: there might either be too many or too few  arguments
                parseError(&in0->token, "argument count does not match the number of explicit parameters (expected: %d, got: %d)", explicit_param_count, in->arg_count);
              }
            }

            if (noError())
            {
              Term **args = pushArray(temp_arena, in->arg_count, Term*);
              for (int arg_id = 0;
                   (arg_id < in->arg_count) && noError();
                   arg_id++)
              {
                Term *param_type0 = signature->param_types[arg_id];
                Term *expected_arg_type = evaluateArrow(temp_arena, args, param_type0, 0);

                // Typecheck & Inference for the arguments. TODO: the hole stuff
                // is kinda hard-coded only for the equality.
                if (in->args[arg_id]->cat == AC_Hole)
                {
                  if (Ast *fill = fillHole(arena, env, &in->args[arg_id]->token, expected_arg_type))
                  {
                    in->args[arg_id] = fill;
                    args[arg_id]     = evaluate(arena, env, fill);
                  }
                  else args[arg_id] = holev;
                }
                else
                {
                  if (Expression arg = buildExpression(arena, env, in->args[arg_id], expected_arg_type))
                  {
                    in->args[arg_id] = arg.ast;
                    args[arg_id]     = arg.value;
                    if (expected_arg_type == holev)
                    {
                      StackPointer *param_type = castTerm(param_type0, StackPointer);
                      assert(param_type->stack_delta == 0);
                      args[param_type->id] = arg.value->type;

                      // write back to the input ast.
                      in->args[param_type->id] = valueToAst(arena, env, arg.value->type);
                    }
                  }
                }
              }

              for (s32 arg_id = 0;
                   arg_id < in->arg_count && noError();
                   arg_id++)
              {
                if (in->args[arg_id]->cat == AC_Hole)
                  parseError(in->args[arg_id], "Cannot fill hole");
              }

              if (noError())
              {
                out.ast   = in0;
                out.value = evaluate(arena, env, in0);
              }
            }
          }
          else
          {
            parseError(in->op, "operator must have an arrow type");
            attach("got type", op.value->type);
          }
        }
      }
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);

      addStackFrame(env);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < in->param_count && noError(); id++)
      {
        Expression param_type = buildExpression(arena, env, in->param_types[id], holev);
        if (param_type)
        {
          in->param_types[id] = param_type.ast;
          Token *name = in->param_names+id;
          introduceOnStack(arena, env, name, param_type.value);
          addLocalBinding(env, name);
        }
      }

      if (noError())
      {
        if (in->output_type)
        {
          if (Expression output_type = buildExpression(arena, env, in->output_type, holev))
            in->output_type = output_type.ast;
        }
      }
      unwindBindingsAndStack(env);

      if (noError())
      {
        out.ast   = in0;
        out.value = evaluate(arena, env, in0);
      }
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      if (Expression build_record = buildExpression(arena, env, in->record, holev))
      {
        Ast   *record   = build_record.ast;
        Term *recordv0 = build_record.value;
        if (Composite *recordv = castTerm(recordv0, Composite))
        {
          in->record = record;
          Arrow *op_type = castTerm(recordv->op->type, Arrow);
          s32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          for (s32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->field_name, op_type->param_names[param_id]))
            {
              in->field_id = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
          {
            out.ast   = in0;
            out.value = evaluate(arena, env, in0);
          }
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", recordv->op);
            attach("in type", op_type->output_type);
          }
        }
        else
        {
          parseError(record, "cannot access a non-record");
          attach("record", recordv0);
        }
      }
    } break;

    case AC_ComputationAst:
    {
      out.ast   = in0;
      out.value = evaluate(arena, env, in0);
    } break;

    case AC_Lambda:
    {
      if (Arrow *signature = castTerm(goal, Arrow))
      {
        Lambda   *in  = castAst(in0, Lambda);
        Function *fun = newTerm(arena, Function, goal);

        addStackFrame(env);
        extendBindings(temp_arena, env);
        for (s32 id=0; id < signature->param_count; id++)
        {
          Token *name = signature->param_names+id;
          Term *param_type = evaluateArrow(arena, env->stack->items, signature->param_types[id], 0);
          introduceOnStack(arena, env, name, param_type);
          addLocalBinding(env, name);
        }
        assert(noError());

        Term *expected_body_type = evaluateArrow(arena, env->stack->items, signature->output_type, 0);
        if (buildSequence(arena, env, in->body, expected_body_type))
        {
          in->signature = castAst(valueToAst(arena, env, goal), ArrowAst);
          assert(in->signature);
          fun->body        = in->body;
          fun->stack_depth = getStackDepth(env);
          out.ast   = in0;
          out.value = &fun->v;
        }

        unwindBindingsAndStack(env);

      }
      else
      {
        parseError(in0, "lambda has to have an arrow type");
        attach("goal", goal);
      }
    } break;

    invalidDefaultCase;
  }

  if (noError() && should_check_type)
  {// one last typecheck if needed
    Term *actual   = out.value->type;
    Term *expected = goal;
    if (!matchType(env, actual, expected))
    {
      parseError(in0, "actual type differs from expected type");
      attach("got", actual);
      attach("expected", expected);
      attach("serial", serial);
      // if (serial == 320) {global_debug_mode = true; matchType(env, actual, expected);}
    }
  }

  if (ParseError *error = getError())
    error->code = ErrorWrongType;

  NULL_WHEN_ERROR(out);
  return out;
}

inline Expression
parseExpression(MemoryArena *arena, LocalBindings *bindings, Term *expected_type)
{
  Expression out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Environment env = {};
    env.bindings = bindings;
    if (Expression build = buildExpression(arena, &env, ast, expected_type))
    {
      out.ast   = build.ast;
      out.value = build.value;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Ast *
parseExpression(MemoryArena *arena)
{
  return parseExpression(arena, 0, holev).ast;
}

inline Expression
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
        if (Sequence *body = parseSequence(arena, is_theorem, false))
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

forward_declare internal Fork *
parseFork(MemoryArena *arena, b32 is_theorem)
{
  Fork *out = 0;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpressionToAst(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *global_tokenizer;
    s32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      ForkParsing *parsing = pushStruct(temp_arena, ForkParsing);
      Sequence **bodies = pushArray(temp_arena, case_count, Sequence*);
      allocateArray(temp_arena, case_count, parsing->ctors);

      s32 actual_case_count = 0;
      for (b32 stop = false;
           !stop && noError();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContext("fork case");
          auto input_case_id = actual_case_count++;
          if (Ast *pattern0 = parseExpressionToAst(temp_arena))
          {
            if (Identifier *ctor = castAst(pattern0, Identifier))
            {
              parsing->ctors[input_case_id]  = *ctor;
            }
            else if (CompositeAst *pattern = castAst(pattern0, CompositeAst))
            {// todo don't need this case anymore
              if ((ctor = castAst(pattern->op, Identifier)))
              {
                parsing->ctors[input_case_id] = *ctor;
              }
              else
                parseError(&pattern->a, "expected constructor");
            }
            else
                parseError(pattern0, "malformed fork pattern");

            if (requireChar(':', "syntax: CASE: BODY"))
            {
              b32 auto_normalize = is_theorem ? true : false;
              if (Sequence *body = parseSequence(arena, is_theorem, auto_normalize))
              {
                bodies[input_case_id] = body;
                if (!optionalChar(','))
                {
                  requireChar('}', "to end fork expression; or use ',' to end the fork case");
                  stop = true;
                }
              }
            }
          }
          popContext();
        }
      }

      if (noError())
      {
        assert(case_count == actual_case_count);
        out = newAst(arena, Fork, &token);
        out->a.token    = token;
        out->subject    = subject;
        out->case_count = case_count;
        out->bodies     = bodies;
        out->parsing    = parsing;
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
        initComposite(branch, op, expected_arg_count, args);
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
          s32 precedence = precedenceOf(&op_token);
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
              initComposite(new_operand, &op->a, arg_count, args);
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
  initValue(&ctor->v, Term_Constructor, 0);
  ctor->uni  = uni;
  ctor->name = nextToken();
  ctor->id   = ctor_id;
  Token *ctor_name = &ctor->name;

  if (isIdentifier(ctor_name))
  {
    if (optionalChar(':'))
    {// subtype
      Arrow *struct_;
      pushContext("struct {FIELD: TYPE ...}");
      if (requireCategory(TC_KeywordStruct))
      {
        ArrowAst *ast = parseArrowType(arena, true);
        Environment env_ = {}; Environment *env = &env_;
        // todo there are hacks we have to do to accept arrow type without
        // output type, which is dumb since the output type exists.
        if (Expression build = buildExpression(arena, env, &ast->a, holev))
          struct_ = castTerm(build.value, Arrow);
      }
      popContext();

      if (noError())
      {
        struct_->output_type = &uni->v;
        ctor->type = &struct_->v;
      }
    }
    else
    {// enum constructor
      if (uni->type == builtins.Set) ctor->type = &uni->v;
      else parseError(ctor_name, "constructors must construct a set member");
    }

    if (noError()) addGlobalBinding(ctor_name, &ctor->v);
  }
  else tokenError("expected an identifier as constructor name");
}

internal void
parseUnion(MemoryArena *arena, Token *name)
{
  // NOTE: the type is in scope of its own constructor.
  Term *type = builtins.Set;
  if (optionalChar(':'))
  {// type override
    b32 valid_type = false;
    if (Expression type_parsing = parseExpressionFull(arena))
    {
      Term *norm_type = evaluate(arena, type_parsing.ast);
      if (Arrow *arrow = castTerm(norm_type, Arrow))
      {
        if (arrow->output_type == builtins.Set)
          valid_type = true;
      }
      else if (norm_type == builtins.Set)
        valid_type = true;

      if (valid_type)
      {
        type = norm_type;
      }
      else
      {
        parseError(type_parsing.ast, "form has invalid type");
        attach("type", norm_type);
      }
    }
  }

  if (noError())
  {
    Union *uni = newTerm(arena, Union, type);
    uni->name = *name;
    addGlobalBinding(name, &uni->v);

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
        case MetaDirective_Null_:
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

        invalidDefaultCase;
      }
    }
    else
    {
      if (token.cat == TC_KeywordBreakhere)
      {
        breakhere;
        global_debug_mode = true;
      }
      else if (equal(token, "compare_expressions"))
      {
        if (Expression lhs = parseExpressionFull(temp_arena))
        {
          requireChar(',');
          if (Expression rhs = parseExpressionFull(temp_arena))
          {
            CompareExpressions compare = compareExpressions(temp_arena, lhs.value, rhs.value);
            (void)compare;
          }
        }
      }
      else if (equal(token, "print"))
      {
        if (Expression expr = parseExpressionFull(temp_arena))
        {
#if 1
          Term *norm = normalize(arena, empty_env, expr.value);
          print(0, norm, {.detailed=true});
#else
          Value *norm = normalize(arena, empty_env, expr.value);
          dump("type before norm:"); dump(expr.value->type); dump();
          dump("type after norm:");  dump(norm->type); dump();
          print(0, norm->type, {.detailed=true});
#endif
          print(0, "\n");
        }
      }
      else if (equal(token, "print_raw"))
      {
        if (auto parsing = parseExpressionFull(temp_arena))
        {
          print(0, parsing.value, {.detailed=true});
          print(0, ": ");
          print(0, parsing.value->type, {});
          print(0, "\n");
        }
      }
      else if (equal(token, "print_debug"))
      {
        if (Ast *exp = parseExpression(temp_arena))
        {
          print(0, exp, {.detailed=true, .print_type=true});
        }
      }
      else if (equal(token, "check"))
      {
        Term *expected_type = 0;
        if (Ast *ast = parseExpressionToAst(temp_arena))
        {
          if (optionalChar(':'))
          {
            if (Ast *type = parseExpression(temp_arena))
              expected_type = evaluate(temp_arena, type);
          }
          if (noError())
            buildExpression(temp_arena, empty_env, ast, expected_type);
        }
      }
      else if (equal(token, "check_truth"))
      {
        if (Term *goal = parseExpressionFull(temp_arena).value)
        {
          if (Composite *eq = castTerm(goal, Composite))
          {
            b32 goal_valid = false;
            if (eq->op == builtins.equal)
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
      }
      else if (isIdentifier(&token))
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
            if (Ast *rhs = parseExpression(arena))
            {
              Term *value = evaluate(arena, rhs);
              addGlobalBinding(&token, value);
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
                buildFunction(arena, empty_env, fun);
            }
          } break;

          case ':':
          {
            if (Expression parse_type = parseExpressionFull(arena))
            {
              if (requireCategory(TC_ColonEqual, "require :=, syntax: name : type := value"))
              {
                Term *type = evaluate(arena, parse_type.ast);
                if (Expression parse_value = parseExpression(arena, 0, type))
                {
                  Term *value = evaluate(arena, parse_value.ast);
                  addGlobalBinding(&token, value);
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
      else
        tokenError("unexpected token to begin top-level form");
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

forward_declare inline Expression
parseExpressionFromString(MemoryArena *arena, char *string)
{
  Tokenizer tk = newTokenizer(String{}, 0);
  Tokenizer *tk_save = global_tokenizer;
  global_tokenizer = &tk;
  tk.at = string;
  Expression out = parseExpressionFull(arena);
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
      builtins.Type->type = builtins.Type; // NOTE: circular types, might bite us
      addBuiltinGlobalBinding("Type", builtins.Type);

      builtins.Set = newTerm(arena, Builtin, builtins.Type);
      addBuiltinGlobalBinding("Set", builtins.Set);
    }

    {// more builtins
      Tokenizer builtin_tk = newTokenizer(print(temp_arena, "<builtin>"), 0);
      global_tokenizer = &builtin_tk;
      builtin_tk.at = "(_A: Set, a, b: _A) -> Set";
      Expression equal_type = parseExpressionFull(arena); 
      builtins.equal = newTerm(arena, Builtin, equal_type.value);
      addBuiltinGlobalBinding("=", builtins.equal);

      builtin_tk.at = "(_A: Set, x: _A) -> =(_A, x, x)";
      Expression refl_type = parseExpressionFull(arena);
      builtins.refl = newTerm(arena, Constructor, refl_type.value);
      builtins.refl->name = newToken("refl");
      addBuiltinGlobalBinding("refl", &builtins.refl->v);

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

  assert(arrayCount(keywords)       == TC_KeywordEnd_ - TC_KeywordBegin_);
  assert(arrayCount(metaDirectives) == MetaDirective_Count_);

  void   *permanent_memory_base = (void*)teraBytes(2);
  size_t  permanent_memory_size = megaBytes(256);
  permanent_memory_base = platformVirtualAlloc(permanent_memory_base, permanent_memory_size);
  MemoryArena  permanent_arena_ = newArena(permanent_memory_size, permanent_memory_base);
  permanent_arena  = &permanent_arena_;

  void   *temp_memory_base = (void*)teraBytes(3);
  size_t  temp_memory_size = megaBytes(2);
  temp_memory_base = platformVirtualAlloc(temp_memory_base, permanent_memory_size);
  MemoryArena temp_arena_ = newArena(temp_memory_size, temp_memory_base);
  temp_arena              = &temp_arena_;

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/basics.rea"))
    success = false;
  resetArena(permanent_arena, true);
#endif

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/test.rea"))
    success = false;
  resetArena(permanent_arena, true);
#endif

  return success;
}

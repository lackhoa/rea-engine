/*
  General Todos: 
  - Replace all token <-> string comparison with keyword checks.
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"

i32 debug_normalization_depth;
i32 debug_evaluation_depth;
i32 debug_serial;

global_variable Builtins builtins;

global_variable Value  holev_ = {.cat = VC_Hole};
global_variable Value *holev = &holev_;

global_variable Sequence dummy_function_under_construction;

inline void
dump(Trinary trinary)
{
  if (trinary == Trinary_True) dump("true");
  else if (trinary == Trinary_False) dump("false");
  else dump("unknown");
}

inline OverwriteRules *
newOverwriteRule(Environment *env, Value *lhs, Value *rhs)
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
dump(Value *in0)
{
  print(0, in0, {});
}

inline void
dump(Ast *in0)
{
  print(0, in0, {});
}

inline void
dump(Stack *stack)
{
  dump("[");
  while (stack)
  {
    dump("[");
    for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
    {
      dump(stack->items[arg_id]);
      if (arg_id != stack->count-1)
        dump(", ");
    }
    dump("]");
    stack = stack->outer;
    if (stack)
      dump(", ");
  }
  dump("]");
}

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
paramImplied(Arrow *arrow, s32 param_id)
{
  return arrow->param_names[param_id].string.chars[0] == '_';
}

inline b32
paramImplied(ArrowV *arrow, s32 param_id)
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

// prints both Composite and CompositeV
inline void
printComposite(MemoryArena *buffer, void *in0, b32 is_value, PrintOptions opt)
{
  int    precedence = 0;  // todo: no idea what the default should be
  void  *op;
  s32    arg_count;
  void **raw_args;

  Ast   *ast   = (Ast *)in0;
  Value *value = (Value *)in0;
  ArrowV *op_type = 0;
  if (is_value)
  {
    CompositeV *in = castValue(value, CompositeV);
    op       = in->op;
    raw_args = (void **)in->args;
    op_type  = castValue(in->op->type, ArrowV);
    assert(op_type);

    if (FunctionV *op_fun = castValue(in->op, FunctionV))
      precedence = precedenceOf(&op_fun->a.token);
  }
  else
  {
    Composite *in = castAst(ast, Composite);
    op       = in->op;
    raw_args = (void **)in->args;
    if (Constant *op = castAst(in->op, Constant))
    {
      op_type = castValue(op->value->type, ArrowV);
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
      if (!paramImplied(op_type, param_id))
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

      case AC_Rewrite:
      {
        Rewrite *in = castAst(in0, Rewrite);
        print(buffer, "rewrite");
        print(buffer, in->path);
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof, new_opt);
      } break;

      case AC_Composite:
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

      case AC_Arrow:
      {
        Arrow *in = castAst(in0, Arrow);
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

      case AC_Accessor:
      {
        Accessor *in = castAst(in0, Accessor);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name);
      } break;

      case AC_Replace:
      {
        print(buffer, "replace");
      } break;

      case AC_FunctionDecl:
      {
        print(buffer, "function decl");
      } break;

      case AC_Let:
      {
        print(buffer, "let");
      } break;

      case AC_Computation:
      {
        Computation *computation = castAst(in0, Computation);
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
print(MemoryArena *buffer, Value *in0, PrintOptions opt)
{// mark: printValue
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed   = false;
    new_opt.print_type = false;
    new_opt.indentation = opt.indentation + 1;

    switch (in0->cat)
    {
      case VC_Null:
      {
        print(buffer, "<NULL>");
      } break;

      case VC_Hole:
      {
        print(buffer, "_");
      } break;

      case VC_StackValue:
      {
        StackValue *in = castValue(in0, StackValue);
#if 0
        print(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
#else
        print(buffer, in->name);
#endif
      } break;

      case VC_CompositeV:
      {
        printComposite(buffer, in0, true, new_opt);
      } break;

      case VC_Union:
      {
        Union *in = castValue(in0, Union);
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

      case VC_FunctionV:
      {
        FunctionV *in = castValue(in0, FunctionV);
        print(buffer, in->a.token);
        if (opt.detailed)
        {
          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          print(buffer, &in->body->a, new_opt);
          print(buffer, "}");
        }
      } break;

      case VC_ArrowV:
      {
        ArrowV *in = castValue(in0, ArrowV);
        print(buffer, &in->a, opt);
      } break;

      case VC_BuiltinEqual:
      {
        print(buffer, "=");
      } break;

      case VC_BuiltinSet:
      {
        print(buffer, "Set");
      } break;

      case VC_BuiltinType:
      {
        print(buffer, "Type");
      } break;

      case VC_Constructor:
      {
        Constructor *in = castValue(in0, Constructor);
        print(buffer, in->name);
      } break;

      case VC_HeapValue:
      {
        HeapValue *in = castValue(in0, HeapValue);
        print(buffer, &in->accessor.v, new_opt);
      } break;

      case VC_RewriteV:
      {
        RewriteV *rewrite = castValue(in0, RewriteV);
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

      case VC_ComputationV:
      {
        print(buffer, "computation: (");
        ComputationV *computation = castValue(in0, ComputationV);
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, "(");
      } break;

      case VC_AccessorV:
      {
        AccessorV *in = castValue(in0, AccessorV);
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
print(MemoryArena *buffer, void *in0, b32 is_value, PrintOptions opt)
{
  if (is_value)
    return print(buffer, (Value*)in0, opt);
  else
    return print(buffer, (Ast*)in0, opt);
}

inline void
addStackFrame(Environment *env)
{
  Stack *stack = pushStruct(temp_arena, Stack);
  stack->depth = getStackDepth(env->stack) + 1;
  stack->outer = env->stack;
  stack->count = 0;
  env->stack = stack;
}

inline void
addStackValue(Environment *env, Value *value)
{
  env->stack->items[env->stack->count++] = value;
}

inline void
extendStack(Environment *env, s32 count, Value **args)
{
  assert(count <= arrayCount(env->stack->items));
  addStackFrame(env);
  for (s32 arg_id = 0; arg_id < count; arg_id++)
  {// todo: #speed copying values around
    addStackValue(env, args[arg_id]);
  }
}

inline b32
equalB32(Value *lhs, Value *rhs)
{
  return equalTrinary(lhs, rhs) == Trinary_True;
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

      case AC_Composite:
      {
        auto l = castAst(lhs, Composite);
        auto r = castAst(rhs, Composite);
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
        return equalB32(l->value, r->value);
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
isCompositeConstructor(Value *in0)
{
  if (CompositeV *in = castValue(in0, CompositeV))
    return in->op->cat == VC_Constructor;
  else
    return false;
}

forward_declare internal CompareExpressions
compareExpressions(MemoryArena *arena, Value *lhs0, Value *rhs0)
{
  CompareExpressions out = {};

  b32 debug = false;
  if (debug && global_debug_mode)
  {
    debug_serial++;
    debugIndent(); dump("comparing("); dump(debug_serial); dump("): "); dump(lhs0); dump(" and "); dump(rhs0); dump();
    if (debug_serial == 2658)
      breakhere;
  }

  out.result = Trinary_Unknown;

  if (!lhs0 | !rhs0)
    out.result = Trinary_False;
  else if (lhs0 == rhs0)
    out.result = Trinary_True;
  else if (lhs0->cat == rhs0->cat)
  {
    switch (lhs0->cat)
    {
      case VC_StackValue:
      {
        StackValue* lhs = castValue(lhs0, StackValue);
        StackValue* rhs = castValue(rhs0, StackValue);
        if ((lhs->stack_depth == rhs->stack_depth) && (lhs->id == rhs->id))
          out.result = Trinary_True;
      } break;

      case VC_ArrowV:
      {
        ArrowV* lhs = castValue(lhs0, ArrowV);
        ArrowV* rhs = castValue(rhs0, ArrowV);

        s32 param_count = lhs->param_count;
        if (rhs->param_count == param_count)
        {
          Environment env = {};
          addStackFrame(&env);
          env.stack->depth = maximum(lhs->stack_depth, rhs->stack_depth)+1;
          // todo: maybe add negative affirmation 
          b32 type_mismatch = false;
          for (s32 id = 0; id < param_count; id++)
          {
            if (equalB32(evaluate(temp_arena, &env, lhs->param_types[id]),
                         evaluate(temp_arena, &env, rhs->param_types[id])))
            {
              introduceOnStack(&env, lhs->param_names+id, lhs->param_types[id]);
            }
            else
            {
              type_mismatch = true;
              break;
            }
          }
          if (!type_mismatch)
          {
            out.result = equalTrinary(evaluate(temp_arena, &env, lhs->output_type),
                                      evaluate(temp_arena, &env, rhs->output_type));
          }
        }
        else out.result = Trinary_False;
      } break;

      case VC_CompositeV:
      {
        CompositeV *lhs = castValue(lhs0, CompositeV);
        CompositeV *rhs = castValue(rhs0, CompositeV);

        Trinary op_compare = equalTrinary((lhs->op), (rhs->op));
        if ((op_compare == Trinary_False) &&
            (lhs->op->cat == VC_Union) &&
            (rhs->op->cat == VC_Union))
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
            CompareExpressions recurse = compareExpressions(arena, lhs->args[id], rhs->args[id]);
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

      case VC_Constructor:
      {
        Constructor *lhs = castValue(lhs0, Constructor);
        Constructor *rhs = castValue(rhs0, Constructor);
        out.result = (Trinary)(lhs->id == rhs->id);
      } break;

      case VC_BuiltinEqual:
      case VC_BuiltinType:
      case VC_BuiltinSet:
      {
        out.result = Trinary_True;
      } break;

      case VC_FunctionV:  // we can compare signatures to eliminate negatives.
      case VC_Null:
      case VC_Hole:
      case VC_HeapValue:
      case VC_Union:
      case VC_RewriteV:
      case VC_ComputationV:
      case VC_AccessorV:
      {
        out.result = Trinary_Unknown;
      } break;
    }
  }
  else if (((lhs0->cat == VC_Constructor) && isCompositeConstructor(rhs0)) ||
           ((rhs0->cat == VC_Constructor) && isCompositeConstructor(lhs0)))
  {
    out.result = Trinary_False;
  }

  if (debug && global_debug_mode)
  {
    debugDedent(); dump("=> "); dump(out.result); dump();
  }

  return out;
}

forward_declare internal Trinary
equalTrinary(Value *lhs0, Value *rhs0)
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

internal Value *
repeatedOverwrite(Environment *env, Value *in)
{
  Value *out = 0;
  // todo: find some way to early out in case expression can't be rewritten
  // if (canBeRewritten(in))
  // todo: #speed this is O(n)
  for (OverwriteRules *rewrite = env->overwrite;
       rewrite && !out;
       rewrite = rewrite->next)
  {
    if (equalB32(in, rewrite->lhs))
      out = rewrite->rhs;
  }
  if (!out)
    out = in;

  return out;
}

forward_declare internal Value *
evaluateFork(MemoryArena *arena, Environment *env, Fork *fork)
{
  Value *out;
  Value *subject = evaluateAndNormalize(arena, env, fork->subject);
  {
    switch (subject->cat)
    {// note: we fail if the fork is undetermined
      case VC_Constructor:
      {
        Constructor *ctor = castValue(subject, Constructor);
        out = evaluateSequence(arena, env, fork->bodies[ctor->id]);
      } break;

      case VC_CompositeV:
      {
        CompositeV *record = castValue(subject, CompositeV);
        if (Constructor *ctor = castValue(record->op, Constructor))
          out = evaluateSequence(arena, env, fork->bodies[ctor->id]);
        else
          out = 0;
      } break;

      default:
        out = 0;
    }
  }
  return out;
}

struct ValuePair {Value *lhs; Value *rhs;};

inline ValuePair getEqualitySides(Value *eq0)
{
  CompositeV *eq = castValue(eq0, CompositeV);
  assert(eq->op == &builtins.equal->v);
  return ValuePair{eq->args[1], eq->args[2]};
}

internal Value *
rewriteExpression(MemoryArena *arena, Value *rhs, TreePath *path, Value *in0)
{
  if (path)
  {
    CompositeV *in  = castValue(in0, CompositeV);
    CompositeV *out = copyStruct(arena, in);
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
  RewriteV     *first;
  RewriteChain *next;
};

forward_declare internal Value *
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
      case AC_Rewrite:
      {
        Rewrite  *rewrite  = castAst(item, Rewrite);
        RewriteV *rewritev = newValue(arena, RewriteV, 0);
        Value *eq_proof = evaluateAndNormalize(arena, env, rewrite->eq_proof);
        rewritev->eq_proof      = eq_proof;
        rewritev->right_to_left = rewrite->right_to_left;
        rewritev->path          = rewrite->path;
        if (rewrite_chain)
        {
          RewriteV *outer_rewrite = rewrite_chain->first;
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
        Value *rhs = evaluateAndNormalize(arena, env, let->rhs);
        addStackValue(env, rhs);
      } break;

      case AC_FunctionDecl:
      {
        FunctionDecl *fun         = castAst(item, FunctionDecl);
        Value        *signature_v = evaluate(arena, env, &fun->signature->a);
        FunctionV    *funv        = newValue(arena, FunctionV, signature_v);
        funv->function = *fun;
        funv->stack    = env->stack;
        addStackValue(env, &funv->v);
      } break;

      invalidDefaultCase;
    }
  }

  if (global_debug_mode)
    breakhere;
  Value *last = 0;
  Ast *last_ast = sequence->items[sequence->count-1];
  if (Fork *fork = castAst(last_ast, Fork))
    last = evaluateFork(arena, env, fork);
  else
    last = evaluateAndNormalize(arena, env, last_ast);

  Value *out = 0;
  if (last)
  {
    if (rewrite_chain)
    {
      RewriteV *last_rewrite = rewrite_chain->first;
      last_rewrite->body = last;

      RewriteChain *chain = rewrite_chain;
      Value *debug_previous_type = 0;
      while (true)
      {
        RewriteV *rewrite = chain->first;
        auto [lhs, rhs] = getEqualitySides(rewrite->eq_proof->type);
        Value *rewrite_to   = rewrite->right_to_left ? rhs : lhs;
        if (debug_previous_type)
        {
          assert(equalB32(debug_previous_type, rewrite->body->type));
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
        Value *type = rewriteExpression(arena, rewrite_to, rewrite->path, rewrite->body->type);

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

forward_declare internal Value *
normalize(MemoryArena *arena, Environment *env, Value *in0) 
{
  debug_normalization_depth++;
  // NOTE: I'm kinda convinced that this is only gonna be a best-effort
  // thing. Handling all cases is a waste of time.
  //
  // TODO there are infinite loops when we rewrite f.ex: "(E: a = b) -> False" => "a != 0".
  Value *out0 = {};

  b32 debug = false;
  if (debug && global_debug_mode)
  {
    debugIndent(); dump("normalize: "); dump(in0); dump();
  }

  switch (in0->cat)
  {
    case VC_CompositeV:
    {
      CompositeV *in = castValue(in0, CompositeV);

      Value **norm_args = pushArray(arena, in->arg_count, Value*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Value *in_arg = in->args[arg_id];
        norm_args[arg_id] = normalize(arena, env, in_arg);
      }

      Value *norm_op = normalize(arena, env, in->op);
      if (norm_op->cat == VC_FunctionV)
      {// Function application
        FunctionV *funv = castValue(norm_op, FunctionV);
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
        assert((norm_op->cat == VC_BuiltinEqual) || (norm_op->cat == VC_Constructor) || (norm_op->cat == VC_StackValue));
#if 1  // special casing for equality
        if (norm_op->cat == VC_BuiltinEqual)
        {// special case for equality
          Value *lhs = norm_args[1];
          Value *rhs = norm_args[2];
          Trinary compare = equalTrinary(lhs, rhs);
#if 0
          if (compare == Trinary_True)
            out0 = &builtins.True->v;
#endif
          // I don't know how to handle inconsistency otherwise
          if (compare == Trinary_False)
            out0 = &builtins.False->v;
        }
#endif
      }

      if (!out0)
      {
        CompositeV *out = newValue(arena, CompositeV, in->type);
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->v;
      }
      assert(out0->cat);
    } break;

    case VC_RewriteV:
    {
      RewriteV *in   = castValue(in0, RewriteV);
      Value *body     = normalize(arena, env, in->body);
      Value *eq_proof = normalize(arena, env, in->eq_proof);
      if ((body != in->body) || (eq_proof != in->eq_proof))
      {
        RewriteV *out = copyStruct(arena, in);
        out->eq_proof = eq_proof;
        out->body     = body;
        out0 = &out->v;
      }
      else
        out0 = in0;
    } break;

    // todo #speed most of these don't need rewriting.
    case VC_Null:
    case VC_Hole:
    case VC_ArrowV:
    case VC_Constructor:
    case VC_BuiltinSet:
    case VC_BuiltinType:
    case VC_BuiltinEqual:
    case VC_FunctionV:
    case VC_StackValue:
    case VC_Union:
    case VC_HeapValue:
    case VC_ComputationV:
    case VC_AccessorV:
    {
      out0 = in0;
    } break;
  }

  Value *before_rewrite = out0;
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
        Value *norm_stack_value = normalize(arena, env, stack->items[in->id]);
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

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      Composite *out = copyStruct(arena, in);
      out->op   = replaceFreeVars(arena, env, in->op, stack_offset);
      out->args = pushArray(arena, in->arg_count, Ast*);
      for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        out->args[arg_id] = replaceFreeVars(arena, env, in->args[arg_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      stack_offset++;
      out->output_type    = replaceFreeVars(arena, env, in->output_type, stack_offset);
      out->param_types = pushArray(arena, in->param_count, Ast*);
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        out->param_types[param_id] = replaceFreeVars(arena, env, in->param_types[param_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = replaceFreeVars(arena, env, in->record, stack_offset);
      out0 = &out->a;
    } break;

    case AC_Rewrite:
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

inline b32 hasFreeVars(Environment *env, Ast *in0, s32 stack_offset)
{
  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      s32 stack_delta = in->stack_delta - stack_offset;
      if (stack_delta >= 0)
      {
        Stack *stack = env->stack;
        for (s32 delta = 0; delta < stack_delta; delta++)
          stack = stack->outer;
        if (in->id >= stack->count)
        {
          dump(env->stack);
          invalidCodePath;
        }
        return true;
      }
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      if (hasFreeVars(env, in->op, stack_offset))
        return true;
      for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        if (hasFreeVars(env, in->args[arg_id], stack_offset))
          return true;
      }
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      if (hasFreeVars(env, in->output_type, stack_offset+1))
        return true;
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        if (hasFreeVars(env, in->param_types[param_id], stack_offset+1))
          return true;
      }
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      return hasFreeVars(env, in->record, stack_offset);
    } break;

    case AC_Constant:
    {
      return false;
    } break;

    case AC_Rewrite:
    case AC_Let:
    case AC_FunctionDecl:
    case AC_Sequence:
    case AC_Fork:
    {
      todoIncomplete;
    } break;

    invalidDefaultCase;
  }
  return false;
}

inline b32
isGlobalValue(Value *value)
{
  switch (value->cat)
  {
    case VC_Hole:
    case VC_StackValue:
    case VC_HeapValue:
    {
      return false;
    } break;

    case VC_CompositeV:
    {
      CompositeV *composite = castValue(value, CompositeV);
      if (!isGlobalValue(composite->op))
        return false;

      for (int id=0; id < composite->arg_count; id++)
      {
        if (!isGlobalValue(composite->args[id]))
          return false;
      }

      return true;
    } break;

    case VC_ArrowV:
    case VC_FunctionV:
    {
      return false;  // TODO: don't know what to do so let's just say false for now.
    } break;

    case VC_Null:
    case VC_BuiltinSet:
    case VC_BuiltinType:
    case VC_BuiltinEqual:
    case VC_Union:
    case VC_Constructor:
    {
      return true;
    } break;

    case VC_AccessorV:
    case VC_RewriteV:
    case VC_ComputationV:
    {
      invalidCodePath;
      return false;
    } break;
  }
}

forward_declare internal Value *
evaluate(MemoryArena *arena, Environment *env, Ast *in0)
{
  Value *out0;

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
      {
        out0 = stack->items[in->id];
      }
      else
      {
        dump(env->stack);
        invalidCodePath;
      }
    } break;

    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = in->value;
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      Value **norm_args = pushArray(arena, in->arg_count, Value*);
      for (int arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        Value *arg = evaluate(arena, env, in_arg);
        norm_args[arg_id] = arg;
      }

      Value *norm_op = evaluate(arena, env, in->op);
      ArrowV *signature = castValue(norm_op->type, ArrowV);
      extendStack(env, in->arg_count, norm_args);
      Value *return_type = evaluate(arena, env, signature->output_type);
      if (return_type == (Value *)0x1000A7F1A)
        assert(false);
      unwindStack(env);
      CompositeV *out = newValue(arena, CompositeV, return_type);
      out->arg_count = in->arg_count;
      out->op        = norm_op;
      out->args      = norm_args;
#if 0
      if (should_normalize)
      {
        // NOTE: the legendary eval-reduce loop
        return normalize(arena, env, &out->v);
      }
      else
        out0 = &out->v;
#else
      out0 = &out->v;
#endif
    } break;

    case AC_Arrow:
    {
      // Arrow  *in  = castAst(in0, Arrow);
      ArrowV *out = newValue(arena, ArrowV, &builtins.Type->v);
      out->stack_depth = getStackDepth(env->stack);
      Arrow *replaced = castAst(replaceFreeVars(arena, env, in0, 0), Arrow);
      out->arrow = *replaced;
      out0 = &out->v;
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      Value *record0 = evaluate(arena, env, in->record);
      // note: it has to be a record, otw we wouldn't know what type to
      // return.
      CompositeV *record = castValue(record0, CompositeV);
      out0 = record->args[in->field_id];
    } break;

    case AC_Computation:
    {
      Computation  *computation = castAst(in0, Computation);
      Value *lhs = evaluate(arena, env, computation->lhs);
      Value *rhs = evaluate(arena, env, computation->rhs);

      // TODO: the "tactics" code proliferates too much
      CompositeV *eq = newValue(arena, CompositeV, &builtins.Set->v);
      eq->op        = &builtins.equal->v;
      eq->arg_count = 3;
      allocateArray(arena, eq->arg_count, eq->args);
      eq->args[0] = lhs->type;
      eq->args[1] = lhs;
      eq->args[2] = rhs;

      ComputationV *out = newValue(arena, ComputationV, &eq->v);
      out->lhs = lhs;
      out->rhs = rhs;
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

forward_declare internal Value *
evaluateAndNormalize(MemoryArena *arena, Environment *env, Ast *in0)
{
  Value *eval = evaluate(arena, env, in0);
  Value *norm = normalize(arena, env, eval);
  return norm;
}

internal Value *
evaluate(MemoryArena *arena, Ast *in0)
{
  Environment env = {};
  return evaluate(arena, &env, in0);
}

inline b32
normalized(Environment *env, Value *in)
{
  Value *norm = normalize(temp_arena, env, in);
  return equalB32(in, norm);
}

inline b32
addLocalBinding(Environment *env, Token *key)
{
  auto lookup = lookupCurrentFrame(env->bindings, key->string, true);
  b32 succeed = false;
  if (lookup.found)
    parseError(key, "reused parameter name");
  else
  {
    succeed = true;
    lookup.slot->value = env->bindings->count++;
  }
  return succeed;
}

inline Constructor *
getSoleConstructor(Value *type)
{
  if (Union *uni = castValue(type, Union))
  {
    if (uni->ctor_count == 1)
      // sole constructor
      return uni->ctors + 0;
  }
  return 0;
}

inline Value *
introduceOnHeap(Environment *env, Value *parent, Constructor *ctor)
{
  // todo: I think we don't need "base_name" anymore, b/c we can walk from the root.
  Value *out = 0;
  if (ArrowV *ctor_sig = castValue(ctor->type, ArrowV))
  {
    s32 param_count = ctor_sig->param_count;
    Value *record_type = evaluate(temp_arena, env, ctor_sig->output_type);
    CompositeV *record = newValue(temp_arena, CompositeV, record_type);
    record->op        = &ctor->v;
    record->arg_count = param_count;
    Environment sig_env = *env;
    {
      Environment *env = &sig_env;  // important: we need the env to evaluate field types
      addStackFrame(env);
      for (s32 field_id=0; field_id < param_count; field_id++)
      {
        String field_name = ctor_sig->param_names[field_id].string;

        Value *member_type = evaluate(temp_arena, env, ctor_sig->param_types[field_id]);
        AccessorV *accessor = newValue(temp_arena, AccessorV, member_type);
        accessor->record     = parent;
        accessor->field_id   = field_id;
        accessor->field_name = field_name;
        if (Constructor *field_ctor = getSoleConstructor(member_type))
        {
          // recursive case
          Value *intro = introduceOnHeap(env, &accessor->v, field_ctor);
          addStackValue(env, intro);
        }
        else
        {
          HeapValue *value = newValue(temp_arena, HeapValue, member_type);
          value->accessor = *accessor;
          addStackValue(env, &value->v);
        }
      }
      record->args = env->stack->items;
      out = &record->v;
    }
  }
  else
  {// rare case: weird type with single enum
    assert(ctor->type->cat == VC_Union);
    out = &ctor->v;
  }
  return out;
}

forward_declare inline void
introduceOnStack(Environment *env, Token *name, Ast *type)
{
  Value *typev = evaluate(temp_arena, env, type);
  Value *intro;

  StackValue *ref = newValue(temp_arena, StackValue, typev);
  ref->name        = *name;
  ref->id          = env->stack->count;  // :stack-ref-id-has-significance
  ref->stack_depth = env->stack->depth;

  if (Constructor *type_ctor = getSoleConstructor(typev))
  {
    intro = introduceOnHeap(env, &ref->v, type_ctor);
  }
  else intro = &ref->v;

  addStackValue(env, intro);
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

inline Value *
lookupBuiltinGlobalName(char *name)
{
  Token token = newToken(name);
  GlobalBinding *slot = lookupGlobalName(&token);
  assert(slot->count == 1);
  return slot->items[0];
}

inline void
addGlobalBinding(Token *token, Value *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(token->string, true);
  // TODO: check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));
}

inline void
addBuiltinGlobalBinding(char *key, Value *value)
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
requireCategory(TokenCategory tc, char *message, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    if (nextToken(tk).cat == tc)
      out = true;
    else
      tokenError(message);
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
addRewriteRule(Environment *env, Value *lhs0, Value *rhs0)
{
  b32 added = false;
  if (!equalB32(lhs0, rhs0))
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
getExplicitParamCount(Arrow *in)
{
  s32 out = 0;
  for (s32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!paramImplied(in, param_id))
      out++;
  }
  return out;
}

inline s32
getExplicitParamCount(ArrowV *in)
{
  s32 out = 0;
  for (s32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!paramImplied(in, param_id))
      out++;
  }
  return out;
}

inline b32
matchType(Environment *env, Value *actual, Value *expected)
{
  if (expected == holev)
    return true;
  else
  {
    Value *norm_actual   = normalize(temp_arena, env, actual);
    Value *norm_expected = normalize(temp_arena, env, expected);
    return equalB32(norm_actual, norm_expected);
  }
}

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

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      Composite *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, out->arg_count, out->args);
      for (s32 id=0; id < in->arg_count; id++)
      {
        out->args[id] = deepCopy(arena, in->args[id]);
      }
      out0 = &out->a;
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
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

    case AC_Rewrite:
    {
      Rewrite *in = castAst(in0, Rewrite);
      Rewrite *out = copyStruct(arena, in);
      out->eq_proof = deepCopy(arena, in->eq_proof);
      out0 = &out->a;
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->a;
    } break;

    invalidDefaultCase;
  }
  return out0;
}

inline ValueArray
getGlobalOverloads(Environment *env, Identifier *ident, Value *expected_type)
{
  ValueArray out = {};
  if (!lookupLocalName(env, &ident->token))
  {
    if (GlobalBinding *slot = lookupGlobalName(&ident->token))
    {
      if (isGlobalValue(expected_type))
      {
        allocateArray(temp_arena, slot->count, out.items);
        for (int slot_id=0; slot_id < slot->count; slot_id++)
        {
          ArrowV *signature = castValue(slot->items[slot_id]->type, ArrowV);
          b32 output_type_mismatch = false;
          addStackFrame(env);
          env->stack->count = signature->param_count;
          if (!hasFreeVars(env, signature->output_type, 0))
          {
            Value *output_type = evaluate(temp_arena, env, signature->output_type);
            if (!equalB32(output_type, expected_type))
              output_type_mismatch = true;
          }
          unwindStack(env);

          if (!output_type_mismatch)
          {
            out.items[out.count++] = slot->items[slot_id];
          }
        }
      }
      else
      {
        out.count = slot->count;
        out.items = (Value **)slot->items;
      }
    }
  }
  return out;
}

internal FunctionV *
buildFunction(MemoryArena *arena, Environment *env, FunctionDecl *fun)
{
  // TODO: we adjust the binding here, which is kinda yikes but what are ya
  // gonna do, that's what you do to support recursion.
  FunctionV *funv = 0;

  if (Expression signature = buildExpression(arena, env, &fun->signature->a, holev))
  {
    // note: store the built signature, maybe to display it later.
    fun->signature = castAst(signature.ast, Arrow);
    funv = newValue(arena, FunctionV, signature.value);
    // note: we only need that funv there for the type.
    funv->a.token = fun->a.token;
    funv->body    = &dummy_function_under_construction;

    // note: add binding first to support recursion
    b32 is_local = (bool)env->bindings;
    if (is_local)
    {// local context
      addLocalBinding(env, &fun->a.token);
      addStackValue(env, &funv->v);
    }
    else
    {// global context
      addGlobalBinding(&fun->a.token, &funv->v);
    }

    if (noError())
    {
      addStackFrame(env);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < fun->signature->param_count; id++)
      {
        Token *name = fun->signature->param_names+id;
        introduceOnStack(env, name, fun->signature->param_types[id]);
        addLocalBinding(env, name);
      }
      assert(noError());

      Value *expected_body_type = evaluate(temp_arena, env, fun->signature->output_type);
      buildSequence(arena, env, fun->body, expected_body_type);
      unwindBindingsAndStack(env);
    }

    funv->function = *fun;
    funv->stack    = env->stack;
  }
  return funv;
}

internal Ast *
valueToAst(MemoryArena *arena, Environment *env, Value* value)
{
  Ast *out;
  Token token = newToken("<synthetic>");
  switch (value->cat)
  {
    case VC_CompositeV:
    {
      CompositeV *compositev = castValue(value, CompositeV);
      Composite  *composite  = newAst(arena, Composite, &token);
      composite->op        = valueToAst(arena, env, compositev->op);
      composite->arg_count = compositev->arg_count;
      allocateArray(arena, composite->arg_count, composite->args);
      for (int id=0; id < composite->arg_count; id++)
      {
        composite->args[id] = valueToAst(arena, env, compositev->args[id]);
      }
      out = &composite->a;
    } break;

    case VC_StackValue:
    {
      StackValue *ref = castValue(value, StackValue);
      Variable   *var = newAst(arena, Variable, &ref->name);
      out = &var->a;
      var->stack_delta = env->stack->depth - ref->stack_depth;
      var->id          = ref->id;  // :stack-ref-id-has-significance
    } break;

    case VC_HeapValue:
    {
      HeapValue *heap_value = castValue(value, HeapValue);
      out = valueToAst(arena, env, &heap_value->accessor.v);
    } break;

    case VC_AccessorV:
    {
      AccessorV *accessorv = castValue(value, AccessorV);
      Accessor  *accessor  = newAst(arena, Accessor, &token);
      accessor->record      = valueToAst(arena, env, accessorv->record);
      accessor->field_id    = accessorv->field_id;
      accessor->field_name  = newToken(accessorv->field_name);
      out = &accessor->a;
    } break;

    case VC_ArrowV:
    {
      ArrowV *arrowv = castValue(value, ArrowV);
      out = &arrowv->arrow.a;
    } break;

    case VC_BuiltinEqual:
    case VC_BuiltinSet:
    case VC_BuiltinType:
    case VC_Union:
    case VC_FunctionV:
    case VC_Constructor:
    {
      Constant *synthetic = newSyntheticConstant(arena, value);
      out = &synthetic->a;
    } break;

    case VC_RewriteV:
    {
      dump(); dump("-------------------"); dump(value);
      todoIncomplete;  // really we don't need it tho?
    } break;

    default:
    {
      todoIncomplete;
      out = 0;
    }
  }

  return out;
}
 
internal SearchOutput
searchExpression(MemoryArena *arena, Value *lhs, Value* in0)
{
  SearchOutput out = {};
  if (equalB32(in0, lhs))
  {
    out.found = true;
    return out;
  }
  else
  {
    switch (in0->cat)
    {
      case VC_CompositeV:
      {
        CompositeV *in = castValue(in0, CompositeV);
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

      case VC_Null:
      case VC_Hole:
      case VC_ComputationV:
      case VC_StackValue:
      case VC_HeapValue:
      case VC_BuiltinEqual:
      case VC_BuiltinSet:
      case VC_BuiltinType:
      case VC_Union:
      case VC_FunctionV:
      case VC_Constructor:
      {} break;

      case VC_ArrowV:
      case VC_RewriteV:  // probably we never work on proofs in this way?
      {
        todoIncomplete;
      } break;

      case VC_AccessorV:
      {
        invalidCodePath;
      } break;
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
    Token token = newToken("<norm inserted by fork>");
    list->first = &newAst(arena, Rewrite, &token)->a;
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
    if (token.cat == TC_KeywordRewrite)
    {
      Rewrite *rewrite = newAst(arena, Rewrite, &token);

      rewrite->right_to_left = false;
      Token next = peekToken();
      if (equal(next, "<-"))
      {
        nextToken();
        rewrite->right_to_left = true;
      }

      rewrite->eq_proof = parseExpressionToAst(arena);
      ast = &rewrite->a;
    }
    else if (token.cat == TC_StrongArrow)
    {
      pushContext("Full-rewrite: => TO_EXPRESSION [{ EQ_PROOF }]");
      Rewrite *rewrite = newAst(arena, Rewrite, &token);
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
    }
    else if (isIdentifier(&token))
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
              requireChar(';');
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
        ast = &newAst(arena, Computation, &token)->a;
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

internal Value *
subExpressionAtPath(Value *in, TreePath *path)
{
  if (path)
  {
    switch (in->cat)
    {
      case VC_CompositeV:
      {
        CompositeV *composite = castValue(in, CompositeV);
        Value *arg = composite->args[path->first];
        return subExpressionAtPath(arg, path->next); 
      } break;

      invalidDefaultCase;
    }
  }
  else
    return in;
}

internal b32
unify(Value **values, Value *lhs, Value *rhs)
{
  b32 success = false;
  b32 debug_print = false;
  if (debug_print)
  {
    debugIndent(); dump("unify: "); dump(lhs); dump(" with "); dump(rhs); dump();
  }
  switch (lhs->cat)
  {
    case VC_StackValue:
    {
      StackValue *stack_value = castValue(lhs, StackValue);
      if (Value *replaced = values[stack_value->id])
      {
        if (equalB32(replaced, rhs))
          success = true;
      }
      else if (equalB32(lhs->type, rhs->type))
      {
        values[stack_value->id] = rhs;
        success = true;
      }
    } break;

    case VC_CompositeV:
    {
      CompositeV *lhs_composite = castValue(lhs, CompositeV);
      if (CompositeV *rhs_composite = castValue(rhs, CompositeV))
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
      success = equalB32(lhs, rhs);
    } break;
  }
  if (debug_print)
  {
    debugDedent(); dump("=> "); if (success) dump("true"); else dump("false"); dump();
  }
  return success;
}

forward_declare internal void
buildSequence(MemoryArena *arena, Environment *env, Sequence *sequence, Value *goal)
{
  Environment *outer_env = env; env = outer_env;

  for (s32 item_id = 0;
       (item_id < sequence->count-1) && noError();
       item_id++)
  {
    Ast *item = sequence->items[item_id];
    switch (item->cat)
    {
      case AC_Let:
      {
        Let   *let = castAst(item, Let);
        Value *let_type = 0;
        if (Expression rhs = buildExpression(arena, env, let->rhs, holev))
        {
          if (let->type)
          {
            if (Expression type = buildExpression(arena, env, let->type, holev))
            {
              if (matchType(env, rhs.value->type, type.value))
              {
                let_type = type.value;
              }
              else
              {
                parseError(item, "the rhs does not have the expected type");
                attach("got", rhs.value->type);
                attach("expected", type.value);
              }
            }
          }

          if (noError())
          {
            addLocalBinding(env, &let->lhs);
            let->rhs = rhs.ast;
            Value *value;
            if (let_type)
            {// type manipulation
              value = copyStruct(temp_arena, rhs.value);
              value->type = let_type;
            }
            else
              value = rhs.value;
            addStackValue(env, value);
          }
        }
      } break;

      case AC_FunctionDecl:
      {// NOTE: common builder for both local and global function.
        buildFunction(arena, env, castAst(item, FunctionDecl));
      } break;

      case AC_Rewrite:
      {
        Rewrite *rewrite = castAst(item, Rewrite);
        if (!rewrite->eq_proof)
        {// just normalize
          Value *new_goal = 0;
          if (!rewrite->to_expression)
          {
            new_goal = normalize(arena, env, goal);
            rewrite->to_expression = valueToAst(arena, env, new_goal);
          }
          else if (Expression build = buildExpression(arena, env, rewrite->to_expression, holev))
          {
            rewrite->to_expression = build.ast;
            new_goal               = build.value;
          }

          if (noError())
          {
            if (equalB32(new_goal, goal))
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
              Value *new_goal_norm = normalize(arena, env, new_goal);
              Value *goal_norm = normalize(arena, env, goal);
              if (equalB32(new_goal_norm, goal_norm))
              {
                Computation *computation = newAst(arena, Computation, &item->token);
                computation->lhs = valueToAst(arena, env, goal);
                computation->rhs = valueToAst(arena, env, new_goal);
                rewrite->eq_proof = &computation->a;
                goal = new_goal;
              }
              else
              {
                parseError(item, "new goal does not match original");
                equalB32(new_goal_norm, goal_norm);
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
            Value *expected_result = to_expression.value;
            CompareExpressions compare = compareExpressions(arena, goal, expected_result);
            if (compare.result == Trinary_True)
              parseError(item, "new goal same as current goal");
            else
            {
              rewrite->path = compare.diff_path;
              Value *from = subExpressionAtPath(goal, compare.diff_path);
              Value *to   = subExpressionAtPath(to_expression.value, compare.diff_path);

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
                Value *hint = 0;
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
                  Value *eq_proof = 0;
                  if (ArrowV *arrowv = castValue(hint->type, ArrowV))
                  {
                    addStackFrame(env);
                    for (int id=0; id < arrowv->param_count; id++)
                    {
                      Token *name = arrowv->param_names+id;
                      introduceOnStack(env, name, arrowv->param_types[id]);
                    }
                    Value *output_type = evaluate(temp_arena, env, arrowv->output_type);
                    unwindStack(env);

                    CompositeV *eq = newValue(temp_arena, CompositeV, &builtins.Set->v);
                    eq->op        = &builtins.equal->v;
                    eq->arg_count = 3;
                    allocateArray(temp_arena, 3, eq->args);
                    eq->args[0]   = from->type;
                    eq->args[1]   = from;
                    eq->args[2]   = to;

                    Value **values = pushArray(temp_arena, arrowv->param_count, Value *, true);
                    if (unify(values, output_type, &eq->v))
                    {
                      // todo: make a standalone typecheck function, to check type of these things
                      CompositeV *eq_proofc = newValue(arena, CompositeV, &eq->v);
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
                      attach("goal", goal);
                    }
                  }
                  else if (CompositeV *composite = castValue(hint->type, CompositeV))
                  {
                    if (composite->op == &builtins.equal->v)
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
                    if (CompositeV *eq = castValue(eq_proof->type, CompositeV))
                    {
                      if (eq->op == &builtins.equal->v)
                      {
                        Value *from, *to;
                        if (rewrite->right_to_left) {from = eq->args[2]; to = eq->args[1];}
                        else                        {from = eq->args[1]; to = eq->args[2];}
                        Value *actual_result = rewriteExpression(arena, to, rewrite->path, goal);
                        if (equalB32(actual_result, expected_result))
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
            if (CompositeV *eq = castValue(eq_proof.value->type, CompositeV))
            {
              if (eq->op == &builtins.equal->v)
              {
                Value *from, *to;
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
    {
      buildFork(arena, env, fork, goal);
    }
    else if (Computation *computation = castAst(last, Computation))
    {
      b32 goal_valid = false;
      if (CompositeV *eq = castValue(goal, CompositeV))
      {
        if (eq->op == &builtins.equal->v)
        {
          goal_valid = true;
          Value *lhs = normalize(temp_arena, env, eq->args[1]);
          Value *rhs = normalize(temp_arena, env, eq->args[2]);
          if (equalB32(lhs, rhs))
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
}

forward_declare internal void
buildFork(MemoryArena *arena, Environment *env, Fork *fork, Value *expected_type)
{
  assert(expected_type);
  if (Expression subject = buildExpression(arena, env, fork->subject, holev))
  {
    fork->subject = subject.ast;
    s32 case_count = fork->case_count;

    if (Union *uni = castValue(subject.value->type, Union))
    {
      if (uni->ctor_count == case_count)
      {
        Sequence **correct_bodies = pushArray(arena, case_count, Sequence *, true);
        Value *subjectv = subject.value;
        Environment *outer_env = env;

        for (s32 input_case_id = 0;
             input_case_id < case_count && noError();
             input_case_id++)
        {
          Environment env = *outer_env;
          Token *ctor_token = &fork->parsing->ctors[input_case_id].token;

          if (GlobalBinding *lookup = lookupGlobalName(ctor_token))
          {
            Constructor *ctor = 0;
            b32 ctor_is_atomic = true;
            for (s32 lookup_id=0;
                 lookup_id < lookup->count && !ctor;
                 lookup_id++)
            {// trying to find the intended constructor of this type, from
              // the global pool of values.
              if (Constructor *candidate = castValue(lookup->items[lookup_id], Constructor))
              {
                if (equalB32(candidate->type, subject.value->type)) 
                {
                  ctor = candidate;
                }
                else
                {// NOTE: rn we DON'T support the weird inductive proposition thingie.
                  if (ArrowV *ctor_sig = castValue(candidate->type, ArrowV))
                  {
                    if (Constant *constant = castAst(ctor_sig->output_type, Constant))
                    {
                      if (equalB32(constant->value, subject.value->type))
                      {
                        ctor_is_atomic = false;
                        ctor = candidate;
                      }
                    }
                  }
                }
              }
            }

            if (ctor)
            {
              if (ctor_is_atomic)
              {
                addRewriteRule(&env, subjectv, &ctor->v);
              }
              else
              {
                Value *record = introduceOnHeap(&env, subjectv, ctor);
                addRewriteRule(&env, subjectv, record);
              }

              if (noError())
              {
                if (correct_bodies[ctor->id])
                {
                  parseError(&fork->bodies[input_case_id]->a, "fork case handled twice");
                  attach("constructor", &ctor->v);
                }
                else
                {
                  buildSequence(arena, &env, fork->bodies[input_case_id], expected_type);
                  correct_bodies[ctor->id] = fork->bodies[input_case_id];
                }
              }
            }
            else
            {
              parseError(ctor_token, "expected a constructor");
              // for (ctor->)
            }
          }
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

forward_declare internal Expression
buildExpression(MemoryArena *arena, Environment *env, Ast *in0, Value *expected_type)
{
  // todo #mem: we just put everything in the arena, including scope values.
  // todo #speed: normalizing expected_type.
  // beware: Usually we mutate in-place, but we may also allocate anew.
  Expression out = {};
  assert(expected_type);
  b32 should_check_type = (expected_type != holev);

  switch (in0->cat) check_switch(expression)
  {
    case AC_Hole:
    {
      // Holes are awesome, flexible placeholders that you can feed to the
      // typechecker to get what you want
      if (matchType(env, expected_type, &builtins.True->v))
      {
        Constant *constant = newSyntheticConstant(arena, &builtins.truth->v, &in0->token);
        return buildExpression(arena, env, &constant->a, expected_type);
      }

      if (CompositeV *eq = castValue(expected_type, CompositeV))
      {
        if (eq->op->cat == VC_BuiltinEqual)
        {
          if (equalB32(normalize(temp_arena, env, eq->args[1]),
                       normalize(temp_arena, env, eq->args[2])))
          {
            Composite *refl = newAst(arena, Composite, &in0->token);
            allocateArray(arena, 1, refl->args);
            refl->op        = &newSyntheticConstant(arena, &builtins.refl->v, &in0->token)->a;
            refl->arg_count = 1;
            refl->args[0]   = valueToAst(arena, env, eq->args[1]);
            return buildExpression(arena, env, &refl->a, expected_type);
          }
        }
      }

      parseError(in0, "proof in progress");
      attach("expected type", expected_type);
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

        Value *value = 0;
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (s32 value_id = 0; value_id < globals->count; value_id++)
          {
            Value *slot_value = globals->items[value_id];
            if (matchType(env, slot_value->type, expected_type))
            {
              if (value)
              {// ambiguous
                if (global_debug_mode)
                  breakhere;
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
            attach("expected_type", normalize(temp_arena, env, expected_type));
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

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      b32 has_multiple_overloads;
      if (Identifier *op_ident = castAst(in->op, Identifier))
      {
        ValueArray global_overloads = getGlobalOverloads(env, op_ident, expected_type);
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

            Composite *in_copy = castAst(deepCopy(arena, in0), Composite);
            in_copy->op        = &constant->a;
            out = buildExpression(arena, env, &in_copy->a, expected_type);

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
        if (Expression op = buildExpression(arena, env, in->op, holev))
        {
          in->op = op.ast;

          if (ArrowV *signature = castValue(op.value->type, ArrowV))
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
                  if (paramImplied(signature, param_id))
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
              Environment signature_env = *env;
              addStackFrame(&signature_env);
              for (int arg_id = 0;
                   (arg_id < in->arg_count) && noError();
                   arg_id++)
              {
                // Typecheck & Inference for the arguments. TODO: the hole stuff
                // is kinda hard-coded only for the equality.
                if (in->args[arg_id]->cat == AC_Hole)
                  addStackValue(&signature_env, holev);
                else
                {
                  Ast *param_type0 = signature->param_types[arg_id];
                  Value *expected_arg_type = evaluate(temp_arena, &signature_env, param_type0);
                  if (Expression arg = buildExpression(arena, env, in->args[arg_id], expected_arg_type))
                  {
                    in->args[arg_id] = arg.ast;
                    addStackValue(&signature_env, arg.value);
                    if (expected_arg_type == holev)
                    {
                      Variable *param_type = castAst(param_type0, Variable);
                      assert(param_type->stack_delta == 0);
                      signature_env.stack->items[param_type->id] = arg.value->type;

                      // write back to the input ast.
                      Ast *synthetic0;
                      switch (arg.value->type->cat)
                      {
                        // todo: #incomplete we need a full-fledged "Value to Ast"
                        // function. HOWEVER that still wouldn't work for
                        // heap-introduced values.
                        case VC_StackValue:
                        {
                          StackValue *ref = castValue(arg.value->type, StackValue);
                          Variable *synthetic = newAst(arena, Variable, &ref->name);
                          synthetic0 = &synthetic->a;
                          synthetic->stack_delta = env->stack->depth - ref->stack_depth;
                          synthetic->id          = ref->id;  // :stack-ref-id-has-significance
                        } break;

                        case VC_BuiltinSet:
                        case VC_BuiltinType:
                        case VC_Union:
                        {
                          Constant *synthetic = newSyntheticConstant(arena, arg.value->type);
                          synthetic0 = &synthetic->a;
                        } break;

                        default:
                          todoIncomplete;
                      }
                      in->args[param_type->id] = synthetic0;
                    }
                  }
                }
              }

              for (s32 arg_id = 0;
                   arg_id < in->arg_count && noError();
                   arg_id++)
              {
                if (in->args[arg_id]->cat == AC_Hole)
                  parseError(in0, "Cannot fill hole in expression");
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

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);

      addStackFrame(env);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < in->param_count && noError(); id++)
      {
        Ast *param_type = buildExpression(arena, env, in->param_types[id], holev).ast;
        if (param_type)
        {
          in->param_types[id] = param_type;
          Token *name = in->param_names+id;
          introduceOnStack(env, name, param_type);
          addLocalBinding(env, name);
        }
      }

      if (noError())
      {
        in->output_type = buildExpression(arena, env, in->output_type, holev).ast;
      }
      unwindBindingsAndStack(env);

      if (noError())
      {
        out.ast   = in0;
        out.value = evaluate(arena, env, in0);
      }
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      if (Expression build_record = buildExpression(arena, env, in->record, holev))
      {
        Ast   *record   = build_record.ast;
        Value *recordv0 = build_record.value;
        if (CompositeV *recordv = castValue(recordv0, CompositeV))
        {
          in->record = record;
          ArrowV *op_type = castValue(recordv->op->type, ArrowV);
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

    invalidDefaultCase;
  }

  if (noError() && should_check_type)
  {// one last typecheck if needed
#if 0
    Value *actual   = normalize(arena, env, out.value->type);
    Value *expected = normalize(arena, env, expected_type);
#else
    Value *actual   = out.value->type;
    Value *expected = expected_type;
#endif
    if (!matchType(env, actual, expected))
    {
      parseError(in0, "actual type differs from expected type");
      attach("got", actual);
      attach("expected", expected);
    }
  }

  if (ParseError *error = getError())
    error->code = ErrorWrongType;

  NULL_WHEN_ERROR(out);
  return out;
}

inline Expression
parseExpression(MemoryArena *arena, LocalBindings *bindings, Value *expected_type)
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
    if (Arrow *signature = castAst(signature0, Arrow))
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
            else if (Composite *pattern = castAst(pattern0, Composite))
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

internal Arrow *
parseArrowType(MemoryArena *arena, b32 is_record)
{
  Arrow *out = 0;

  s32     param_count;
  Token  *param_names;
  Ast   **param_types;
  Token marking_token = peekToken();
  char begin_arg_char = is_record ? '{' : '(';
  char end_arg_char   = is_record ? '}' : ')';
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
    b32 parse_return_type = !is_record;
    if (parse_return_type)
    {
      if (requireCategory(TC_Arrow, "syntax: (param: type, ...) -> ReturnType"))
      {
        if (Ast *return_type = parseExpressionToAst(arena))
        {
          out = newAst(arena, Arrow, &marking_token);
          out->output_type = return_type;
          out->param_count = param_count;
          out->param_names = param_names;
          out->param_types = param_types;
        }
      }
    }
    else
    {
      out = newAst(arena, Arrow, &marking_token);
      out->output_type = 0;
      out->param_count = param_count;
      out->param_names = param_names;
      out->param_types = param_types;
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
        Composite *branch = newAst(arena, Composite, &op->token);
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
  {
    if (eatUntilMatchingPair(tk))
    {
      out = nextToken(tk).cat == TC_Arrow;
    }
  }

  return out;
}

internal Ast *
parseExpressionToAstMain(MemoryArena *arena, ParseExpressionOptions opt)
{
  Ast *out = 0;
  if (seesArrowExpression())
  {
    out = &parseArrowType(arena, false)->a;
  }
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
          Accessor *new_operand = newAst(arena, Accessor, &op_token);
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

              Composite *new_operand = newAst(arena, Composite, &op_token);
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
parseUnionCase(MemoryArena *arena, Union *uni)
{
  s32 ctor_id = uni->ctor_count++;
  Constructor *out = uni->ctors + ctor_id;
  Token tag = nextToken();
  if (isIdentifier(&tag))
  {
    if (optionalChar(':'))
    {// constructor with custom type (not sure if we need it)
      if (Ast *parsed_type = parseExpressionFull(arena).ast)
      {
        Value *norm_type0 = evaluate(arena, parsed_type);
        initValue(&out->v, VC_Constructor, norm_type0);
        b32 valid_type = false;
        if (Union *type = castValue(norm_type0, Union))
        {
          if (type == uni)
            valid_type = true;
        }
        else if (ArrowV *type = castValue(norm_type0, ArrowV))
        {
          if (getFormOf(type->output_type) == uni)
            valid_type = true;
        }

        if (valid_type)
        {
          out->name = tag;
          out->id   = ctor_id;
        }
        else
        {
          parseError(parsed_type, "invalid type for constructor");
          attach("type", parsed_type);
        }
      }
    }
    else
    {// constructor as a sole tag
      if (uni->type == &builtins.Set->v)
      {
        initValue(&out->v, VC_Constructor, &uni->v);
        out->name = tag;
        out->id   = ctor_id;
      }
      else
        parseError(&tag, "constructors must construct a set member");
    }

    if (noError())
      addGlobalBinding(&tag, &out->v);
  }
  else
    tokenError("expected an identifier as constructor name");
}

internal void
parseUnion(MemoryArena *arena, Token *name)
{
  // NOTE: the type is in scope of its own constructor.
  Value *type = &builtins.Set->v;
  if (optionalChar(':'))
  {// type override
    b32 valid_type = false;
    if (Expression type_parsing = parseExpressionFull(arena))
    {
      Value *norm_type = evaluate(arena, type_parsing.ast);
      if (ArrowV *arrow = castValue(norm_type, ArrowV))
      {
        if (Constant *return_type = castAst(arrow->output_type, Constant))
          if (return_type->value == &builtins.Set->v)
            valid_type = true;
      }
      else if (norm_type == &builtins.Set->v)
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
    Union *uni = newValue(arena, Union, type);
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
            parseUnionCase(arena, uni);
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
            breakhere;
          }
        }
      }
      else if (equal(token, "print"))
      {
        if (Expression expr = parseExpressionFull(temp_arena))
        {
#if 1
          Value *norm = normalize(arena, empty_env, expr.value);
          print(0, norm, {.detailed=true});
#else
          Value *norm = normalize(arena, empty_env, expr.value);
          dump("type before norm:"); dump(expr.value->type); dump();
          dump("type after norm:");  dump(norm->type); dump();
          print(0, norm->type, {.detailed=true});
#endif
          print(0, "\n");
        }
        requireChar(';');
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
        requireChar(';');
      }
      else if (equal(token, "print_debug"))
      {
        if (Ast *exp = parseExpression(temp_arena))
        {
          char *output = print(temp_arena, exp, {.detailed=true, .print_type=true});
          printf("%s\n", output);
        }
        requireChar(';');
      }
      else if (equal(token, "check"))
      {
        Value *expected_type = 0;
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
        requireChar(';');
      }
      else if (equal(token, "check_truth"))
      {
        if (Value *goal = parseExpressionFull(temp_arena).value)
        {
          if (CompositeV *eq = castValue(goal, CompositeV))
          {
            b32 goal_valid = false;
            if (eq->op == &builtins.equal->v)
            {
              goal_valid = true;
              Value *lhs = normalize(temp_arena, empty_env, eq->args[1]);
              Value *rhs = normalize(temp_arena, empty_env, eq->args[2]);
              if (!equalB32(lhs, rhs))
              {
                parseError(&token, "equality cannot be proven by computation");
                Value *lhs = normalize(temp_arena, empty_env, eq->args[1]);
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
            if (Ast *value = parseExpression(arena))
            {
              Value *norm = evaluate(arena, value);
              addGlobalBinding(&token, norm);
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
                Value *type = evaluate(arena, parse_type.ast);
                if (Expression parse_value = parseExpression(arena, 0, type))
                {
                  Value *value = evaluate(arena, parse_value.ast);
                  addGlobalBinding(&token, value);
                  requireChar(';');
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

    Tokenizer  tk_ = newTokenizer(arena, input_path.directory, read.content);
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
      printf("%s:%d:%d: [%s] %s",
             input_path.path,

             error->line,
             error->column,

             error->context ? error->context : "",
             error->message.base);

      if (error->attachment_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attachment_count;
             attached_id++)
        {
          auto attachment = error->attachments[attached_id];
          printf("%s: ", attachment.string);
          switch (attachment.type)
          {
            case AttachmentType_Ast:
            {
              print(0, (Ast*)attachment.p, {});
            } break;

            case AttachmentType_Value:
            {
              print(0, (Value*)attachment.p, {});
            } break;

            case AttachmentType_Token:
            {
              Token *token = (Token*)attachment.p;
              print(0, token->string);
            } break;

            case AttachmentType_TypeMatcher:
            {
              Matcher *matcher = (Matcher *)attachment.p;
              switch (matcher->cat)
              {
                case MC_Unknown:
                {
                  print(0, "<any type>");
                };

                case MC_Exact:
                {
                  print(0, matcher->Exact, {});
                } break;

                case MC_OutType:
                {
                  printf("? -> ");
                  print(0, matcher->OutType, {});
                } break;
              }
            } break;
          }
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
  Tokenizer tk = newTokenizer(temp_arena, String{}, 0);
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
  EngineState *state = pushStruct(arena, EngineState);
  state->arena = arena;

  {
    global_bindings = pushStruct(arena, GlobalBindings);  // :global-bindings-zero-at-startup

    builtins = {};
    {// Type and Set
      // Token superset_name = newToken("Type");
      builtins.Type = newValue(arena, BuiltinType, 0);
      builtins.Type->type = &builtins.Type->v; // NOTE: circular types, might bite us
      addBuiltinGlobalBinding("Type", &builtins.Type->v);

      builtins.Set = newValue(arena, BuiltinSet, &builtins.Type->v);
      addBuiltinGlobalBinding("Set", &builtins.Set->v);
    }

    {// more builtins
#if 1
      Tokenizer builtin_tk = newTokenizer(arena, print(temp_arena, "<builtin>"), 0);
      global_tokenizer = &builtin_tk;
      builtin_tk.at = "(_A: Set, a, b: _A) -> Set";
      Expression equal_type = parseExpressionFull(arena);
      builtins.equal = newValue(arena, BuiltinEqual, equal_type.value);
      addBuiltinGlobalBinding("=", &builtins.equal->v);

      builtin_tk.at = "(_A: Set, x: _A) -> =(_A, x, x)";
      Expression refl_type = parseExpressionFull(arena);
      builtins.refl = newValue(arena, Constructor, refl_type.value);
      builtins.refl->name = newToken("refl");
      addBuiltinGlobalBinding("refl", &builtins.refl->v);

      EngineState builtin_engine_state = EngineState{.arena=arena};
      builtin_tk.at = "True :: union { truth }";
      parseTopLevel(&builtin_engine_state);
      builtins.True  = castValue(lookupBuiltinGlobalName("True"), Union);
      builtins.truth = castValue(lookupBuiltinGlobalName("truth"), Constructor);
      builtin_tk.at = "False :: union { }";
      parseTopLevel(&builtin_engine_state);
      builtins.False = castValue(lookupBuiltinGlobalName("False"), Union);

#else
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), false);
      assert(success);
      Value *equal_type = lookupBuiltinGlobalName("equal_type");
      builtins.equal = newValue(arena, BuiltinEqual, equal_type);
      builtins.True  = castValue(lookupBuiltinGlobalName("True"), Union);
      builtins.truth = castValue(lookupBuiltinGlobalName("truth"), Constructor);
      builtins.False = castValue(lookupBuiltinGlobalName("False"), Union);
      addBuiltinGlobalBinding("=", builtins.equal);
#endif
    }
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
  resetZeroArena(permanent_arena);
#endif

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/test.rea"))
    success = false;
  resetZeroArena(permanent_arena);
#endif

  return success;
}

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_globals.h"
#include <stdint.h>

global_variable b32 global_debug_mode;

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
myprint(RewriteRule *rewrite)
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
myprint(Value *in0)
{
  print(0, in0, {});
}

inline void
myprint(Ast *in0)
{
  print(0, in0, {});
}

inline void
myprint(Stack *stack)
{
  myprint("[");
  while (stack)
  {
    myprint("[");
    for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
    {
      myprint(stack->args[arg_id]);
      if (arg_id != stack->count-1)
        myprint(", ");
    }
    myprint("]");
    stack = stack->outer;
    if (stack)
      myprint(", ");
  }
  myprint("]");
}

inline void
myprint(Environment *env)
{
  myprint("stack: ");
  myprint(env->stack);
  myprint(", rewrites: ");
  myprint(env->rewrite);
}

s32 global_variable debug_indentation;
inline void
debugIndent()
{
  debug_indentation++;
  for (s32 id = 0; id < debug_indentation; id++)
    myprint(" ");
}

inline void
debugDedent()
{
  for (s32 id = 0; id < debug_indentation; id++)
    myprint(" ");
  debug_indentation--;
}

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

inline b32
paramImplied(Arrow *arrow, s32 param_id)
{
  return arrow->param_names[param_id].text.chars[0] == '_';
}

inline b32
paramImplied(ArrowV *arrow, s32 param_id)
{
  return arrow->param_names[param_id].text.chars[0] == '_';
}

// prints both Composite and CompositeV
inline void
printComposite(MemoryArena *buffer, void *in0, b32 is_value, PrintOptions opt)
{
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
    else
      arg_count = in->arg_count;
  }

  void **args;
  if (op_type)
  {// print out unignored args only
    args = pushArray(temp_arena, op_type->param_count, void*);
    arg_count = 0;
    for (s32 param_id = 0; param_id < op_type->param_count; param_id++)
    {
      if (!paramImplied(op_type, param_id))
      {
        args[arg_count++] = raw_args[param_id];
      }
    }
  }
  else
    args = raw_args;

  if (arg_count == 2)
  {// special path for infix operator
    print(buffer, "(");
    print(buffer, args[0], is_value, opt);
    print(buffer, " ");
    print(buffer, op, is_value, opt);
    print(buffer, " ");
    print(buffer, args[1], is_value, opt);
    print(buffer, ")");
  }
  else
  {// normal pre path
    print(buffer, op, is_value, opt);
    print(buffer, "(");
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {
      print(buffer, args[arg_id], is_value, opt);
      if (arg_id < arg_count-1)
        print(buffer, ", ");
    }
    print(buffer, ")");
  }
}

forward_declare internal char *
print(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0 == dummy_hole)
  {
    print(buffer, "_");
  }
  else if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
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
        print(buffer, in->a.token);
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
        print(buffer, "rewrite ");
        print(buffer, in->proof, new_opt);
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
        print(buffer, " {");
        Union *form = in->uni;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          Constructor *subset = form->ctors + ctor_id;
          switch (subset->v.type->cat)
          {// print pattern
            case VC_Union:
            {
              print(buffer, &subset->v, new_opt);
            } break;

            case VC_ArrowV:
            {
              print(buffer, &subset->v, new_opt);
              print(buffer, " ");
              ArrowV *signature = castValue(subset->v.type, ArrowV);
              for (s32 param_id = 0; param_id < signature->param_count; param_id++)
              {
                print(buffer, " ");
              }
            } break;

            default:
              invalidCodePath;
          }

          print(buffer, ": ");
          print(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != form->ctor_count-1)
            print(buffer, ", ");
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

        print(buffer, in->out_type, new_opt);
      } break;

      case AC_Accessor:
      {
        Accessor *in = castAst(in0, Accessor);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->member);
      } break;

      default:
      {
        print(buffer, "<unimplemented category: %u>", in0->cat);
        invalidCodePath;
      } break;
    }
  }
  else
    print(buffer, "<null>");
  return out;
}

forward_declare internal char *
print(MemoryArena *buffer, Value *in0, PrintOptions opt)
{
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
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

          if (opt.print_type)
          {
            print(buffer, ": ");
            print(buffer, in->v.type, new_opt);
          }

          if (in->ctor_count)
          {
            print(buffer, " {");
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Constructor *subset = in->ctors + ctor_id;
              print(buffer, subset->name);
              print(buffer, ": ");
              print(buffer, subset->v.type, new_opt);
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
          print(buffer, " { ");
          print(buffer, in->body, new_opt);
          print(buffer, " }");
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

      case VC_AccessorV:
      {
        AccessorV *in = castValue(in0, AccessorV);
        print(buffer, &in->record->v, new_opt);
        print(buffer, ".");
        ArrowV *op_type = castValue(in->record->op->type, ArrowV);
        print(buffer, op_type->param_names[in->param_id]);
      }

      case VC_Constructor:
      {
        Constructor *in = castValue(in0, Constructor);
        print(buffer, in->name);
      } break;

      case VC_HeapValue:
      {
        HeapValue *in = castValue(in0, HeapValue);
        print(buffer, in->name);
      } break;

      default:
      {
        print(buffer, "<unimplemented category: %u>", in0->cat);
        invalidCodePath;
      } break;
    }
  }
  else
    print(buffer, "<null>");
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
  env->stack->args[env->stack->count++] = value;
}

inline void
extendStack(Environment *env, s32 arg_count, Value **args)
{
  assert(arg_count <= arrayCount(env->stack->args));
  addStackFrame(env);
  if (args)
  {
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {// todo: #speed copying values around
      addStackValue(env, args[arg_id]);
    }
  }
}

inline b32
equalB32(Value *lhs, Value *rhs)
{
  return equalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isConstructor(Value *in0)
{
  if (CompositeV *in = castValue(in0, CompositeV))
    return in->op->cat == VC_Constructor;
  else
    return false;
}

internal Trinary
compareExpressionList(Value **lhs_list, Value **rhs_list, s32 count)
{
  Trinary out = Trinary_Unknown;
  b32 mismatch_found = false;
  b32 unknown_found  = false;
  for (s32 id = 0;
       (id < count) && !mismatch_found;
       id++)
  {
    auto lhs = lhs_list[id];
    auto rhs = rhs_list[id];
    auto compare = equalTrinary(lhs, rhs);
    if (compare == Trinary_Unknown)
      unknown_found = true;
    if (compare == Trinary_False)
      mismatch_found = true;
  }
  if (mismatch_found)
    out = Trinary_False;
  else if (unknown_found)
    out = Trinary_Unknown;   
  else
    out = Trinary_True;

  return out;
}

internal Trinary
equalTrinary(Value *lhs0, Value *rhs0)
{
#if 0
  if (global_debug_mode)
  {
    myprint("comparing: ");
    myprint(&lhs0->a);
    myprint(" and ");
    myprint(&rhs0->a);
    myprint();
  }
#endif

  Trinary out = Trinary_Unknown;

  if (!lhs0 | !rhs0)
    out = Trinary_False;
  else if (lhs0 == rhs0)
    out = Trinary_True;
  else if (lhs0->cat == rhs0->cat)
  {
    switch (lhs0->cat)
    {
      case VC_StackValue:
      {
        StackValue* lhs = castValue(lhs0, StackValue);
        StackValue* rhs = castValue(rhs0, StackValue);
        if ((lhs->stack_depth == rhs->stack_depth) && (lhs->id == rhs->id))
          out = Trinary_True;
      } break;

      case VC_ArrowV:
      {
        ArrowV* lhs = castValue(lhs0, ArrowV);
        ArrowV* rhs = castValue(rhs0, ArrowV);

        s32 param_count = lhs->param_count;
        if (rhs->param_count == param_count)
        {
          Environment env = newEnvironment(temp_arena);
          addStackFrame(&env);
          env.stack->depth = maximum(lhs->stack_depth, rhs->stack_depth)+1;
          // todo: maybe add negative affirmation 
          b32 type_mismatch = false;
          for (s32 id = 0; id < param_count; id++)
          {
            if (equalB32(evaluate(&env, lhs->param_types[id]),
                         evaluate(&env, rhs->param_types[id])))
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
            out = equalTrinary(evaluate(&env, lhs->out_type),
                               evaluate(&env, rhs->out_type));
          }
        }
        else
          out = Trinary_False;
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
          out = Trinary_False;
        }
        else if (op_compare == Trinary_True)
        {
          s32 count = lhs->arg_count;
          assert(lhs->arg_count == rhs->arg_count);
          out = compareExpressionList((lhs->args), (rhs->args), count);
        }
      } break;

      case VC_FunctionV:
      {// we can compare the types to eliminate negatives, but we don't care.
      } break;

      case VC_Constructor:
      {
        Constructor *lhs = castValue(lhs0, Constructor);
        Constructor *rhs = castValue(rhs0, Constructor);
        assert(lhs->v.type == rhs->v.type);
        out = (Trinary)(lhs->id == rhs->id);
      } break;

      case VC_AccessorV:
      {
        AccessorV *lhs = castValue(lhs0, AccessorV);
        AccessorV *rhs = castValue(rhs0, AccessorV);
        // NOTE: would loop forever if we did this
        // if (identicalB32(&lhs->record->v, &rhs->record->v))
        if (lhs->record == rhs->record)
          if (lhs->param_id == rhs->param_id)
            out = Trinary_True;
      } break;

      case VC_BuiltinEqual:
      case VC_BuiltinType:
      case VC_BuiltinSet:
      {
        out = Trinary_True;
      } break;

      case VC_HeapValue:
      case VC_Union:
      case VC_Null:
      {
        out = Trinary_Unknown;
      } break;
    }
  }
  else if (((lhs0->cat == VC_Constructor) && isConstructor(rhs0)) ||
           ((rhs0->cat == VC_Constructor) && isConstructor(lhs0)))
  {
    out = Trinary_False;
  }

  return out;
}

global_variable GlobalBindings *global_bindings;

internal GlobalBinding *
lookupGlobalNameSlot(String key)
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
        slot->next_hash_slot = pushStruct(permanent_arena, GlobalBinding, true);
        slot = slot->next_hash_slot;
        slot->key = key;
        break;
      }
    }
  }
  else
    slot->key = key;

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
rewriteExpression(Environment *env, Value *in)
{
  Value *out = 0;
  // todo: find some way to early out in case expression can't be rewritten
  // if (canBeRewritten(in))
  // todo: #speed this is O(n)
  for (RewriteRule *rewrite = env->rewrite;
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
normalize(Environment env, Value *in0) 
{
  // NOTE: I'm kinda convinced that this is only gonna be a best-effort
  // thing. Handling all cases is a waste of time.
  //
  // todo #speed don't pass the Environment in wholesale?
  Value *out0 = {};
  MemoryArena *arena = env.arena;

  if (global_debug_mode)
  {
    debugIndent();
    myprint("normalize: ");
    myprint(in0);
    myprint();
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
        norm_args[arg_id] = normalize(env, in_arg);
      }

      Value *norm_op = normalize(env, in->op);
      if (norm_op->cat == VC_FunctionV)
      {// Function application
        FunctionV *funv = castValue(norm_op, FunctionV);
        if (funv->body != &dummy_function_under_construction)
        {
          extendStack(&env, in->arg_count, norm_args);
          // note: evaluation might fail, in which case we back out.
          out0 = evaluateMain(&env, funv->body, true);
          unwindStack(&env);
        }
      }
      else
      {
        if (norm_op == builtins.equal)
        {// special case for equality
          Value *lhs = norm_args[1];
          Value *rhs = norm_args[2];
          Trinary compare = equalTrinary(lhs, rhs);
          if (compare == Trinary_True)
            out0 = &builtins.True->v;
          else if (compare == Trinary_False)
            out0 = &builtins.False->v;
        }
        else
          assert((norm_op->cat == VC_Constructor) ||
                 (norm_op->cat == VC_StackValue));
      }

      if (!out0)
      {
        CompositeV *out = newValue(env.arena, CompositeV, in->v.type);
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->v;
      }
      assert(out0->cat);
    } break;

    case VC_AccessorV:
    {
      AccessorV *in = castValue(in0, AccessorV);
      out0 = in->record->args[in->param_id];
    } break;

    // todo #speed most of these don't need rewriting.
    case VC_ArrowV:
    case VC_Constructor:
    case VC_BuiltinSet:
    case VC_BuiltinType:
    case VC_BuiltinEqual:
    case VC_FunctionV:
    case VC_StackValue:
    case VC_Union:
    case VC_HeapValue:
    {
      out0 = in0;
    } break;

    invalidDefaultCase;
  }

  if (out0)
  {
    Value *before_rewrite = out0;
    out0 = rewriteExpression(&env, out0);
    if (out0 != before_rewrite)
      out0 = normalize(env, out0); // normalize again, because there might
                                   // be new information not present at the time
                                   // the rewrite rule was added (f.ex the op
                                   // might be expanded now)
  }

  if (global_debug_mode)
  {
    debugDedent();
    myprint("=> ");
    myprint(out0);
    myprint();
  }

  return out0;
}

internal Value *
normalize(MemoryArena *arena, Value *in0)
{
  return normalize(newEnvironment(arena), in0);
}

inline Ast *
replaceFreeVars(Environment *env, Ast *in0, s32 stack_offset)
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
          myprint(env->stack);
          invalidCodePath;
        }
        Value *norm_stack_value = normalize(*env, stack->args[in->id]);
        Constant *out = newSyntheticConstant(env->arena, norm_stack_value);
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
      Composite *out = copyStruct(env->arena, in);
      out->op   = replaceFreeVars(env, in->op, stack_offset);
      out->args = pushArray(env->arena, in->arg_count, Ast*);
      for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        out->args[arg_id] = replaceFreeVars(env, in->args[arg_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      Arrow *out = copyStruct(env->arena, in);
      stack_offset++;
      out->out_type    = replaceFreeVars(env, in->out_type, stack_offset);
      out->param_types = pushArray(env->arena, in->param_count, Ast*);
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        out->param_types[param_id] = replaceFreeVars(env, in->param_types[param_id], stack_offset);
      }
      out0 = &out->a;
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      Accessor *out = copyStruct(env->arena, in);
      out->record = replaceFreeVars(env, in->record, stack_offset);
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

inline b32
hasFreeVars(Environment *env, Ast *in0, s32 stack_offset)
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
          myprint(env->stack);
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
      stack_offset++;
      if (hasFreeVars(env, in->out_type, stack_offset))
        return true;
      for (s32 param_id = 0; param_id < in->param_count; param_id++)
      {
        if (hasFreeVars(env, in->param_types[param_id], stack_offset))
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

forward_declare internal Value *
evaluateMain(Environment *env, Ast *in0, b32 expect_failure)
{
  // this function may fail due to a fork that cannot continue, or the caller
  // expects some arrow type to not have any dependency on its parameters
  Value *out0 = 0;
  MemoryArena *arena = env->arena;

  if (global_debug_mode)
  {
    debugIndent();
    myprint("evaluate: ");
    myprint(in0);
    myprint();
  }

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
        out0 = stack->args[in->id];
      }
      else
      {
        myprint(env->stack);
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
      b32 failed = false;
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        if (Value *arg = evaluateMain(env, in_arg, expect_failure))
          norm_args[arg_id] = arg;
        else
        {
          failed = true;
          break;
        }
      }

      if (!failed)
      {
        if (Value *norm_op = evaluateMain(env, in->op, expect_failure))
        {
          ArrowV *signature = castValue(norm_op->type, ArrowV);
          extendStack(env, in->arg_count, norm_args);
          if (Value *return_type = evaluateMain(env, signature->out_type, expect_failure))
          {
            unwindStack(env);
            CompositeV *out = newValue(arena, CompositeV, return_type);
            out->arg_count = in->arg_count;
            out->op        = norm_op;
            out->args      = norm_args;

            // NOTE: the legendary eval-reduce loop
            out0 = normalize(*env, &out->v);
          }
        }
      }
    } break;

    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      if (Value *subject = evaluateMain(env, in->subject, expect_failure))
      {
        switch (subject->cat)
        {// note: we fail if the fork is undetermined
          case VC_Constructor:
          {
            Constructor *ctor = castValue(subject, Constructor);
            out0 = evaluateMain(env, in->bodies[ctor->id], expect_failure);
          } break;

          case VC_CompositeV:
          {
            CompositeV *record = castValue(subject, CompositeV);
            if (Constructor *ctor = castValue(record->op, Constructor))
            {
              out0 = evaluateMain(env, in->bodies[ctor->id], expect_failure);
            }
          } break;

          default:
            out0 = 0;
        }
      }
    } break;

    case AC_Arrow:
    {
      // Arrow  *in  = castAst(in0, Arrow);
      ArrowV *out = newValue(arena, ArrowV, builtins.Type);
      out->stack_depth = getStackDepth(env->stack);
      Arrow *replaced = castAst(replaceFreeVars(env, in0, 0), Arrow);
      out->arrow = *replaced;
      out0 = &out->v;
    } break;

    case AC_Sequence:
    {
      Environment  env_ = *env; Environment *env  = &env_;
      Sequence *in = castAst(in0, Sequence);
      b32 failed = false;
      for (s32 id = 0;  (id < in->count-1) && !failed;  id++)
      {
        Ast *item0 = in->items[id];
        switch (item0->cat)
        {// todo: this has to be inline because we pass env by value. Might
         // actually be cleaner, but we need to sync with "buildExpession".
          case AC_Rewrite:
          {} break;

          case AC_Let:
          {
            Let *item = castAst(item0, Let);
            if (Value *rhs = evaluateMain(env, item->rhs, expect_failure))
              addStackValue(env, rhs);
            else
              failed = true;
          } break;

          case AC_FunctionDecl:
          {
            FunctionDecl  *item        = castAst(item0, FunctionDecl);
            if (Value *signature_v = evaluateMain(env, &item->signature->a, expect_failure))
            {
              FunctionV *funv = newValue(arena, FunctionV, signature_v);
              funv->function = *item;
              funv->stack    = env->stack;
              addStackValue(env, &funv->v);
            }
            else
              failed = true;
          } break;

          // todo screen the input
          invalidDefaultCase;
        }
      }
      if (!failed)
        out0 = evaluateMain(env, in->items[in->count-1], expect_failure);
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      if (Value *record0 = evaluateMain(env, in->record, expect_failure))
      {
        // note: it has to be a record, otw we wouldn't know what type to
        // return.
        CompositeV *record = castValue(record0, CompositeV);
        out0 = record->args[in->param_id];
      }
    } break;

    case AC_FunctionDecl:
    {
      FunctionDecl *in = castAst(in0, FunctionDecl);
      if (Value *signature = evaluateMain(env, &in->signature->a, expect_failure))
      {
        FunctionV *out = newValue(env->arena, FunctionV, signature);
        out->function = *in;
        out->stack    = env->stack;
      }
    }
    break;

    invalidDefaultCase;
  }

  if (global_debug_mode)
  {
    debugDedent();
    myprint("=> ");
    myprint(out0);
    myprint();
  }

  if (out0)
    out0 = normalize(*env, out0);
  else
    assert(expect_failure);

  return out0;
}

forward_declare internal Value *
evaluate(Environment *env, Ast *in0)
{
  return evaluateMain(env, in0, false);
}

internal Value *
evaluate(MemoryArena *arena, Ast *in0)
{
  Environment env = newEnvironment(arena);
  return evaluate(&env, in0);
}

inline b32
normalized(Environment env, Value *in)
{
  Value *norm = normalize(env, in);
  return equalB32(in, norm);
}

inline b32
addLocalBinding(LocalBindings *bindings, Token *key)
{
  auto lookup = lookupCurrentFrame(bindings, key->text, true);
  b32 succeed = false;
  if (lookup.found)
    parseError(key, "reused parameter name");
  else
  {
    succeed = true;
    lookup.slot->value = bindings->count++;
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
introduceOnHeap(Environment *env, String base_name, Constructor *ctor)
{
  Value *out = 0;
  if (Arrow *ctor_sig = toArrow(ctor->v.type))
  {
    s32 param_count = ctor_sig->param_count;
    Value *record_type = evaluate(env, ctor_sig->out_type);
    CompositeV *record = newValue(temp_arena, CompositeV, record_type);
    record->op        = &ctor->v;
    record->arg_count = param_count;
    Environment sig_env = *env;
    {
      Environment *env = &sig_env;
      addStackFrame(env);
      for (s32 field_id=0; field_id < param_count; field_id++)
      {
        size_t original_used = temp_arena->used;
        char *field_name_chars = print(temp_arena, base_name);
        print(temp_arena, ".");
        print(temp_arena, ctor_sig->param_names[field_id]);
        // todo: hack to get the string length back, so clunky.
        String field_name = String{field_name_chars, (s32)(temp_arena->used - original_used)};

        Value *field_type = evaluate(env, ctor_sig->param_types[field_id]);
        if (Constructor *field_ctor = getSoleConstructor(field_type))
        {
          Value *intro = introduceOnHeap(env, field_name, field_ctor);
          addStackValue(env, intro);
        }
        else
        {
          HeapValue *value = newValue(temp_arena, HeapValue, field_type);
          value->name = field_name;
          addStackValue(env, &value->v);
        }
      }
      record->args = env->stack->args;
      out = &record->v;
    }
  }
  else
  {// rare case: weird type with single enum
    assert(ctor->v.type->cat == VC_Union);
    out = &ctor->v;
  }
  return out;
}

forward_declare
inline void
introduceOnStack(Environment *env, Token *name, Ast *type)
{
  Value *typev = evaluate(env, type);
  Value *intro;
  if (Constructor *type_ctor = getSoleConstructor(typev))
  {
    intro = introduceOnHeap(env, name->text, type_ctor);
  }
  else
  {
    StackValue *ref    = newValue(temp_arena, StackValue, typev);
    ref->name        = *name;
    ref->id          = env->stack->count;  // :stack-ref-id-has-significance
    ref->stack_depth = env->stack->depth;
    intro = &ref->v;
  }
  addStackValue(env, intro);

  if (env->bindings)
    addLocalBinding(env->bindings, name);
}

inline GlobalBinding *
lookupGlobalName(Token *token)
{
  GlobalBinding *slot = lookupGlobalNameSlot(token->text);
  if (slot->count == 0)
  {
    // note: assume that if the code gets here, then the identifier isn't in
    // local scope either.
    parseError(token, "identifier not found");
    return 0;
  }
  else
    return slot;
}

inline Value *
lookupBuiltinGlobalName(char *name)
{
  Token token = newToken(name);
  GlobalBinding *slot = lookupGlobalName(&token);
  assert(slot->count == 1);
  return slot->values[0];
}

inline void
addGlobalBinding(Token *token, Value *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(token->text);
  // nocheckin: check for type conflict
  slot->values[slot->count++] = value;
  assert(slot->count < arrayCount(slot->values));
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
    LookupCurrentFrame lookup = lookupCurrentFrame(bindings, token->text, false);
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
    reason = "<no reason provided>";
  if (hasMore(tk))
  {
    Token token = nextToken(tk);
    if (token.text.length == 1 && token.text.chars[0] == c)
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

internal void
addRewrite(Environment *env, Value *lhs0, Value *rhs0)
{
#if REA_DIAGNOSTICS
  assert(normalized(*env, lhs0));
  assert(normalized(*env, rhs0));
#endif
  if (!equalB32(lhs0, rhs0))
  {
    b32 added = false;

    if (CompositeV *lhs = castValue(lhs0, CompositeV))
      if (CompositeV *rhs = castValue(rhs0, CompositeV))
    {
      if ((lhs->op->cat == VC_Union) &&
          (rhs->op->cat == VC_Union))
      {
        assert(equalB32((lhs->op), (rhs->op)));
        for (s32 arg_id = 0; lhs->arg_count; arg_id++)
          addRewrite(env, (lhs->args[arg_id]), (rhs->args[arg_id]));
        added = true;
      }
    }

    if (!added)
    {
      RewriteRule *rewrite = newRewrite(env, lhs0, rhs0);
      env->rewrite = rewrite;
    }

#if 0
    print(0, "added rewrite: ");
    print(0, lhs, {});
    print(0, " -> ");
    print(0, rhs, {});
    printNewline();
#endif
  }
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
matchType(Value *actual, Value *expected)
{
  if (expected == dummy_holev)
    return true;
  else
    return equalB32(actual, expected);
}



#if 0
inline ValueArray
resolveIdentifier(Environment *env, Identifier *in)
{
  // NOTE: this function should return the possible values for an identifier, so
  // the typechecker has something to work with.
  ValueArray out = {};
  Token *name = &in->token;
  LookupLocalName lookup = lookupLocalName(env->bindings, name);
  if (lookup.found)
  {
    Value *norm = evaluate(*env, lookup.ast);
    out.count = 1;
    allocateArray(out.items, out.count);
    out.items[0] = lookup.value;
  }
  else
  {
    Constant *constant = newAst(arena, Constant, name);
    if (Value *value = selectMatchingGlobalValue(env, expected_type, name))
    {
      should_check_type = false;
      constant->value = value;
      out.ast   = &constant->a;
      out.value = constant->value;
    }
  }
  return out;
}
#endif

internal Ast *
deepCopy(MemoryArena *arena, Ast *in0)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_DummyHole:
    case AC_Identifier:
    {
      out0 = in0;
    } break;

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
      out->out_type = deepCopy(arena, in->out_type);
      allocateArray(arena, out->param_count, out->param_types);
      for (s32 id=0; id < in->param_count; id++)
      {
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      }
      out0 = &out->a;
    } break;

    case AC_FunctionDecl:
    {
      FunctionDecl *in = castAst(in0, FunctionDecl);
      FunctionDecl *out = copyStruct(arena, in);
      out->signature = castAst(deepCopy(arena, &in->signature->a), Arrow);
      out->body      = deepCopy(arena, in->body);
      out0 = &out->a;
    } break;

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
      out->proof = deepCopy(arena, in->proof);
      out0 = &out->a;
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->a;
    } break;

    default:
      todoIncomplete;
  }
  return out0;
}

inline GlobalBinding *
getOverloads(Environment *env, Ast *in0)
{
  if (Identifier *in = castAst(in0, Identifier))
  {
    if (lookupLocalName(env, &in->token))
      return 0;
    else if (GlobalBinding *slot = lookupGlobalNameSlot(in->token))
    {
      if (slot->count > 1)
        return slot;
    }
  }
  return 0;
}

forward_declare internal Expression
buildExpression(Environment *env, Ast *in0, Value *expected_type)
{
  // important: env can be modified, if the caller expects it.
  // beware: Usually we mutate in-place, but we may also allocate anew.
  Expression out = {};
  assert(expected_type);
  b32 should_check_type = (expected_type != dummy_holev);
  MemoryArena *arena = env->arena;

  switch (in0->cat)
  {
    case AC_Constant:
    {
      // this case can happen if we retry.
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
        out.value = evaluate(env, out.ast);
      }
      else
      {
        Constant *constant = newAst(arena, Constant, name);

        Value *value = 0;
        Value *norm_expected = normalize(*env, expected_type);
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (s32 value_id = 0; value_id < globals->count; value_id++)
          {
            Value *slot_value = globals->values[value_id];
            // todo: #speed not happy about the repeated normalization within.
            if (matchType(slot_value->type, norm_expected))
            {
              if (value)
              {// ambiguous
                parseError(name, "not enough type information to disambiguate global name");
                break;
              }
              else
                value = slot_value;
            }
          }
          if (!value)
          {
            parseError(name, "found no global matching expected type");
            pushAttachment("expected_type", norm_expected);
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

      if (GlobalBinding *overloads = getOverloads(env, in->op))
      {
        // NOTE: pre-empt operator overloads.
        // play with op.globals to figure out the output type;
        // we'd have to pretty much build, typecheck and evaluate the whole thing.
        // todo #mem
        for (s32 candidate_id=0; candidate_id < overloads->count; candidate_id++)
        {
          Constant *constant = newAst(arena, Constant, &in->op->token);
          constant->value    = overloads->values[candidate_id];

          Composite *in_copy = castAst(deepCopy(arena, in0), Composite);
          in_copy->op = &constant->a;

          // myprint("deep copy: "); myprint(in0); myprint(" => "); myprint(&in_copy->a); myprint();

          out = buildExpression(env, &in_copy->a, expected_type);
          if (out) break;
          else wipeError();
        }
        if (!out)
          parseError(in->op, "there is no suitable function overload");
      }
      else if (Expression op = buildExpression(env, in->op, dummy_holev))
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
                  in->args[param_id] = dummy_hole;
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
              parseError(&in0->token, "argument count does not match the number of explicit parameters (expected %d)", explicit_param_count);
            }
          }

          if (noError())
          {
            Environment signature_env = *env;
            signature_env.arena = temp_arena;
            addStackFrame(&signature_env);
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {// Typecheck/inference for the arguments. todo: the hole stuff is
              // kinda hard-coded only for the equality.
              if (in->args[arg_id] == dummy_hole)
                addStackValue(&signature_env, dummy_holev);
              else
              {
                Ast *param_type0 = signature->param_types[arg_id];
                Value *expected_arg_type = evaluate(&signature_env, param_type0);
                if (Expression arg = buildExpression(env, in->args[arg_id], expected_arg_type))
                {
                  in->args[arg_id] = arg.ast;
                  // bookmark: evaluating the same value here...
                  addStackValue(&signature_env, evaluate(env, arg.ast));
                  if (expected_arg_type == dummy_holev)
                  {
                    Variable *param_type = castAst(param_type0, Variable);
                    assert(param_type->stack_delta == 0);
                    signature_env.stack->args[param_type->id] = arg.value->type;

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
              if (in->args[arg_id] == dummy_hole)
                parseError(in0, "Cannot fill hole in expression");
            }

            if (noError())
            {
              out.ast   = in0;
              out.value = evaluate(env, in0);
            }
          }
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          pushAttachment("got type", op.value->type);
        }
      }
    } break;

    case AC_Sequence:
    {
      // we're gonna change the env.
      // todo #speed add a way to quickly unwind the rewrites?
      Environment *outer_env = env;
      Environment  env       = *outer_env;

      should_check_type = false;
      Sequence *in = castAst(in0, Sequence);
      for (s32 item_id = 0;
           (item_id < in->count-1) && noError();
           item_id++)
      {
        buildExpression(&env, in->items[item_id], dummy_holev);
      }
      if (noError())
      {
        Expression last = buildExpression(&env, in->items[in->count-1], expected_type);
        in->items[in->count-1] = last.ast;

        out.ast   = &in->a;
        out.value = last.value;
      }
    } break;

    case AC_Let:
    {
      Let *in = castAst(in0, Let);
      if (Expression build_rhs = buildExpression(env, in->rhs, dummy_holev))
      {
        addLocalBinding(env->bindings, &in->lhs);
        in->rhs = build_rhs.ast;
        addStackValue(env, evaluate(env, in->rhs));

        out.ast   = in->rhs;
        out.value = build_rhs.value;
      }
    } break;

    case AC_FunctionDecl:
    {// NOTE: common builder for both local and global function.
      FunctionDecl *in = castAst(in0, FunctionDecl);

      char *debug_name = "+";
      if (equal(in->a.token, debug_name))
      {
        // global_debug_mode = true;
        breakhere;
      }

      if (Expression signature = buildExpression(env, &in->signature->a, dummy_holev))
      {
        // note: store the built signature, maybe to display it later.
        in->signature = castAst(signature.ast, Arrow);
        FunctionV *funv = newValue(arena, FunctionV, signature.value);
        // note: we only need that funv there for the type.
        funv->a.token = in->a.token;
        funv->body    = &dummy_function_under_construction;

        // note: add binding first to support recursion
        b32 is_local = (bool)env->bindings;
        if (is_local)
        {// local context
          addLocalBinding(env->bindings, &in->a.token);
          addStackValue(env, &funv->v);
        }
        else
        {// global context
          addGlobalBinding(&in->a.token, &funv->v);
        }

        if (noError())
        {
          addStackFrame(env);
          extendBindings(temp_arena, env);
          for (s32 id=0; id < in->signature->param_count; id++)
          {
            introduceOnStack(env, in->signature->param_names+id, in->signature->param_types[id]);
          }
          assert(noError());

          Value *expected_body_type = evaluate(env, in->signature->out_type);
          in->body = buildExpression(env, in->body, expected_body_type).ast;
          unwindBindingsAndStack(env);
        }

        funv->function = *in;
        funv->stack    = env->stack;

        out.ast   = in0;
        out.value = &funv->v;
      }
    } break;

    case AC_Rewrite:
    {
      Rewrite *in = castAst(in0, Rewrite);
      if (Expression rewrite = buildExpression(env, in->proof, dummy_holev))
      {
        in->proof = rewrite.ast;
        b32 rule_valid = false;
        if (CompositeV *rule = castValue(rewrite.value->type, CompositeV))
        {
          if (rule->op == builtins.equal)
          {
            rule_valid = true;
            if (in->right_to_left)
              addRewrite(env, rule->args[2], rule->args[1]);
            else
              addRewrite(env, rule->args[1], rule->args[2]);
          }
        }
        if (!rule_valid)
        {
          parseError(in0, "invalid rewrite rule, can only be equality");
          pushAttachment("got", rewrite.value->type);
        }
      }

      out.ast   = in0;
      out.value = &builtins.truth->v; // #hack
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);

      addStackFrame(env);
      extendBindings(temp_arena, env);
      for (s32 id=0; id < in->param_count && noError(); id++)
      {
        Ast *param_type = in->param_types[id] = buildExpression(env, in->param_types[id], dummy_holev).ast;
        if (param_type)
          introduceOnStack(env, in->param_names+id, param_type);
      }

      if (noError())
      {
        in->out_type = buildExpression(env, in->out_type, dummy_holev).ast;
      }
      unwindBindingsAndStack(env);

      out.ast   = in0;
      out.value = evaluate(env, in0);
    } break;

    case AC_Fork:
    {
      should_check_type = false;
      Fork *in = castAst(in0, Fork);

      if (Expression subject = buildExpression(env, in->subject, dummy_holev))
      {
        in->subject = subject.ast;
        s32 case_count = in->case_count;

        if (Union *uni = castValue(subject.value->type, Union))
        {
          if (uni->ctor_count == case_count)
          {
            Ast **correct_bodies = pushArray(arena, case_count, Ast *, true);
            Value *subjectv = evaluate(env, in->subject);
            Environment *outer_env = env;

            if (case_count == 0)
            {
              if (!expected_type)
                parseError(in0, "please annotate empty fork with type information");
            }

            Value *common_type = expected_type;
            for (s32 input_case_id = 0;
                 input_case_id < case_count && noError();
                 input_case_id++)
            {
              Environment env = *outer_env;
              // bookmark: here we need to run the ctor token lookup through the
              // type matcher, just like we did in the identifier case (in fact
              // we could make it an identifier, but that'd be redundant I think)
              Token *ctor_token = &in->parsing->ctors[input_case_id].token;

              if (GlobalBinding *lookup = lookupGlobalName(ctor_token))
              {
                Constructor *ctor = 0;
                b32 ctor_is_atomic = true;
                for (s32 lookup_id=0;
                     lookup_id < lookup->count && !ctor;
                     lookup_id++)
                {// trying to find the intended constructor of this type, from
                 // the global pool of values.
                  if (Constructor *candidate = castValue(lookup->values[lookup_id], Constructor))
                  {
                    if (equalB32(candidate->v.type, subject.value->type)) 
                    {
                      ctor = candidate;
                    }
                    else
                    {// NOTE: rn we DON'T support the weird inductive proposition thingie.
                      if (ArrowV *ctor_sig = castValue(candidate->v.type, ArrowV))
                      {
                        if (Constant *constant = castAst(ctor_sig->out_type, Constant))
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
                    addRewrite(&env, subjectv, &ctor->v);
                  }
                  else
                  {
                    Value *record = introduceOnHeap(&env, subject.ast->token, ctor);
                    addRewrite(&env, subjectv, record);
                  }

                  if (noError())
                  {
                    if (correct_bodies[ctor->id])
                    {
                      parseError(in->bodies[input_case_id], "fork case handled twice");
                      pushAttachment("constructor", &ctor->v);
                    }
                    else
                    {
                      Expression body = buildExpression(&env, in->bodies[input_case_id], common_type);
                      correct_bodies[ctor->id] = body.ast;
                      if (common_type == dummy_holev)
                        common_type = body.value->type;
                    }
                  }
                }
                else
                  parseError(ctor_token, "expected a constructor");
              }
            }

            if (noError())
            {
              in->a.cat  = AC_Fork;
              in->uni    = uni;
              in->bodies = correct_bodies;

              out.ast   = in0;
              // nocheckin: explain yourself: well forks aren't expressions, so
              // "buildExpression" would never have to return this.
              out.value = pushStruct(arena, Value);
              out.value->cat  = VC_Null;
              out.value->type = common_type;
            }
          }
          else
            parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                       uni->ctor_count, in->case_count);
        }
        else
        {
          parseError(in->subject, "cannot fork expression of type");
          pushAttachment("type", subject.value->type);
        }
      }
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      if (Expression build_record = buildExpression(env, in->record, dummy_holev))
      {
        Ast   *record   = build_record.ast;
        Value *recordv0 = evaluate(env, record);
        if (CompositeV *recordv = castValue(recordv0, CompositeV))
        {
          in->record = record;
          Arrow *op_type = toArrow(recordv->op->type);
          s32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          for (s32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->member, op_type->param_names[param_id]))
            {
              in->param_id = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
          {
            out.ast   = in0;
            out.value = evaluate(env, in0);
          }
          else
          {
            tokenError(&in->member, "accessor has invalid member");
            pushAttachment("expected a member of constructor", recordv->op);
            pushAttachment("in type", op_type->out_type);
          }
        }
        else
        {
          parseError(record, "cannot access a non-record");
          evaluate(env, record);
          pushAttachment("record", recordv0);
        }
      }
    } break;

    invalidDefaultCase;
  }

  if (noError() && should_check_type)
  {// one last typecheck if needed
    Value *norm_actual   = normalize(*env, out.value->type);
    Value *norm_expected = normalize(*env, expected_type);
    if (!matchType(norm_actual, norm_expected))
    {
      parseError(in0, "actual type differs from expected type");
      pushAttachment("got", norm_actual);
      pushAttachment("expected", norm_expected);
    }
  }

  if (noError())
  {
    assert(out.ast && out.value);
  }
  else
  {
    out.ast   = 0;
    out.value = 0;
  }
  return out;
}

inline Expression
buildExpressionGlobal(MemoryArena *arena, Ast *ast, Value *expected_type=dummy_holev)
{
  Environment env = newEnvironment(arena);
  return buildExpression(&env, ast, expected_type);
}

inline Expression
parseExpression(MemoryArena *arena, LocalBindings *bindings, Value *expected_type)
{
  Expression out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Environment env = newEnvironment(arena);
    env.bindings = bindings;
    if (Expression build = buildExpression(&env, ast, expected_type))
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
  return parseExpression(arena, 0, dummy_holev).ast;
}

inline Expression
parseExpressionFull(MemoryArena *arena)
{
  return parseExpression(arena, 0, dummy_holev);
}

inline Ast *
parseSequence(MemoryArena *arena)
{
  pushContext;
  Token first_token = global_tokenizer->last_token;
  Ast *out0 = 0;
  s32 count = 0;
  AstList *list = 0;
  while (hasMore())
  {
    // todo #speed make a way to rewind the state of the tokenizer
    Tokenizer tk_save = *global_tokenizer;
    Token token = nextToken();
    if (isExpressionEndMarker(&token))
    {
      *global_tokenizer = tk_save;
      break;
    }
    else
    {
      Ast *ast = 0;
      if (Keyword keyword = matchKeyword(&token))
      {
        switch (keyword)
        {
          case Keyword_Rewrite:
          {
            Rewrite *out = newAst(arena, Rewrite, &token);

            out->right_to_left = false;
            Token next = peekToken();
            if (equal(next, "left"))
            {
              nextToken();
              out->right_to_left = true;
            }

            out->proof = parseExpressionToAst(arena);
            ast = &out->a;
          } break;

          default:
          {// falls through to expression parser
          } break;
        }
      }
      else if (isIdentifier(&token))
      {
        Token *name = &token;
        Token after_name = nextToken();
        switch (after_name.cat)
        {
          case TC_DoubleColon:
          {
            pushContextName("function");
            FunctionDecl *fun = parseFunction(arena, name);
            ast = &fun->a;
            popContext();
          } break;

          case TC_ColonEqual:
          {
            pushContextName("let");
            if (Ast *rhs = parseExpressionToAst(arena))
            {
              Let *let = newAst(arena, Let, name);
              ast = &let->a;
              let->lhs = *name;
              let->rhs = rhs;
            }
            popContext();
          } break;

          default: {};
        }
      }

      if (noError() && !ast)
      {
        *global_tokenizer = tk_save;
        ast = parseExpressionToAst(arena);
      }

      if (noError())
      {
        count++;
        AstList *new_list = pushStruct(temp_arena, AstList);
        new_list->first = ast;
        new_list->next  = list;
        list = new_list;
        // f.ex function definitions don't end with ';'
        optionalChar(';');
      }
    }
  }

  if (noError())
  {
    if (count == 0)
      parseError(&first_token, "expected an expression here");
    else
    {
      if (count == 1)
        out0 = list->first;
      else
      {
        Ast **items = pushArray(arena, count, Ast*);
        for (s32 id = count-1; id >= 0; id--)
        {
          items[id] = list->first;
          list = list->next;
        }
        Sequence *out = newAst(arena, Sequence, &first_token);
        out->count = count;
        out->items = items;
        out0 = &out->a;
      }
    }
  }

  popContext();
  return out0;
}

forward_declare
internal FunctionDecl *
parseFunction(MemoryArena *arena, Token *name)
{
  pushContext;
  FunctionDecl *out = newAst(arena, FunctionDecl, name);

  assert(isIdentifier(name));
  char *debug_name = "testLocalVariable";
  if (equal(toString(debug_name), name->text))
    breakhere;

  if (Ast *signature0 = parseExpressionToAst(arena))
  {
    if (Arrow *signature = castAst(signature0, Arrow))
    {
      // NOTE: rebuild the function's local bindings from the signature

      if (requireChar('{', "open function body"))
      {
        if (Ast *body = parseSequence(arena))
        {
          if (requireChar('}'))
          {
            out->body = body;
            out->signature = signature;
          }
        }
      }
    }
    else
      parseError(&signature->a, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  popContext();
  return out;
}

internal Fork *
parseFork(MemoryArena *arena)
{
  pushContext;

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
      Ast **bodies = pushArray(temp_arena, case_count, Ast*);
      allocateArray(temp_arena, case_count, parsing->ctors);

      s32 actual_case_count = 0;
      for (b32 stop = false;
           !stop && noError();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContextName("fork case");
          auto input_case_id = actual_case_count++;
          if (Ast *pattern0 = parseExpressionToAst(temp_arena))
          {
            if (Identifier *ctor = castAst(pattern0, Identifier))
            {
              parsing->ctors[input_case_id]  = *ctor;
            }
            else if (Composite *pattern = castAst(pattern0, Composite))
            {
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
              if (Ast *body = parseSequence(arena))
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
  popContext();

  return out;
}

internal Arrow *
parseArrowType(MemoryArena *arena, b32 is_record)
{
  Arrow *out = 0;
  pushContext;

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
          out->out_type = return_type;
          out->param_count = param_count;
          out->param_names = param_names;
          out->param_types = param_types;
        }
      }
    }
    else
    {
      out = newAst(arena, Arrow, &marking_token);
      out->out_type = 0;
      out->param_count = param_count;
      out->param_names = param_names;
      out->param_types = param_types;
    }
  }

  popContext();
  NULL_WHEN_ERROR(out);
  return out;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  pushContext;

  Ast *out = 0;
  Token token1 = nextToken();
  if (Keyword keyword = matchKeyword(&token1))
  {
    switch (keyword)
    {
      case Keyword_Fork:
      {
        out = &parseFork(arena)->a;
      } break;

      default:
          tokenError("keyword does not constitute an expression");
    }
  }
  else if (isIdentifier(&token1))
  {
    if (equal(&token1, '_'))
      // todo: this doesn't preserve identifier location
      out = dummy_hole;
    else
      out = &(newAst(arena, Identifier, &token1))->a;
  }
  else if (equal(&token1, '('))
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

  if (noError()) {assert(out);} else out = 0;

  popContext();
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
            new_operand->member = member;
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

forward_declare
inline Ast *
parseExpressionToAst(MemoryArena *arena)
{
  return parseExpressionToAstMain(arena, ParseExpressionOptions{});
}

internal void
parseUnionCase(MemoryArena *arena, Union *uni)
{
  pushContext;

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
          if (getFormOf(type->out_type) == uni)
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
          pushAttachment("type", parsed_type);
        }
      }
    }
    else
    {// constructor as a sole tag
      if (uni->v.type == builtins.Set)
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

  popContext();
}

internal void
parseUnion(MemoryArena *arena, Token *name)
{
  pushContext;

  // NOTE: the type is in scope of its own constructor.
  Value *type = builtins.Set;
  if (optionalChar(':'))
  {// type override
    b32 valid_type = false;
    if (Expression type_parsing = parseExpressionFull(arena))
    {
      Value *norm_type = evaluate(arena, type_parsing.ast);
      if (ArrowV *arrow = castValue(norm_type, ArrowV))
      {
        if (Constant *return_type = castAst(arrow->out_type, Constant))
          if (return_type->value == builtins.Set)
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
        pushAttachment("type", norm_type);
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

  popContext();
}

internal void
parseRecord(MemoryArena *arena)
{
  parseArrowType(arena, true);
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  pushContext;
  MemoryArena *arena = state->arena;
  b32 should_fail_active = false;

  while (hasMore())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
#endif

    Token token = nextToken(); 
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
          pushContextName("#load");
          auto file = nextToken();
          if (file.cat != TC_StringLiteral)
            tokenError("expect \"FILENAME\"");
          else
          {
            auto path_buffer = arena;
            char *load_path = print(path_buffer, global_tokenizer->directory);
            print(path_buffer, file.text);
            path_buffer->used++;

            // note: this could be made more efficient but we don't care.
            auto full_path = platformGetFileFullPath(arena, load_path);

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
          }
        } break;

        invalidDefaultCase;
      }
    }
    else
    {
      Keyword keyword = matchKeyword(&token);
      if (keyword)
      {
        switch (keyword)
        {
          case Keyword_Breakhere:
          {
            breakhere;
          } break;

          case Keyword_Print:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              Value *reduced = normalize(temp_arena, evaluate(temp_arena, parsing.ast));
              print(0, reduced, {.detailed=true});
              print(0, ": ");
              print(0, parsing.value->type, {});
              myprint();
            }
            requireChar(';');
          } break;

          case Keyword_PrintRaw:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              print(0, parsing.ast, {.detailed=true});
              print(0, ": ");
              print(0, parsing.value->type, {});
              myprint();
            }
            requireChar(';');
          } break;

          case Keyword_PrintDebug:
          {
            if (Ast *exp = parseExpression(temp_arena))
            {
              char *output = print(temp_arena, exp, {.detailed=true, .print_type=true});
              printf("%s\n", output);
            }
            requireChar(';');
          } break;

          case Keyword_Check:
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
                buildExpressionGlobal(temp_arena, ast, expected_type);
            }
            requireChar(';');
          } break;

          default:
          {
            parseError(&token, "invalid keyword at top-level");
          } break;
        }
      }
      else if (isIdentifier(&token))
      {
        pushContextName("definition");
        Token *name = &token;
        Token after_name = nextToken();
        switch (after_name.cat)
        {
          case TC_ColonEqual:
          {
            pushContextName("constant definition: CONSTANT := VALUE;");
            if (Ast *value = parseExpression(arena))
            {
              Value *norm = evaluate(arena, value);
              addGlobalBinding(name, norm);
              requireChar(';');
            }
          } break;

          case TC_DoubleColon:
          {
            Token after_dcolon = peekToken();
            if (equal(after_dcolon, "union"))
            {
              nextToken();
              parseUnion(arena, name);
            }
            else if (equal(after_dcolon, "record"))
            {
              nextToken();
              parseRecord(arena);
            }
            else if (FunctionDecl *fun = parseFunction(arena, name))
            {
              buildExpressionGlobal(arena, &fun->a);
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
                  addGlobalBinding(name, value);
                  requireChar(';');
                }
              }
            }
          } break;

          default:
          {
            tokenError("unexpected token");
          } break;
        }
        popContext();
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
      else
        wipeError(global_tokenizer);
    }
  }

  popContext();
}

forward_declare
internal b32
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
    if (ParseError error = tk->error)
    {
      success = false;
      printf("%s:%d:%d: [%s] %s",
             input_path.path,

             error->line,
             error->column,

             error->context,
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
              print(0, token->text);
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
      builtins.Type->type = builtins.Type; // NOTE: circular types, might bite us
      addBuiltinGlobalBinding("Type", builtins.Type);

      builtins.Set = newValue(arena, BuiltinSet, builtins.Type);
      addBuiltinGlobalBinding("Set", builtins.Set);
    }

    {// more builtins
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), false);
      assert(success);

      ArrowV *equal_type = castValue(lookupBuiltinGlobalName("equal_type"), ArrowV);
      builtins.equal = newValue(arena, BuiltinEqual, &equal_type->v);
      addBuiltinGlobalBinding("=", builtins.equal);

      builtins.True  = castValue(lookupBuiltinGlobalName("True"), Union);
      builtins.truth = castValue(lookupBuiltinGlobalName("truth"), Constructor);
      builtins.False = castValue(lookupBuiltinGlobalName("False"), Union);
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

// little debug struct
union astdbg
{
  Variable   Variable;
  Constant   Constant;
  Composite  Composite;
  CompositeV CompositeV;
  Fork       Fork;
  Arrow      Arrow;
  ArrowV     ArrowV;
  Union      Form;
  FunctionDecl   Function;
  FunctionV  FunctionV;
  StackValue   StackRef;
  Accessor   Accessor;
  // AccessorV  AccessorV;
};

int
engineMain()
{
  astdbg whatever = {}; (void)whatever;

  int success = true;

#if REA_INTERNAL
  // for printf debugging: when it crashes you can still see the prints
  setvbuf(stdout, NULL, _IONBF, 0);
#endif

  assert(arrayCount(keywords)       == Keywords_Count_);
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

#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_globals.h"
#include "print.cpp"

#define TRANSITION 1

global_variable b32 global_debug_mode;
#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

// Important: all parsing must be aborted when the tokenizer encounters error.

#define VARIABLE_MATCHER(name) \
  b32 name(Environment env, Variable *in, void* opt)

typedef VARIABLE_MATCHER(variable_matcher);

// todo: #speed copying values around
inline void
extendStack(Environment *env, s32 arg_count, Value **args, s32 depth_override=0)
{
  Stack *stack = pushStruct(temp_arena, Stack);
  stack->depth = depth_override ? depth_override : (getStackDepth(env->stack) + 1);
  stack->outer = env->stack;
  assert(arg_count <= arrayCount(stack->args));
  stack->arg_count = arg_count;
  if (args)
  {
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {
      stack->args[arg_id] = args[arg_id];
    }
  }

  env->stack = stack;
}

inline void
myprint(char *str)
{
  printToBuffer(0, str);
}

#if 0
internal b32
searchVariable(Environment env, Ast *in, variable_matcher *matcher, void *opt)
{
  b32 found = false;
  switch (in->cat)
  {
    case AC_Variable:
    {
      Variable *var = castAst(in, Variable);
      found = matcher(env, var, opt);
  } break;

    case AC_Fork:
    {
      Fork *fork = castAst(in, Fork);
      if (searchVariable(env, fork->subject, matcher, opt))
        found = true;
      else
      {
        for (s32 case_id = 0; case_id < fork->case_count; case_id++)
        {
          env.stack_offset++;
          if (searchVariable(env, fork->bodies[case_id], matcher, opt))
          {
            found = true;
            break;
          }
        }
      }
    } break;

    case AC_Composite:
    {
      auto app = castAst(in, Composite);
      if (searchVariable(env, app->op, matcher, opt))
        found = true;
      else
      {
        for (int arg_id = 0; arg_id < app->arg_count; arg_id++)
        {
          if (searchVariable(env, app->args[arg_id], matcher, opt))
          {
            found = true;
            break;
          }
        }
      }
    } break;

    case AC_Arrow:
    {
      auto arrow = castAst(in, Arrow);
      env.stack_offset++;
      if (searchVariable(env, arrow->return_type, matcher, opt))
        found = true;
      else
      {
        for (int param_id = 0;
             param_id < arrow->param_count;
             param_id++)
        {
          // we only wanna search the types, since we probably don't care about
          // the parameters.
          if (searchVariable(env, arrow->param_types[param_id], matcher, opt))
          {
            found = true;
            break;
          }
        }
      }
    }
  }
  return found;
}

VARIABLE_MATCHER(isAnyVariable)
{
  (void) opt; (void) in; (void) env;
  return true;
}

inline b32
hasAnyVariable(Ast *in)
{
  Environment env = newEnvironment(temp_arena);
  return searchVariable(env, in, isAnyVariable, 0);
}
#endif

#if 0
VARIABLE_MATCHER(isFreeVariable)
{
  (void) opt;
  return (in->stack_delta >= env.stack_offset) && (in->stack_depth == 0);
}

inline b32
hasFreeVariable(Ast *in)
{
  Environment env = newEnvironment(temp_arena);
  return searchVariable(env, in, isFreeVariable, 0);
}

VARIABLE_MATCHER(isInstantiatedVariable)
{
  (void) opt; (void) env;
  return in->stack_depth != 0;
}

inline b32
hasInstantiated(Ast *in)
{
  Environment env = newEnvironment(temp_arena);
  return searchVariable(env, in, isInstantiatedVariable, 0);
}

VARIABLE_MATCHER(isDeepVariable)
{
  (void) opt;
  return in->stack_depth > env.stack_depth;
}

inline b32
hasDeepVariable(Environment env, Ast *in)
{
  return searchVariable(env, in, isDeepVariable, 0);
}
#endif

inline b32
identicalB32(Value *lhs, Value *rhs)
{
  return identicalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeForm(Value *in0)
{
  if (Composite *in = castAst(in0, Composite))
    return castAst(in->op, Form) != 0;
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
    auto compare = identicalTrinary(lhs, rhs);
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

internal Value *
normalize(Environment env, Value *in0);

internal Value *
evaluate(Environment env, Ast *in0);

internal Value **
introduce(Environment *env, s32 count, Token *names, Ast **types_ast, s32 depth_override=0)
{
  assert(count < arrayCount(env->stack->args));
  extendStack(env, count, 0, depth_override);
  Value **types = pushArray(temp_arena, count, Value *);
  for (s32 id = 0; id < count; id++)
  {
    types[id] = (evaluate(*env, types_ast[id]));
    StackRef *ref    = newValue(temp_arena, StackRef, names+id, types[id]);
    ref->name        = names[id];
    ref->id          = id;
    ref->stack_depth = env->stack->depth;
    env->stack->args[id] = &ref->v;
  }
  return env->stack->args;
}

internal Value **
introduce(Environment *env, Arrow *signature)
{
  return introduce(env, signature->param_count, signature->param_names, signature->param_types);
}

internal Value **
introduce(Environment *env, ArrowV *signature, s32 depth_override=0)
{
  return introduce(env, signature->a->param_count, signature->a->param_names, signature->a->param_types, depth_override);
}

internal Trinary
identicalTrinary(Value *lhs0, Value *rhs0) // TODO: turn the args into values
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
      case AC_StackRef:
      {
        StackRef* lhs = castAst(lhs0, StackRef);
        StackRef* rhs = castAst(rhs0, StackRef);
        if ((lhs->stack_depth == rhs->stack_depth) && (lhs->id == rhs->id))
          out = Trinary_True;
      } break;

      case AC_Form:
      {
        out = (Trinary)(castAst(lhs0, Form)->ctor_id ==
                        castAst(rhs0, Form)->ctor_id);
      } break;

      case AC_ArrowV:
      {
        ArrowV* lhs = castAst(lhs0, ArrowV);
        ArrowV* rhs = castAst(rhs0, ArrowV);

        s32 param_count = lhs->a->param_count;
        if (rhs->a->param_count == param_count)
        {
          s32 l_depth = getStackDepth(lhs->stack);
          s32 r_depth = getStackDepth(rhs->stack);
          s32 new_depth = maximum(l_depth, r_depth)+1;
          // s32 rl_stack_delta = r_depth - l_depth;
          // s32 l_stack_offset = (rl_stack_delta >= 0) ? rl_stack_delta : 0;
          // s32 r_stack_offset = (rl_stack_delta >= 0) ? 0 : -rl_stack_delta;
          Environment lenv = newEnvironment(temp_arena);
          Environment renv = newEnvironment(temp_arena);
          lenv.stack = lhs->stack;
          renv.stack = rhs->stack;
          introduce(&lenv, lhs, new_depth);
          introduce(&renv, rhs, new_depth);

          Value **lnorm_param_types = pushArray(temp_arena, param_count, Value*);
          Value **rnorm_param_types = pushArray(temp_arena, param_count, Value*);
          for (s32 param_id = 0; param_id < param_count; param_id++)
          {
            lnorm_param_types[param_id] = (evaluate(lenv, lhs->a->param_types[param_id]));
            rnorm_param_types[param_id] = (evaluate(renv, rhs->a->param_types[param_id]));
          }
          Trinary compare_param_types = compareExpressionList(lnorm_param_types, rnorm_param_types, param_count);
          if (compare_param_types == Trinary_False)
          {
            out = Trinary_False;
          }
          else if (compare_param_types == Trinary_True)
          {
            Value *lnorm_return_type = evaluate(lenv, lhs->a->out_type);
            Value *rnorm_return_type = evaluate(renv, rhs->a->out_type);

            out = identicalTrinary(lnorm_return_type, rnorm_return_type);
          }
        }
        else
          out = Trinary_False;
      } break;

      case AC_CompositeV:
      {
        CompositeV *lhs = castAst(lhs0, CompositeV);
        CompositeV *rhs = castAst(rhs0, CompositeV);

        Trinary op_compare = identicalTrinary((lhs->op), (rhs->op));
        if ((op_compare == Trinary_False) &&
            (lhs->op->cat == AC_Form) &&
            (rhs->op->cat == AC_Form))
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

      case AC_FunctionV:
      {// we can compare the types to eliminate negatives, but we don't care.
      } break;

      invalidDefaultCase;
    }
  }
  else if (((lhs0->cat == AC_Form) && isCompositeForm(rhs0)) ||
           ((rhs0->cat == AC_Form) && isCompositeForm(lhs0)))
  {
    out = Trinary_False;
  }

  return out;
}

inline void
myprint(Stack *stack)
{
  myprint("[");
  while (stack)
  {
    myprint("[");
    for (s32 arg_id = 0; arg_id < stack->arg_count; arg_id++)
    {
      myprint(stack->args[arg_id]);
      if (arg_id != stack->arg_count-1)
        myprint(", ");
    }
    myprint("], ");
    stack = stack->outer;
  }
  myprint("]");
}

global_variable GlobalBindings *global_bindings;

struct LookupName { GlobalBinding* slot; b32 found; };

internal LookupName
lookupNameCurrentFrame(GlobalBindings *bindings, String key)
{
  GlobalBinding *slot = 0;
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
        allocate(bindings->arena, slot->next);
        slot = slot->next;
        slot->key  = key;
        slot->next = 0;
      }
    }
  }
  else
  {
    slot->key = key;
    slot->value = {};
  }

  LookupName out = { slot, found };
  return out;
}

struct LookupLocalName { LocalBinding* slot; b32 found; };

internal LookupLocalName
lookupNameCurrentFrame(LocalBindings *bindings, String key, b32 add_if_missing)
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
    slot->key = key;
    slot->value = {};
  }

  LookupLocalName out = { slot, found };
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
    if (identicalB32(in, rewrite->lhs))
      out = rewrite->rhs;
  }
  if (!out)
    out = in;

  return out;
}

// todo #speed don't pass the Environment in wholesale?
internal Value *
normalize(Environment env, Value *in0)
{
  Value *out0 = {};
  MemoryArena *arena = env.arena;

  if (global_debug_mode)
  {
    myprint("normalize: ");
    myprint(in0);
    myprint();
  }

  switch (in0->cat)
  {
    // #done
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      assert(env.stack_offset >= 0);
      assert(in->stack_delta >= 0);
      s32 stack_delta = in->stack_delta + env.stack_offset;
      Stack *stack = env.stack;
      for (s32 delta = 0; delta < stack_delta; delta++)
        stack = stack->outer;
      if (!(in->id < stack->arg_count))
      {
        myprint(env.stack);
        invalidCodePath;
      }
      out0 = stack->args[in->id];
    } break;

    // #done
    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = in->value;
    } break;

#if !TRANSITION
    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      Value **norm_args = pushArray(arena, in->arg_count, Value*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        norm_args[arg_id] = (normalize(env, in_arg));
      }

      Value *norm_op = (normalize(env, in->op));
      ArrowV *signature = castValue(norm_op->type, ArrowV);
      Value *return_type = (normalize(env, signature->a->out_type));

      CompositeV *out = newValue(env.arena, CompositeV, &in->a.token, return_type);
      out->arg_count = in->arg_count;
      out->op        = norm_op;
      out->args      = norm_args;

      out0 = &out->v.a;

      out0 = normalize(env, out0);
    } break;
#endif

    case AC_CompositeV:
    {
      CompositeV *in = castAst(in0, CompositeV);

      Value **norm_args = pushArray(arena, in->arg_count, Value*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Value *in_arg = in->args[arg_id];
        norm_args[arg_id] = (normalize(env, in_arg));
      }

      Value *norm_op = normalize(env, in->op);
      // todo: we don't expand if there is any free variable. (eg for arrow
      // types this would not normalize the return type).
      // if (env.stack_offset == 0)
      {
        if (norm_op->cat == AC_FunctionV)
        {// Function application
          FunctionV *funv = castAst(norm_op, FunctionV);
          if (funv->a != (Function *)&dummy_function_under_construction)
          {
            Environment fun_env = env;
            fun_env.stack = funv->stack;
            extendStack(&fun_env, in->arg_count, norm_args);
            // note: evaluation might fail, in which case we back out.
            out0 = evaluate(fun_env, funv->a->body);
          }
        }
        else
        {
          assert(norm_op->cat == AC_Form);
          if (norm_op == &builtins.identical->v)
          {// special case for equality
            Value *lhs = norm_args[1];
            Value *rhs = norm_args[2];
            Trinary compare = identicalTrinary(lhs, rhs);
            if (compare == Trinary_True)
              out0 = &builtins.True->v;
            else if (compare == Trinary_False)
              out0 = &builtins.False->v;
          }
        }
      }

      if (!out0)
      {
        ArrowV *signature = castValue(norm_op->type, ArrowV);
        Value *return_type = evaluate(env, signature->a->out_type);

        CompositeV *out = newValue(env.arena, CompositeV, &in->v.a.token, return_type);
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->v;
      }
      assert(out0->cat);
    } break;

#if !TRANSITION
    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Ast *norm_subject = normalize(env, in->subject);

      Environment fork_env = env;
      switch (norm_subject->cat)
      {
        case AC_Form:
        {
          Form *ctor = castAst(norm_subject, Form);
          extendStack(&fork_env, 0, 0);
          out0 = normalize(fork_env, in->bodies[ctor->ctor_id]);
        } break;

        case AC_CompositeV:
        {
          CompositeV *subject = castAst(norm_subject, CompositeV);
          if (Form *ctor = castAst(subject->op, Form))
          {
            Ast *body = in->bodies[ctor->ctor_id];
            extendStack(&fork_env, subject->arg_count, subject->args);
            out0 = normalize(fork_env, body);
          }
        } break;

        default:
          // note: we fail if the fork is undetermined
          out0 = 0;
      }
    } break;

    case AC_Sequence:
    {
      Sequence *in = castAst(in0, Sequence);
      for (s32 id = 0; id < in->count-1; id++)
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
            env.stack->args[env.stack->arg_count++] = (normalize(env, item->rhs));
          } break;

          case AC_Function:
          {
            Function  *item        = castAst(item0, Function);
            Value     *signature_v = (normalize(env, &item->signature->a));
            FunctionV *funv        = newValue(arena, FunctionV, &item->a.token, signature_v);
            funv->a     = item;
            funv->stack = env.stack;
            env.stack->args[env.stack->arg_count++] = &funv->v;
          } break;

          // todo screen the input
          invalidDefaultCase;
        }
      }
      out0 = normalize(env, in->items[in->count-1]);
    } break;

    case AC_Arrow:
    {// we can't do anything here, so just store it off somewhere.
      Arrow *in = castAst(in0, Arrow);
      ArrowV *out = newValue(env.arena, ArrowV, &in->a.token, &builtins.Type->v);
      out->a = in;
      out->stack = env.stack;
      out0 = &out->v.a;
    } break;
#endif

    case AC_ArrowV:
    case AC_FunctionV:
    case AC_StackRef:
    case AC_Form:
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
      out0 = normalize(env, out0); // do another iteration (todo: WHY?
                                   // rewriteExpression already did the loop)
  }

  if (global_debug_mode)
  {
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

internal Value *
evaluate(Environment env, Ast *in0)
{
  Value *out0 = 0;
  MemoryArena *arena = env.arena;

  if (global_debug_mode)
  {
    myprint("evaluate: ");
    myprint(in0);
    myprint();
  }

  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      assert(env.stack_offset >= 0);
      assert(in->stack_delta >= 0);
      s32 stack_delta = in->stack_delta + env.stack_offset;
      Stack *stack = env.stack;
      for (s32 delta = 0; delta < stack_delta; delta++)
        stack = stack->outer;
      if (!(in->id < stack->arg_count))
      {
        myprint(env.stack);
        invalidCodePath;
      }
      out0 = stack->args[in->id];
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
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        norm_args[arg_id] = evaluate(env, in_arg);
      }

      Value *norm_op = evaluate(env, in->op);
      ArrowV *signature = castValue(norm_op->type, ArrowV);
      Value *return_type = evaluate(env, signature->a->out_type);

      CompositeV *out = newValue(env.arena, CompositeV, &in->a.token, return_type);
      out->arg_count = in->arg_count;
      out->op        = norm_op;
      out->args      = norm_args;

      // NOTE: the legendary eval-reduce loop
      out0 = normalize(env, &out->v);
    } break;

    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Value *norm_subject = normalize(env, evaluate(env, in->subject));

      Environment fork_env = env;
      switch (norm_subject->cat)
      {
        case AC_Form:
        {
          Form *ctor = castAst(norm_subject, Form);
          extendStack(&fork_env, 0, 0);
          out0 = evaluate(fork_env, in->bodies[ctor->ctor_id]);
        } break;

        case AC_CompositeV:
        {
          CompositeV *subject = castAst(norm_subject, CompositeV);
          if (Form *ctor = castAst(subject->op, Form))
          {
            Ast *body = in->bodies[ctor->ctor_id];
            extendStack(&fork_env, subject->arg_count, subject->args);
            out0 = evaluate(fork_env, body);
          }
        } break;

        default:
          // note: we fail if the fork is undetermined
          out0 = 0;
      }
    } break;

    case AC_Arrow:
    {// we can't do anything here, so just store it off somewhere.
      Arrow *in = castAst(in0, Arrow);
      ArrowV *out = newValue(env.arena, ArrowV, &in->a.token, &builtins.Type->v);
      out->a     = in;
      out->stack = env.stack;
      out0 = &out->v;
    } break;

    case AC_Sequence:
    {
      Sequence *in = castAst(in0, Sequence);
      for (s32 id = 0; id < in->count-1; id++)
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
            env.stack->args[env.stack->arg_count++] = normalize(env, evaluate(env, item->rhs));
          } break;

          case AC_Function:
          {
            Function  *item        = castAst(item0, Function);
            Value     *signature_v = evaluate(env, &item->signature->a);
            FunctionV *funv        = newValue(arena, FunctionV, &item->a.token, signature_v);
            funv->a     = item;
            funv->stack = env.stack;
            env.stack->args[env.stack->arg_count++] = &funv->v;
          } break;

          // todo screen the input
          invalidDefaultCase;
        }
      }
      out0 = evaluate(env, in->items[in->count-1]);
    } break;

    invalidDefaultCase;
  }

  if (global_debug_mode)
  {
    myprint(" => ");
    myprint(out0);
    myprint();
  }

  return out0;
}

internal Value *
evaluate(MemoryArena *arena, Ast *in0)
{
  return evaluate(newEnvironment(arena), in0);
}

inline b32
normalized(Environment env, Value *in)
{
  Value *norm = normalize(env, in);
  return identicalB32(in, norm);
}

inline b32
addLocalBinding(LocalBindings *bindings, Token *key)
{
  auto lookup = lookupNameCurrentFrame(bindings, key->text, true);
  b32 succeed = false;
  if (lookup.found)
    parseError(key, "reused parameter name");
  else
  {
    succeed = true;
    lookup.slot->value = LocalBindingValue{bindings->count++};
  }
  return succeed;
}

internal Expression
buildExpression(Environment *env, Ast *in0, Value *expected_type);

inline b32
addLocalBindings(Environment *env, s32 count, Token *names, Ast **types, b32 should_build_types)
{
  env->bindings = extendBindings(temp_arena, env->bindings);
  // todo: #cutnpaste from "introduce", hopefully can collapse it because we'll
  // merge typecheck with build phase later.
  extendStack(env, count, 0);
  for (s32 id = 0; id < count && noError(); id++)
  {
    if (should_build_types)
      types[id] = buildExpression(env, types[id], 0).ast;
    Value    *type       = evaluate(*env, types[id]);
    StackRef *ref        = newValue(temp_arena, StackRef, names+id, type);
    env->stack->args[id] = &ref->v;

    ref->name        = names[id];
    ref->id          = id;
    ref->stack_depth = env->stack->depth;

    addLocalBinding(env->bindings, names + id);
  }
  return noError();
}

inline b32
addLocalBindings(Environment *env, Arrow *signature)
{
  return addLocalBindings(env, signature->param_count, signature->param_names, signature->param_types, false);
}

inline Value *
lookupGlobalName(char *name)
{
  return lookupNameCurrentFrame(global_bindings, toString(name)).slot->value;
}

inline Value *
lookupGlobalName(String name)
{
  return lookupNameCurrentFrame(global_bindings, name).slot->value;
}

inline b32
addGlobalBinding(Token *token, Value *value)
{
  auto lookup = lookupNameCurrentFrame(global_bindings, token->text);
  b32 succeed = true;
  if (lookup.found)
  {
    succeed = false;
    parseError(token, "redefinition");
  }
  else
    lookup.slot->value = value;
  return succeed;
}

inline b32
addGlobalBinding(char *key, Value *value)
{
  Token token = newToken(key);
  return addGlobalBinding(&token, value);
}

struct LookupNameRecursive { Ast *value; b32 found; };

inline LookupNameRecursive
lookupLocalName(MemoryArena *arena, LocalBindings *bindings, Token *token)
{
  Ast *expr = {};
  b32 found = false;

  for (s32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupLocalName lookup = lookupNameCurrentFrame(bindings, token->text, false);
    if (lookup.found)
    {
      found = true;
      auto [id] = lookup.slot->value;
      Variable *var = newAst(arena, Variable, token);
      initVariable(var, id);
      var->stack_delta = stack_delta;
      expr = &var->a;
      break;
    }
    else
      bindings = bindings->next;
  }

  LookupNameRecursive out = { expr, found };
  if (found) {assert(expr);}
  return out;
}

inline Constant *
constantFromGlobalName(MemoryArena *arena, Token *token)
{
  Constant *out = 0;
  auto lookup = lookupNameCurrentFrame(global_bindings, token->text);
  if (lookup.found)
  {
    out = newAst(arena, Constant, token);
    initConstant(out, lookup.slot->value);
  }
  return out;
}

inline b32
requireChar(Tokenizer *tk, char c, char *reason = 0)
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
requireChar(char c, char *reason = 0)
{
  return requireChar(global_tokenizer, c, reason);
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
    if (peekNext(tk).cat == tc)
    {
      out = true;
      nextToken();
    }

  return out;
}

inline b32
optionalChar(Tokenizer *tk, char c)
{
  b32 out = false;
  Token token = peekNext(tk);
  if (equal(&token, c))
  {
    out = true;
    nextToken(tk);
  }
  return out;
}

inline b32
optionalChar(char c)
{
  return optionalChar(global_tokenizer, c);
}

internal Form *
addBuiltinForm(MemoryArena *arena, char *name, Value *type, const char **ctor_names, s32 ctor_count)
{
  Token form_name = newToken(name);
  Form *form = newValue(arena, Form, &form_name, type);

  Form *ctors = pushArray(arena, ctor_count, Form);
  for (s32 ctor_id = 0; ctor_id < ctor_count; ctor_id++)
  {
    Form *ctor = ctors + ctor_id;
    Token ctor_name = newToken(ctor_names[ctor_id]);
    initValue(&ctor->v, AC_Form, &ctor_name, &form->v);
    initForm(ctor, ctor_id);
    if (!addGlobalBinding(&ctor_name, &ctor->v))
      invalidCodePath;
  }

  initForm(form, ctor_count, ctors, getNextFormId());
  if (!addGlobalBinding(&form_name, &form->v))
    invalidCodePath;

  return form;
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
  if (equal(op, "="))
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

#define VARIABLE_TRANSFORMER(name)              \
  Ast *name(Environment env, Variable *in, void *opt)

typedef VARIABLE_TRANSFORMER(variable_transformer);

#if 0
// note: this makes a copy (todo: #mem don't copy if not necessary)
// todo cheesing out on functions right now
inline Ast *
transformVariables(Environment env, Ast *in0, variable_transformer *transformer, void *opt)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in_var = castAst(in0, Variable);
      out0 = transformer(env, in_var, opt);
    } break;

    case AC_Composite:
    {
      Composite *in  = castAst(in0, Composite);
      Composite *out = copyStruct(env.arena, in);
      out0 = &out->a;
      out->op = transformVariables(env, in->op, transformer, opt);
      allocateArray(env.arena, out->arg_count, out->args);
      for (s32 arg_id = 0; arg_id < out->arg_count; arg_id++)
      {
        out->args[arg_id] = transformVariables(env, in->args[arg_id], transformer, opt);
      }
    } break;

    case AC_Fork:
    {
      Fork *in_fork  = castAst(in0, Fork);
      Fork *out_fork = copyStruct(env.arena, in_fork);
      out0 = &out_fork->a;
      out_fork->subject = transformVariables(env, in_fork->subject, transformer, opt);
      allocateArray(env.arena, out_fork->case_count, out_fork->params);
      env.stack_offset++;
      for (s32 case_id = 0;
           case_id < out_fork->case_count;
           case_id++)
      {
        out_fork->params[case_id] = in_fork->params[case_id];
        out_fork->bodies[case_id] = transformVariables(env, in_fork->bodies[case_id], transformer, opt);
      }
    } break;

    default:
        out0 = in0;
  }
  return out0;
}

VARIABLE_TRANSFORMER(abstractInstantiated)
{
  (void) opt;
  Variable *out;
  if (in->stack_depth)
  {
    assert(in->stack_depth);
    out = copyStruct(env.arena, in);
    out->stack_delta = env.stack_depth + env.stack_offset - in->stack_depth;
    out->stack_depth = 0;
  }
  else
  {
    assert(in->stack_delta < env.stack_offset);
    out = in;
  }
  return &out->h;
}

internal Ast *
abstractExpression(Environment env, Ast *in)
{
  return transformVariables(env, in, abstractInstantiated, 0);
}
#endif

// think of a function application
VARIABLE_TRANSFORMER(replaceCurrentLevelVariable)
{
  Ast **args = (Ast **)opt;
  if (env.stack_offset == in->stack_delta)
    return args[in->id];
  else
    return &in->a;
}

#if 0
// think of a function application
internal Ast *
replaceCurrentLevel(Environment env, Ast *in, Ast **args)
{
  Ast *out = transformVariables(env, in, replaceCurrentLevelVariable, args);
  // assert(identicalB32(in->type, out->type));
  return out;
}
#endif

inline void
printRewrites(Environment env)
{
  for (RewriteRule *rewrite = env.rewrite; rewrite; rewrite = rewrite->next)
  {
    printAst(0, &rewrite->lhs->a, {});
    printToBuffer(0, " => ");
    printAst(0, &rewrite->rhs->a, {});
    if (rewrite->next)
      printToBuffer(0, ", ");
  }
  myprint();
}

inline Ast *
parseExpression(MemoryArena *arena);

internal void
addRewrite(Environment *env, Value *lhs0, Value *rhs0)
{
  assert(normalized(*env, lhs0));
  assert(normalized(*env, rhs0));
  if (!identicalB32(lhs0, rhs0))
  {
    b32 added = false;

    if (CompositeV *lhs = castValue(lhs0, CompositeV))
      if (CompositeV *rhs = castValue(rhs0, CompositeV))
    {
      if ((lhs->op->cat == AC_Form) &&
          (rhs->op->cat == AC_Form))
      {
        assert(identicalB32((lhs->op), (rhs->op)));
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
    printToBuffer(0, "added rewrite: ");
    printAst(0, lhs, {});
    printToBuffer(0, " -> ");
    printAst(0, rhs, {});
    printNewline();
#endif
  }
}

VARIABLE_TRANSFORMER(rebaseVariable)
{
  Variable *out = 0;
  s32 *adjustment = (s32 *)opt;
  if (in->stack_delta >= env.stack_offset)
  {
    out = copyStruct(env.arena, in);
    out->stack_delta += *adjustment;
  }
  else
    out = in;
  return &out->a;
}

#if 0
inline Ast *
rebaseDownExpr(MemoryArena *arena, Ast *in)
{
  s32 adjustment = +1;
  Ast *out = transformVariables(newEnvironment(arena), in, rebaseVariable, &adjustment);
  return out;
}

inline Ast *
rebaseUpExpr(MemoryArena *arena, Ast *in)
{
  s32 adjustment = -1;
  return transformVariables(newEnvironment(arena), in, rebaseVariable, &adjustment);
}
#endif

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

// important: env can be modified, if the caller expects it.
// beware: Usually we mutate in-place, but we may also allocate anew.
internal Expression
buildExpression(Environment *env, Ast *in0, Value *expected_type)
{
  Expression out = {};
  b32 should_check_type = true;

  MemoryArena *arena = env->arena;
  switch (in0->cat)
  {
    // nocheckin: these cannot be standalone
    case AC_DummyHole:
    {
      out.ast = in0;
    } break;

    case AC_Identifier:
    {
      auto lookup = lookupLocalName(arena, env->bindings, &in0->token);
      if (lookup.found)
      {
        Value *norm = evaluate(*env, lookup.value);
        out.ast  = lookup.value;
        out.type = norm->type;
      }
      else
      {
        if (Constant *constant = constantFromGlobalName(arena, &in0->token))
        {
          out.ast  = &constant->a;
          out.type = constant->value->type;
        }
        else
          parseError(in0, "unbound identifier in expression");
      }
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      b32 should_build_op = true;
      Value *op_type;
      if ((in->op->cat == AC_Identifier) &&
          equal(in->op->token, "="))
      {// todo: special mutation sauce for equality
        should_build_op = false;
        assert(in->arg_count == 2);
        Ast **new_args = pushArray(arena, 3, Ast*);
        new_args[0] = &dummy_hole;
        new_args[1] = in->args[0];
        new_args[2] = in->args[1];
        // note: this is just a temporary hack to have a constant expr as the
        // operator, and not the whole form.
        Token identical_token = in->op->token;
        identical_token.text  = toString("identical");
        Constant *identical = constantFromGlobalName(arena, &identical_token);
        assert(identical);

        in->op        = &identical->a;
        in->arg_count = 3;
        in->args      = new_args;
        op_type = identical->value->type;
      }

      if (should_build_op)
      {
        Expression build_op = buildExpression(env, in->op, 0);
        in->op  = build_op.ast;
        op_type = build_op.type;
      }

      if (noError())
      {
        if (ArrowV *signature = castValue(op_type, ArrowV))
        {
          if (signature->a->param_count == in->arg_count)
          {
            Environment signature_env = *env;
            signature_env.arena = temp_arena;
            extendStack(&signature_env, in->arg_count, 0);
            Value **stack_frame = signature_env.stack->args;
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {// Type inference for the arguments. todo: the hole stuff is
              // kinda hard-coded only for the equality.
              if (in->args[arg_id] == &dummy_hole)
                stack_frame[arg_id] = 0;
              else
              {
                Ast *param_type = signature->a->param_types[arg_id];
                Value *norm_param_type = evaluate(signature_env, param_type);
                if (Expression build_arg = buildExpression(env, in->args[arg_id], norm_param_type))
                {
                  in->args[arg_id] = build_arg.ast;
                  stack_frame[arg_id] = evaluate(*env, in->args[arg_id]);
                  if (norm_param_type == 0)
                  {
                    Variable *param_type_var = castAst(param_type, Variable);
                    assert(param_type_var->stack_delta == 0);
                    stack_frame[param_type_var->id] = build_arg.type;

                    // write back to the input ast. (TODO: doesn't actually work
                    // since we don't handle variables in the type)
                    Token token = newToken("<synthetic>");
                    Constant *synthetic = newAst(arena, Constant, &token);
                    synthetic->value = build_arg.type;
                    in->args[param_type_var->id] = &synthetic->a;
                  }
                }
              }
            }

            if (noError())
            {
              extendStack(env, in->arg_count, stack_frame);
              out.ast = in0;
              out.type = evaluate(*env, signature->a->out_type);
              unwindStack(env);
            }
          }
          else
            parseError(in0, "incorrect arg count: %d (signature expected %d)", in->arg_count, signature->a->param_count);
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          pushAttachment("got type", &op_type->a);
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
        buildExpression(&env, in->items[item_id], 0);
      }
      Expression last = buildExpression(&env, in->items[in->count-1], expected_type);
      in->items[in->count-1] = last.ast;

      out.type = last.type;
      out.ast = &in->a;
    } break;

    case AC_Let:
    {
      Let *in = castAst(in0, Let);
      if (Expression build_rhs = buildExpression(env, in->rhs, 0))
      {
        addLocalBinding(env->bindings, &in->lhs.a.token);
        in->rhs = build_rhs.ast;
        env->stack->args[env->stack->arg_count++] = evaluate(*env, in->rhs);

        out.ast  = in->rhs;
        out.type = build_rhs.type;
      }
    } break;

    case AC_Function:
    {// NOTE: both local and global function.
      Function *in = castAst(in0, Function);

      assert(!expected_type);
      char *debug_name = "+";
      if (equal(in->a.token, debug_name))
        breakhere;

      if (auto build_signature = buildExpression(env, &in->signature->a, 0))
      {
        // note: store the built signature, maybe to display it later.
        in->signature = castAst(build_signature.ast, Arrow);
        Value *signature_v = evaluate(*env, &in->signature->a);
        FunctionV *funv = newValue(arena, FunctionV, &in->a.token, signature_v);
        // note: we only need that funv there for the type.
        funv->a = &dummy_function_under_construction;

        // note: add binding first to support recursion
        b32 is_local = (bool)env->bindings;
        if (is_local)
        {// local context
          addLocalBinding(env->bindings, &in->a.token);
          env->stack->args[env->stack->arg_count++] = &funv->v;
        }
        else
        {// global context
          addGlobalBinding(&in->a.token, &funv->v);
        }

        if (noError())
        {
          addLocalBindings(env, in->signature);
          assert(noError());

          Value *expected_body_type = evaluate(*env, in->signature->out_type);
          in->body = buildExpression(env, in->body, expected_body_type).ast;
          unwindBindingsAndStack(env);
        }
        out.ast  = in0;
        out.type = signature_v;

        // add this function to the stack.
        funv->a     = in;
        funv->stack = env->stack;
        if (is_local)
        {
          env->stack->args[env->stack->arg_count++] = &funv->v;
        }
      }
    } break;

    case AC_Rewrite:
    {
      Rewrite *in = castAst(in0, Rewrite);
#if 0
      if (in->rhs)
      {
        Ast *lhs = in->lhs = buildExpression(env, in->lhs, 0).ast;
        Ast *rhs = in->rhs = buildExpression(env, in->rhs, 0).ast;
        Value *norm_lhs_begin = normalize(*env, lhs);
        Value *norm_lhs = norm_lhs_begin;
        Value *norm_rhs = (normalize(*env, rhs));
        while (noError())
        {
          if (identicalB32(norm_lhs, norm_rhs))
          {
            addRewrite(env, norm_lhs_begin, norm_rhs);
            break;
          }
          Value *before = norm_lhs;
          norm_lhs = (normalize(*env, &norm_lhs->a));
          if (identicalB32(norm_lhs, before))
          {
            parseError(in0, "failed to prove legitimacy of rewrite rule");
          }
        }
      }
      else
#endif
      {
        if (Expression build_rewrite = buildExpression(env, in->lhs, 0))
        {
          in->lhs = build_rewrite.ast;
          b32 rule_valid = false;
          if (CompositeV *norm_rule = castValue(build_rewrite.type, CompositeV))
          {
            if (norm_rule->op == &builtins.identical->v)
            {
              rule_valid = true;
              addRewrite(env, (norm_rule->args[1]), (norm_rule->args[2]));
            }
          }
          if (!rule_valid)
          {
            parseError(in0, "invalid rewrite rule, can only be equality");
            pushAttachment("got", &build_rewrite.type->a);
          }
        }
      }

      out.ast  = in0;
      out.type = &builtins.True->v;  // #hack
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      out.ast = in0;
      out.type = &builtins.Type->v;
      // note: we build the types along with adding local bindings below.
      addLocalBindings(env, in->param_count, in->param_names, in->param_types, true);
      if (noError())
      {
        in->out_type = buildExpression(env, in->out_type, 0).ast;
      }
      unwindBindingsAndStack(env);
    } break;

    case AC_IncompleteFork:
    {
      should_check_type = false;
      IncompleteFork *in = castAst(in0, IncompleteFork);

      if (auto [subject, subject_type] = buildExpression(env, in->subject, 0))
      {
        in->subject = subject;
        s32 case_count = in->case_count;

        if (Form *form = castValue(subject_type, Form))
        {
          if (form->ctor_count == case_count)
          {
            ForkParameters  *correct_params = pushArray(arena, case_count, ForkParameters, true);
            Ast            **correct_bodies = pushArray(arena, case_count, Ast *, true);
            Value *common_type  = expected_type;
            Value *norm_subject = evaluate(*env, in->subject);
            Environment *outer_env = env;
            for (s32 input_case_id = 0;
                 input_case_id < case_count && noError();
                 input_case_id++)
            {
              Environment env = *outer_env;
              Token *ctor_token = &in->parsing->ctors[input_case_id].a.token;

              ForkParameters *params = in->parsing->params + input_case_id;
              Token *param_names = params->names;
              s32    param_count = params->count;

              if (Value *lookup = lookupGlobalName(ctor_token->text))
              {
                if (Form *ctor = castValue(lookup, Form))
                {
                  if (param_count == 0)
                  {
                    if (identicalB32(ctor->v.type, subject_type)) 
                    {
                      addRewrite(&env, norm_subject, &ctor->v);
                      addLocalBindings(&env, 0, 0, 0, false);
                    }
                    else
                    {
                      parseError(ctor_token, "constructor of wrong type");
                      pushAttachment("expected type", &subject_type->a);
                      pushAttachment("got type", &ctor->v.type->a);
                    }
                  }
                  else
                  {
                    if (ArrowV *ctor_sig = castValue(ctor->v.type, ArrowV))
                    {
                      if (identicalB32(&getFormOf(ctor_sig->a->out_type)->v,
                                       &getFormOf(subject_type)->v))
                      {
                        if (param_count == ctor_sig->a->param_count)
                        {
                          addLocalBindings(&env, param_count, params->names, ctor_sig->a->param_types, false);
                          Value *pattern_type = evaluate(env, ctor_sig->a->out_type);
                          CompositeV *pattern = newValue(temp_arena, CompositeV, &ctor->v.a.token, pattern_type);
                          pattern->op        = &ctor->v;
                          pattern->arg_count = param_count;
                          pattern->args      = env.stack->args;
                          addRewrite(&env, norm_subject, &pattern->v);
                        }
                        else
                          parseError(ctor_token, "pattern has wrong number of parameters (expected: %d, got: %d)", ctor_sig->a->param_count, param_count);
                      }
                      else
                      {
                        parseError(ctor_token, "composite constructor has wrong return type");
                        pushAttachment("expected type", &subject_type->a);
                        pushAttachment("got type", ctor_sig->a->out_type);
                      }
                    }
                    else
                    {
                      parseError(ctor_token, "expected a composite constructor");
                      pushAttachment("got type", &ctor_sig->v.a);
                    }
                  }

                  if (noError())
                  {
                    if (correct_bodies[ctor->ctor_id])
                    {
                      parseError(in->parsing->bodies[input_case_id], "fork case handled twice");
                      pushAttachment("constructor", &ctor->v.a);
                    }
                    else
                    {
                      correct_params[ctor->ctor_id].count = param_count;
                      correct_params[ctor->ctor_id].names = param_names;
                      Expression body = buildExpression(&env, in->parsing->bodies[input_case_id], common_type);
                      correct_bodies[ctor->ctor_id] = body.ast;
                      if (!common_type)
                        common_type = body.type;
                    }
                  }
                }
                else
                  parseError(ctor_token, "expected constructor");
              }
              else
                parseError(ctor_token, "undefined identifier");
            }

            if (noError())
            {
              in->a.cat   = AC_Fork;
              in->form    = form;
              in->params  = correct_params;
              in->bodies  = correct_bodies;

              out.ast  = in0;
              out.type = common_type;
            }
          }
          else
            parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                       form->ctor_count, in->case_count);
        }
        else
        {
          parseError(in->subject, "cannot fork expression of type");
          pushAttachment("type", &subject_type->a);
        }
      }
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// one last typecheck if needed
    if (expected_type && should_check_type)
    {
      Value *norm_expected = normalize(*env, expected_type);
      Value *norm_actual = normalize(*env, out.type);
      if (!identicalB32(norm_expected, norm_actual))
      {
        parseError(in0, "actual type differs from expected type");
        global_debug_mode = true;
        normalize(*env, expected_type);
        pushAttachment("expected", &norm_expected->a);
        pushAttachment("got", &norm_actual->a);
      }
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Expression
buildExpressionGlobal(MemoryArena *arena, Ast *ast, Value *expected_type = 0)
{
  Environment env = newEnvironment(arena);
  return buildExpression(&env, ast, expected_type);
}

inline Expression
parseExpressionAndTypecheck(MemoryArena *arena, LocalBindings *bindings, Value *expected_type)
{
  Expression out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Environment env = newEnvironment(arena);
    env.bindings = bindings;
    if (Expression build = buildExpression(&env, ast, expected_type))
    {
      out.ast  = build.ast;
      out.type = build.type;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Ast *
parseExpression(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0).ast;
}

inline Expression
parseExpressionFull(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0);
}

internal Rewrite *
parseRewrite(MemoryArena *arena)
{
  Token token = global_tokenizer->last_token;
  Rewrite *out = newAst(arena, Rewrite, &token);
  if (Ast *lhs_or_proof = parseExpressionToAst(arena))
  {
    if (optionalCategory(TC_StrongArrow))
    {
      if (Ast *rhs = parseExpressionToAst(arena))
      {
        out->lhs = lhs_or_proof;
        out->rhs = rhs;
      }
    }
    else
    {
      out->lhs = lhs_or_proof;
      out->rhs = 0;
    }
  }
  NULL_WHEN_ERROR(out);
  return out;
}

internal Function *
parseFunction(MemoryArena *arena, Token *name);

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
    b32 commit = true;
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
          // todo: do we really wanna constraint it to only appear in sequence?
          case Keyword_Rewrite:
          {
            ast = &parseRewrite(arena)->a;
          } break;

          default:
          {
            commit = false;
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
            pushContextName("recursive let");
            Function *fun = parseFunction(arena, name);
            ast = &fun->a;
            popContext();
          } break;

          case TC_ColonEqual:
          {
            pushContextName("let");
            Ast *rhs = parseExpressionToAst(arena);

            Let *let = newAst(arena, Let, name);
            ast = &let->a;
            initAst(&let->lhs.a, AC_Identifier, name);
            let->rhs = rhs;

            popContext();
          } break;

          default:
          {
            commit = false;
          } break;
        }
      }

      if (noError())
      {
        if (commit) {assert(ast);}
        else
        {
          *global_tokenizer = tk_save;
          ast = parseExpressionToAst(arena);
        }
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

internal Function *
parseFunction(MemoryArena *arena, Token *name)
{
  pushContext;
  Function *out = newAst(arena, Function, name);

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

internal IncompleteFork *
parseFork(MemoryArena *arena)
{
  pushContext;

  IncompleteFork *out = 0;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpressionToAst(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *global_tokenizer;
    s32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      ForkParsing *parsing = pushStruct(temp_arena, ForkParsing);
      Ast **bodies   = parsing->bodies = pushArray(temp_arena, case_count, Ast*);
      allocateArray(temp_arena, case_count, parsing->ctors);
      allocateArray(temp_arena, case_count, parsing->params);

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
              parsing->params[input_case_id] = {};
            }
            else if (Composite *pattern = castAst(pattern0, Composite))
            {
              s32 param_count = pattern->arg_count;
              if ((ctor = castAst(pattern->op, Identifier)))
              {
                parsing->ctors[input_case_id] = *ctor;

                ForkParameters *params = parsing->params + input_case_id;
                params->count = param_count;
                allocateArray(temp_arena, param_count, params->names);
                for (s32 param_id = 0;
                     param_id < param_count && noError();
                     param_id++)
                {
                  if (Identifier *param = castAst(pattern->args[param_id], Identifier))
                  {
                    params->names[param_id] = param->a.token;
                  }
                  else
                    parseError(pattern->args[param_id], "expected pattern variable");
                }
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
        out = newAst(arena, IncompleteFork, &token);
        out->a.token    = token;
        out->subject    = subject;
        out->case_count = case_count;
        out->parsing    = parsing;
      }
    }
  }
  popContext();

  return out;
}

internal Arrow *
parseArrowType(MemoryArena *arena)
{
  Arrow *out = 0;
  pushContext;

  s32     param_count;
  Token  *param_names;
  Ast   **param_types;
  Token marking_token = peekNext();
  if (requireChar('('))
  {
    Tokenizer tk_copy = *global_tokenizer;
    param_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      param_names = pushArray(arena, param_count, Token);
      param_types = pushArray(arena, param_count, Ast*);

      s32 parsed_param_count = 0;
      s32 typeless_run = 0;
      Token typeless_token;
      for (b32 stop = false;
           !stop && hasMore();
           )
      {
        Token param_name_token = nextToken();
        if (equal(&param_name_token, ')'))
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
              if (equal(&delimiter, ')'))
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

  if (requireCategory(TC_Arrow, "syntax: (param: type, ...) -> ReturnType"))
  {
    if (Ast *return_type = parseExpressionToAst(arena))
    {
      out = newAst(arena, Arrow, &marking_token);
      out->param_count = param_count;
      out->out_type = return_type;
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
      out = &dummy_hole;
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
    Token funcall = peekNext();
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
  if (requireChar(tk, '('))
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
    // todo wth is this?
    out = &parseArrowType(arena)->a;
  }
  else
  {
    if (Ast *operand = parseOperand(arena))
    {
      // (a+b) * c
      //     ^
      for (b32 stop = false; !stop && hasMore();)
      {
        Token op_token = peekNext();
        if (isIdentifier(&op_token))
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
              Ast **args = pushArray(arena, 2, Ast*);
              args[0] = operand;
              args[1] = recurse;
              Composite *new_operand = newAst(arena, Composite, &op_token);
              initComposite(new_operand, &op->a, 2, args);
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
          tokenError(&op_token, "expected operator token, got");
      }
      if (noError())
        out = operand;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Ast *
parseExpressionToAst(MemoryArena *arena)
{
  return parseExpressionToAstMain(arena, ParseExpressionOptions{});
}

internal Form *
parseConstructorDef(MemoryArena *arena, Form *out, Form *form, s32 ctor_id)
{
  pushContext;

  Token ctor_token = nextToken();
  if (isIdentifier(&ctor_token))
  {
    if (addGlobalBinding(&ctor_token, &out->v))
    {
      if (optionalChar(':'))
      {
        if (Ast *parsed_type = parseExpressionFull(arena).ast)
        {
          Value *norm_type0 = evaluate(arena, parsed_type);
          b32 valid_type = false;
          if (Form *type = castValue(norm_type0, Form))
          {
            if (type == form)
              valid_type = true;
          }
          else if (ArrowV *type = castValue(norm_type0, ArrowV))
          {
            if (getFormOf(type->a->out_type) == form)
              valid_type = true;
          }

          if (valid_type)
          {
            initValue(&out->v, AC_Form, &ctor_token, norm_type0);
            initForm(out, ctor_id);
          }
          else
          {
            parseError(parsed_type, "invalid type for constructor");
            pushAttachment("type", parsed_type);
          }
        }
      }
      else
      {
        // default type is the form itself
        if (form->v.type == &builtins.Set->v)
        {
          initValue(&out->v, AC_Form, &ctor_token, &form->v);
          initForm(out, ctor_id);
        }
        else
          parseError(&ctor_token, "constructors must construct a set member");
      }
    }
    else
      tokenError("redefinition of constructor name");
  }
  else
    tokenError("expected an identifier as constructor name");

  popContext();
  return out;
}

internal void
parseTypedef(MemoryArena *arena)
{
  pushContext;

  Token form_name = nextToken();
  if (isIdentifier(&form_name))
  {
    Form *form = pushStruct(arena, Form);
    // NOTE: the type is in scope of its own constructor.
    if (addGlobalBinding(&form_name, &form->v))
    {
      Value *type = &builtins.Set->v;
      if (optionalChar(':'))
      {// type override
        b32 valid_type = false;
        if (Expression type_parsing = parseExpressionFull(arena))
        {
          Value *norm_type = evaluate(arena, type_parsing.ast);
          if (ArrowV *arrow = castValue(norm_type, ArrowV))
          {
            if (Constant *return_type = castAst(arrow->a->out_type, Constant))
              if (return_type->value == &builtins.Set->v)
                valid_type = true;
          }
          else if (norm_type == &builtins.Set->v)
            valid_type = true;

          if (valid_type)
            type = norm_type;
          else
          {
            parseError(type_parsing.ast, "form has invalid type");
            pushAttachment("type", &norm_type->a);
          }
        }
      }

      if (requireChar('{', "open typedef body"))
      {
        Tokenizer tk_copy = *global_tokenizer;
        s32 expected_ctor_count = getCommaSeparatedListLength(&tk_copy);
        // NOTE: init here for recursive definition
        if (noError(&tk_copy))
        {
          Form *ctors = pushArray(arena, expected_ctor_count, Form);
          initValue(&form->v, AC_Form, &form_name, type);
          initForm(form, expected_ctor_count, ctors, getNextFormId());
          s32 parsed_ctor_count = 0;
          for (s32 stop = 0;
               !stop && noError();)
          {
            if (optionalChar('}'))
              stop = true;
            else
            {
              s32 ctor_id = parsed_ctor_count++;
              parseConstructorDef(arena, (ctors + ctor_id), form, ctor_id);
              if (!optionalChar(','))
              {
                requireChar('}', "to end the typedef; or you might want a comma ',' to delimit constructors");
                stop = true;
              }
            }
          }

          if (noError())
          {
            assert(parsed_ctor_count == expected_ctor_count);
            assert(constantFromGlobalName(temp_arena, &form_name));
          }
        }
      }
    }
    else
      tokenError("redefinition of type");
  }

  popContext();
}

struct FileList
{
  char     *first_path;
  char     *first_content;
  FileList *next;
};

struct EngineState
{
  MemoryArena *arena;
  FileList    *file_list;
};

internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file = false);

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  pushContext;
  MemoryArena *arena = state->arena;

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
        case MetaDirective_Load:
        {
          pushContextName("#load");
          auto file = nextToken();
          if (file.cat != TC_StringLiteral)
            tokenError("expect \"FILENAME\"");
          else
          {
            auto path_buffer = arena;
            char *load_path = printToBuffer(path_buffer, global_tokenizer->directory);
            printToBuffer(path_buffer, file.text);
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
              auto interp_result = interpretFile(state, full_path);
              if (!interp_result)
                tokenError("failed loading file");
            }
          }
          popContext();
        } break;

        default:
        {
          tokenError("unknown meta directive");
        } break;
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

          case Keyword_Typedef:
          {
            parseTypedef(arena);
          } break;

          case Keyword_Print:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              Value *reduced = normalize(temp_arena, evaluate(temp_arena, parsing.ast));
              printAst(0, reduced, {.detailed=true});
              printToBuffer(0, ": ");
              printAst(0, &parsing.type->a, {});
              myprint();
            }
            requireChar(';');
          } break;

          case Keyword_PrintRaw:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              printAst(0, parsing.ast, {.detailed=true});
              printToBuffer(0, ": ");
              printAst(0, &parsing.type->a, {});
              myprint();
            }
            requireChar(';');
          } break;

          case Keyword_PrintDebug:
          {
            if (Ast *exp = parseExpression(temp_arena))
            {
              char *output = printAst(temp_arena, exp, {.detailed=true, .print_type=true});
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
            parseError(&token, "invalid keyword at top-leve");
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
            if (Function *fun = parseFunction(arena, name))
            {
              buildExpressionGlobal(arena, &fun->a);
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
  }

  popContext();
}

internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  MemoryArena *arena = state->arena;
  b32 success = true;
#if 0
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

      if (error->attached_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attached_count;
             attached_id++)
        {
          auto attachment = error->attached[attached_id];
          printf("%s: ", attachment.string);
          printAst(0, attachment.expression, {});
          if (attached_id != error->attached_count-1) 
            printf("\n");
        }
      }
      printf("\n");
    }

#if 0
    auto compile_time = platformGetSecondsElapsed(begin_time, platformGetWallClock(arena));
    printf("Compile time for file %s: %fs\n", file_path, compile_time);
    printf("----------------\n");
#endif

    global_tokenizer = old_tokenizer;
  }
  else
  {
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
    global_bindings = pushStruct(arena, GlobalBindings);
    global_bindings->arena = arena;

    builtins = {};
    const char *builtin_Type_members[] = {"Set"};
    builtins.Type = addBuiltinForm(arena, "Type", 0, builtin_Type_members, 1);
    builtins.Set  = castValue(lookupGlobalName("Set"), Form);
    builtins.Type->v.type = &builtins.Type->v; // note: circular types are gonna bite us

    const char *true_members[] = {"truth"};
    addBuiltinForm(arena, "True", &builtins.Set->v, true_members, 1);
    builtins.True  = castValue(lookupGlobalName("True"), Form);
    builtins.truth = castValue(lookupGlobalName("truth"), Form);

    addBuiltinForm(arena, "False", &builtins.Set->v, (const char **)0, 0);
    builtins.False = castValue(lookupGlobalName("False"), Form);

    {// Equality
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), true);
      assert(success);
      builtins.identical = castValue(lookupGlobalName("identical"), Form);
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
  Variable  Variable;
  Constant  Constant;
  Composite Composite;
  Fork      Fork;
  Arrow ArrowType;
  Form      Form;
  Function  Function;
  StackRef  StackRef;
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
  MemoryArena *permanent_arena  = &permanent_arena_;

  void   *temp_memory_base = (void*)teraBytes(3);
  size_t  temp_memory_size = megaBytes(2);
  temp_memory_base = platformVirtualAlloc(temp_memory_base, permanent_memory_size);
  MemoryArena temp_arena_ = newArena(temp_memory_size, temp_memory_base);
  temp_arena       = &temp_arena_;

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/basics.rea"))
    success = false;
  resetZeroArena(permanent_arena);
#endif

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/nat.rea"))
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

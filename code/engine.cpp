#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_globals.h"

#if REA_INTERNAL
#  define INTERNAL_ERROR global_tokenizer->error
#else
#  define INTERNAL_ERROR false
#endif

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

inline void
initSet(Set *in, AstCategory cat, Token *token, Value *type)
{
  initValue(&in->v, cat, type);
  in->token  = *token;
  in->set_id = getNextSetId();
}

inline Set *
newSet_(MemoryArena *arena, size_t size, AstCategory cat, Token *token, Value *type)
{
  Set *out = (Set *)pushSize(arena, size, true);
  initSet(out, cat, token, type);
  return out;
}

#define newSet(arena, cat, ...)                     \
  ((cat *) newSet_(arena, sizeof(cat), AC_##cat, __VA_ARGS__))

inline void
initSetNocheckin(Union *in, Token *token, u64 set_id)
{
  in->v.cat    = AC_Union;
  in->s.token  = *token;
  in->s.set_id = SetId{set_id}; // todo set_id is used to distinguish branches in a
                          // fork, which is now the wrong semantics.
  in->subset_count = 0;
  in->subsets      = 0;
}

// prints both Composite and CompositeV
inline void
printComposite(MemoryArena *buffer, void *in0, PrintOptions opt)
{
  void  *op;
  s32    arg_count;
  void **raw_args;

  Ast   *ast   = (Ast *)in0;
  Value *value = (Value *)in0;
  ArrowV *op_type = 0;
  if (Composite *in = castAst(ast, Composite))
  {
    op = in->op;
    raw_args = (void **)in->args;
    if (Constant *op = castAst(in->op, Constant))
    {
      op_type = castAst(op->value->type, ArrowV);
      assert(op_type);
    }
    else
    {
      arg_count = in->arg_count;
    }
  }
  else if (CompositeV *in = castAst(value, CompositeV))
  {
    op = in->op;
    raw_args = (void **)in->args;
    op_type = castAst(in->op->type, ArrowV);
    assert(op_type);
  }
  else
  {
    invalidCodePath;
  }

  void **args;
  if (op_type)
  {// print out unignored args only
    args = pushArray(temp_arena, op_type->a->param_count, void*);
    arg_count = 0;
    for (s32 param_id = 0; param_id < op_type->a->param_count; param_id++)
    {
      if (!op_type->a->param_implied[param_id])
      {
        args[arg_count++] = raw_args[param_id];
      }
    }
  }
  else
    args = raw_args;

  if (arg_count == 2)
  {// special path for infix operator
    printToBuffer(buffer, "(");
    printAst(buffer, args[0], opt);
    printToBuffer(buffer, " ");
    printAst(buffer, op, opt);
    printToBuffer(buffer, " ");
    printAst(buffer, args[1], opt);
    printToBuffer(buffer, ")");
  }
  else
  {// normal pre path
    printAst(buffer, op, opt);
    printToBuffer(buffer, "(");
    for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
    {
      printAst(buffer, args[arg_id], opt);
      if (arg_id < arg_count-1)
        printToBuffer(buffer, ", ");
    }
    printToBuffer(buffer, ")");
  }
}

// note: prints both (built) ast and value
forward_declare
internal char *
printAst(MemoryArena *buffer, void *in_void, PrintOptions opt)
{
  Ast *in0 = (Ast *)in_void;
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0 == &dummy_hole)
  {
    printToBuffer(buffer, "_");
  }
  else if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
      case AC_StackRef:
      {
        StackRef *in = castAst(in0, StackRef);
#if 0
        printToBuffer(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
#else
        printToBuffer(buffer, in->name);
#endif
      } break;

      case AC_Constant:
      {
        Constant *in = castAst(in0, Constant);
        printToBuffer(buffer, in->a.token);
      } break;

      case AC_Variable:
      {
        Variable *in = castAst(in0, Variable);
#if 0
        printToBuffer(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
#else
        printToBuffer(buffer, in->a.token);
#endif
      } break;

      case AC_Sequence:
      {
        Sequence *in = castAst(in0, Sequence);
        for (s32 id = 0; id < in->count; id++)
        {
          printAst(buffer, in->items[id], new_opt);
          if (id < in->count-1)
            printToBuffer(buffer, "; ");
        }
      } break;

      case AC_Rewrite:
      {
        Rewrite *in = castAst(in0, Rewrite);
        printToBuffer(buffer, "rewrite ");
        printAst(buffer, in->proof, new_opt);
      } break;

      case AC_CompositeV:
      case AC_Composite:
      {
        printComposite(buffer, in0, new_opt);
      } break;

      case AC_Fork:
      {
        Fork *in = castAst(in0, Fork);
        printToBuffer(buffer, "fork ");
        printAst(buffer, in->subject, new_opt);
        printToBuffer(buffer, " {");
        Union *form = in->union0;
        for (s32 ctor_id = 0;
             ctor_id < form->subset_count;
             ctor_id++)
        {
          ForkParameters *casev = in->params + ctor_id;
          Set *subset = form->subsets[ctor_id];
          switch (subset->v.type->cat)
          {// print pattern
            case AC_Union:
            {
              printAst(buffer, &subset->v, new_opt);
            } break;

            case AC_ArrowV:
            {
              printAst(buffer, &subset->v, new_opt);
              printToBuffer(buffer, " ");
              ArrowV *signature = castAst(subset->v.type, ArrowV);
              for (s32 param_id = 0; param_id < signature->a->param_count; param_id++)
              {
                printToBuffer(buffer, casev->names[param_id]);
                printToBuffer(buffer, " ");
              }
            } break;

            invalidDefaultCase;
          }

          printToBuffer(buffer, ": ");
          printAst(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != form->subset_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, "}");
      } break;

      case AC_Arrow:
      {
        Arrow *in = castAst(in0, Arrow);
        printToBuffer(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          printToBuffer(buffer, in->param_names[param_id]);
          printToBuffer(buffer, ": ");
          printAst(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ") -> ");

        printAst(buffer, in->out_type, new_opt);
      } break;

      case AC_Union:
      {
        Union *in = castAst(in0, Union);
        if (opt.detailed)
        {
          printToBuffer(buffer, in->s.token);

          if (opt.print_type)
          {
            printToBuffer(buffer, ": ");
            printAst(buffer, in->v.type, new_opt);
          }

          if (in->subset_count)
          {
            printToBuffer(buffer, " {");
            for (s32 subset_id = 0; subset_id < in->subset_count; subset_id++)
            {
              Set *subset = in->subsets[subset_id];
              printToBuffer(buffer, subset->token);
              printToBuffer(buffer, ": ");
              printAst(buffer, subset->v.type, new_opt);
            }
            printToBuffer(buffer, " }");
          }
        }
        else
          printToBuffer(buffer, in->s.token);
      } break;

      case AC_FunctionV:
      {
        FunctionV *in = castAst(in0, FunctionV);
        printToBuffer(buffer, in->token);
        if (opt.detailed)
        {
          printToBuffer(buffer, " { ");
          printAst(buffer, in->a->body, new_opt);
          printToBuffer(buffer, " }");
        }
      } break;

      case AC_ArrowV:
      {
        ArrowV *in = castAst(in0, ArrowV);
        printAst(buffer, &in->a->a, opt);
      } break;

      case AC_BuiltinEqual:
      {
        printToBuffer(buffer, "=");
      } break;

      case AC_BuiltinSet:
      {
        printToBuffer(buffer, "Set");
      } break;

      case AC_BuiltinType:
      {
        printToBuffer(buffer, "Type");
      } break;

      default:
      {
        printToBuffer(buffer, "<unimplemented category: %u>", in0->cat);
      } break;
    }
  }
  else
    printToBuffer(buffer, "<null>");
  return out;
}

inline void
myprint(Value *in0)
{
  printAst(0, in0, {});
}

inline void
myprint(Ast *in0)
{
  printAst(0, in0, {});
}

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

inline b32
identicalB32(Value *lhs, Value *rhs)
{
  return identicalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeForm(Value *in0)
{
  if (Composite *in = castAst(in0, Composite))
    return castAst(in->op, Union) != 0;
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

internal Value **
introduce(Environment *env, s32 count, Token *names, Ast **types_ast, s32 depth_override=0)
{
  assert(count < arrayCount(env->stack->args));
  extendStack(env, count, 0, depth_override);
  Value **types = pushArray(temp_arena, count, Value *);
  for (s32 id = 0; id < count; id++)
  {
    types[id] = evaluate(*env, types_ast[id]);
    StackRef *ref    = newValue(temp_arena, StackRef, types[id]);
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

      case AC_Union:
      {
        out = (Trinary)(castAst(lhs0, Union)->s.set_id.id ==
                        castAst(rhs0, Union)->s.set_id.id);
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
            (lhs->op->cat == AC_Union) &&
            (rhs->op->cat == AC_Union))
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
  else if (((lhs0->cat == AC_Union) && isCompositeForm(rhs0)) ||
           ((rhs0->cat == AC_Union) && isCompositeForm(lhs0)))
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
    slot->key   = key;
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
forward_declare
internal Value *
normalize(Environment env, Value *in0)
{
  Value *out0 = {};
  MemoryArena *arena = env.arena;

  if (INTERNAL_ERROR)
  {
    debugIndent();
    myprint("normalize: ");
    myprint(in0);
    myprint();
  }

  switch (in0->cat)
  {
    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      Stack *stack = env.stack;
      for (s32 delta = 0; delta < in->stack_delta ; delta++)
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
          if (norm_op == builtins.equal)
          {// special case for equality
            Value *lhs = norm_args[1];
            Value *rhs = norm_args[2];
            Trinary compare = identicalTrinary(lhs, rhs);
            if (compare == Trinary_True)
              out0 = &builtins.True->v;
            else if (compare == Trinary_False)
              out0 = &builtins.False->v;
          }
          else
            assert(norm_op->cat == AC_Union);
        }
      }

      if (!out0)
      {
        ArrowV *signature = castAst(norm_op->type, ArrowV);
        Value *return_type = evaluate(env, signature->a->out_type);

        CompositeV *out = newValue(env.arena, CompositeV, return_type);
        out->arg_count = in->arg_count;
        out->op        = norm_op;
        out->args      = norm_args;

        out0 = &out->v;
      }
      assert(out0->cat);
    } break;

#if 0
    case AC_AccessorV:
    {
      AccessorV *in = castAst(in0, AccessorV);
      out0 = in->record->args[in->param_id];
    } break;
#endif

    case AC_BuiltinSet:
    case AC_BuiltinType:
    case AC_BuiltinEqual:
    case AC_ArrowV:
    case AC_FunctionV:
    case AC_StackRef:
    case AC_Union:
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

  if (INTERNAL_ERROR)
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

forward_declare
internal Value *
evaluate(Environment env, Ast *in0)
{
  Value *out0 = 0;
  MemoryArena *arena = env.arena;

  if (INTERNAL_ERROR)
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
      Stack *stack = env.stack;
      for (s32 delta = 0; delta < in->stack_delta; delta++)
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
      ArrowV *signature = castAst(norm_op->type, ArrowV);
      Value *return_type = evaluate(env, signature->a->out_type);

      CompositeV *out = newValue(env.arena, CompositeV, return_type);
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
        case AC_Union:
        {
          Union *ctor = castAst(norm_subject, Union);
          extendStack(&fork_env, 0, 0);
          out0 = evaluate(fork_env, in->bodies[ctor->s.set_id]);
        } break;

        case AC_CompositeV:
        {
          CompositeV *subject = castAst(norm_subject, CompositeV);
          if (Union *ctor = castAst(subject->op, Union))
          {
            Ast *body = in->bodies[ctor->s.set_id];
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
      ArrowV *out = newValue(env.arena, ArrowV, builtins.Type);
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
            FunctionV *funv        = newValue(arena, FunctionV, signature_v);
            funv->token = item->a.token;
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

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      CompositeV *recordv = castAst(evaluate(env, in->record), CompositeV);
      out0 = recordv->args[in->param_id];
    } break;

    invalidDefaultCase;
  }

  if (INTERNAL_ERROR)
  {
    debugDedent();
    myprint("=> ");
    myprint(out0);
    myprint();
  }

  if (out0)
    out0 = normalize(env, out0);

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
    lookup.slot->value = bindings->count++;
  }
  return succeed;
}

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
    else
      assert(types[id]);

    if (types[id])
    {
      Value    *type       = evaluate(*env, types[id]);
      StackRef *ref        = newValue(temp_arena, StackRef, type);
      env->stack->args[id] = &ref->v;

      ref->name        = names[id];
      ref->id          = id;
      ref->stack_depth = env->stack->depth;

      addLocalBinding(env->bindings, names + id);
    }
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
      s32 id = lookup.slot->value;
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
optionalChar(Tokenizer *tk, char c)
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
optionalChar(char c)
{
  return optionalChar(global_tokenizer, c);
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

inline void
printRewrites(Environment env)
{
  for (RewriteRule *rewrite = env.rewrite; rewrite; rewrite = rewrite->next)
  {
    printAst(0, rewrite->lhs, {});
    printToBuffer(0, " => ");
    printAst(0, rewrite->rhs, {});
    if (rewrite->next)
      printToBuffer(0, ", ");
  }
  myprint();
}

internal void
addRewrite(Environment *env, Value *lhs0, Value *rhs0)
{
  assert(normalized(*env, lhs0));
  assert(normalized(*env, rhs0));
  if (!identicalB32(lhs0, rhs0))
  {
    b32 added = false;

    if (CompositeV *lhs = castAst(lhs0, CompositeV))
      if (CompositeV *rhs = castAst(rhs0, CompositeV))
    {
      if ((lhs->op->cat == AC_Union) &&
          (rhs->op->cat == AC_Union))
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

inline s32
getExplicitParamCount(Arrow *in)
{
  s32 out = 0;
  for (s32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!in->param_implied[param_id])
      out++;
  }
  return out;
}

// important: env can be modified, if the caller expects it.
// beware: Usually we mutate in-place, but we may also allocate anew.
forward_declare
internal Expression
buildExpression(Environment *env, Ast *in0, Value *expected_type)
{
  Expression out = {};
  b32 should_check_type = true;

  MemoryArena *arena = env->arena;
  switch (in0->cat)
  {
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

      if (Expression build_op = buildExpression(env, in->op, 0))
      {
        in->op = build_op.ast;

        if (ArrowV *signaturev = castAst(build_op.type, ArrowV))
        {
          Arrow *signature = signaturev->a;
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
                if (signature->param_implied[param_id])
                {
                  in->args[param_id] = &dummy_hole;
                }
                else
                {
                  assert(arg_id < explicit_param_count);
                  in->args[param_id] = supplied_args[arg_id++];
                }
              }
            }
            else
            {
              parseError(&in0->token, "too few arguments supplied, expected at least %d", explicit_param_count);
            }
          }

          if (noError())
          {
            Environment signature_env = *env;
            signature_env.arena = temp_arena;
            extendStack(&signature_env, in->arg_count, 0);
            Value **stack_frame = signature_env.stack->args;
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {// Typecheck/inference for the arguments. todo: the hole stuff is
              // kinda hard-coded only for the equality.
              if (in->args[arg_id] == &dummy_hole)
                stack_frame[arg_id] = 0;
              else
              {
                Ast *param_type0 = signature->param_types[arg_id];
                Value *norm_param_type = evaluate(signature_env, param_type0);
                if (Expression build_arg = buildExpression(env, in->args[arg_id], norm_param_type))
                {
                  in->args[arg_id] = build_arg.ast;
                  stack_frame[arg_id] = evaluate(*env, in->args[arg_id]);
                  if (norm_param_type == 0)
                  {
                    Variable *param_type = castAst(param_type0, Variable);
                    assert(param_type->stack_delta == 0);
                    stack_frame[param_type->id] = build_arg.type;

                    // write back to the input ast. (TODO: doesn't actually work
                    // since we don't handle the case where there are variables
                    // in the current arg's type)
                    Token token = newToken("<synthetic>");
                    Constant *synthetic = newAst(arena, Constant, &token);
                    synthetic->value = build_arg.type;
                    in->args[param_type->id] = &synthetic->a;
                  }
                }
              }
            }

            for (s32 arg_id = 0;
                 arg_id < in->arg_count && noError();
                 arg_id++)
            {
              if (in->args[arg_id] == &dummy_hole)
                parseError(in0, "Cannot fill hole in expression");
            }

            if (noError())
            {
              extendStack(env, in->arg_count, stack_frame);
              out.ast = in0;
              out.type = evaluate(*env, signature->out_type);
              unwindStack(env);
            }
          }
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          pushAttachment("got type", build_op.type);
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
        FunctionV *funv = newValue(arena, FunctionV, signature_v);
        // note: we only need that funv there for the type.
        funv->a = &dummy_function_under_construction;
        funv->token = in->a.token;

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
      if (Expression build_rewrite = buildExpression(env, in->proof, 0))
      {
        in->proof = build_rewrite.ast;
        b32 rule_valid = false;
        if (CompositeV *norm_rule = castAst(build_rewrite.type, CompositeV))
        {
          if (norm_rule->op == builtins.equal)
          {
            rule_valid = true;
            if (in->right_to_left)
              addRewrite(env, norm_rule->args[2], norm_rule->args[1]);
            else
              addRewrite(env, norm_rule->args[1], norm_rule->args[2]);
          }
        }
        if (!rule_valid)
        {
          parseError(in0, "invalid rewrite rule, can only be equality");
          pushAttachment("got", build_rewrite.type);
        }
      }

      out.ast  = in0;
      out.type = &builtins.True->v;  // #hack
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      out.ast = in0;
      out.type = builtins.Type;
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

        if (Union *form = castAst(subject_type, Union))
        {
          if (form->subset_count == case_count)
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
                if (Union *ctor = castAst(lookup, Union))
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
                      pushAttachment("expected type", subject_type);
                      pushAttachment("got type", ctor->v.type);
                    }
                  }
                  else
                  {
                    if (ArrowV *ctor_sig = castAst(ctor->v.type, ArrowV))
                    {
                      if (identicalB32(&getFormOf(ctor_sig->a->out_type)->v,
                                       &getFormOf(subject_type)->v))
                      {
                        if (param_count == ctor_sig->a->param_count)
                        {
                          addLocalBindings(&env, param_count, params->names, ctor_sig->a->param_types, false);
                          Value *pattern_type = evaluate(env, ctor_sig->a->out_type);
                          CompositeV *pattern = newValue(temp_arena, CompositeV, pattern_type);
                          pattern->op        = &ctor->v;
                          pattern->arg_count = param_count;
#if 1
                          pattern->args      = env.stack->args;
#else
                          pattern->args = pushArray(temp_arena, param_count, Value*);
                          for(s32 arg_id=0; arg_id < param_count; arg_id++)
                          {
                            pattern->args[arg_id] = &newValue(temp_arena, AccessorV, evaluate(env, ctor_sig->a->param_types[arg_id]))->v;
                          }
#endif
                          addRewrite(&env, norm_subject, &pattern->v);
                        }
                        else
                          parseError(ctor_token, "pattern has wrong number of parameters (expected: %d, got: %d)", ctor_sig->a->param_count, param_count);
                      }
                      else
                      {
                        parseError(ctor_token, "composite constructor has wrong return type");
                        pushAttachment("expected type", subject_type);
                        pushAttachment("got type", ctor_sig->a->out_type);
                      }
                    }
                    else
                    {
                      parseError(ctor_token, "expected a composite constructor");
                      pushAttachment("got type", &ctor_sig->v);
                    }
                  }

                  if (noError())
                  {
                    if (correct_bodies[ctor->s.set_id])
                    {
                      parseError(in->parsing->bodies[input_case_id], "fork case handled twice");
                      pushAttachment("constructor", &ctor->v);
                    }
                    else
                    {
                      correct_params[ctor->s.set_id].count = param_count;
                      correct_params[ctor->s.set_id].names = param_names;
                      Expression body = buildExpression(&env, in->parsing->bodies[input_case_id], common_type);
                      correct_bodies[ctor->s.set_id] = body.ast;
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
              in->union0    = form;
              in->params  = correct_params;
              in->bodies  = correct_bodies;

              out.ast  = in0;
              out.type = common_type;
            }
          }
          else
            parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                       form->subset_count, in->case_count);
        }
        else
        {
          parseError(in->subject, "cannot fork expression of type");
          pushAttachment("type", subject_type);
        }
      }
    } break;

    case AC_Accessor:
    {
      Accessor *in = castAst(in0, Accessor);
      if (Expression build_record = buildExpression(env, in->record, 0))
      {
        Ast   *record   = build_record.ast;
        Value *recordv0 = evaluate(*env, record);
        if (CompositeV *recordv = castAst(recordv0, CompositeV))
        {
          in->record = record;
          Arrow *op_type = castAst(recordv->op->type, ArrowV)->a;
          s32 param_count = op_type->param_count;
          s32 param_id;
          for (param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->member, op_type->param_names[param_id]))
            {
              in->param_id = param_id;
              out.ast = in0;
              break;
            }
          }

          if (param_id == op_type->param_count)
            tokenError(&in->member, "accessor has invalid member");
          else
          {// typing: curse you dependent type!
            extendStack(env, param_count, recordv->args);
            out.type = evaluate(*env, op_type->param_types[in->param_id]);
#if 0
            Value **stack_frame = env->stack->args;
            for (s32 param_id=0; param_id < param_count; param_id++)
            {
              Value *param_type = evaluate(*env, op_type->param_types[param_id]);
              if (param_id == in->param_id)
              {
                out.type = param_type;
                break;
              }
              else
              {
                // todo: does this need to exist
                AccessorV *paramv = newValue(temp_arena, AccessorV, param_type);
                paramv->param_id = param_id;
                paramv->record   = recordv;
                stack_frame[param_id] = &paramv->v;
              }
            }
#endif
            unwindStack(env);
          }
        }
        else
        {
          parseError(record, "cannot access a non-record");
          pushAttachment("record", recordv0);
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
        // normalize(*env, expected_type);
        pushAttachment("expected", norm_expected);
        pushAttachment("got", norm_actual);
      }
    }
  }

  if (noError())
  {
    assert(out.ast && out.type);
  }
  else
    out = {};
  return out;
}

inline Expression
buildExpressionGlobal(MemoryArena *arena, Ast *ast, Value *expected_type = 0)
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
  return parseExpression(arena, 0, 0).ast;
}

inline Expression
parseExpressionFull(MemoryArena *arena)
{
  return parseExpression(arena, 0, 0);
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
          // todo: do we really wanna constraint it to only appear in sequence?
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
parseArrowType(MemoryArena *arena, b32 is_record)
{
  Arrow *out = 0;
  pushContext;

  s32     param_count;
  Token  *param_names;
  Ast   **param_types;
  b32    *param_implied;
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
      param_implied = pushArray(arena, param_count, b32, true);

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
          if (param_name_token.text.chars[0] == '_')
          {
            param_implied[param_id] = true;
          }

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
          out->param_count   = param_count;
          out->param_names   = param_names;
          out->param_types   = param_types;
          out->param_implied = param_implied;
        }
      }
    }
    else
    {
      out = newAst(arena, Arrow, &marking_token);
      out->out_type = 0;
      out->param_count   = param_count;
      out->param_names   = param_names;
      out->param_types   = param_types;
      out->param_implied = param_implied;
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
parseUnionCase(MemoryArena *arena, Union *superset)
{
  pushContext;

  Value *out0;
  Token tag = nextToken();
  s32 subset_id = superset->subset_count++;
  if (isIdentifier(&tag))
  {
    if (optionalChar(':'))
    {
      if (Ast *parsed_type = parseExpressionFull(arena).ast)
      {
        Value *norm_type0 = evaluate(arena, parsed_type);
        b32 valid_type = false;
        if (Union *type = castAst(norm_type0, Union))
        {
          if (type == superset)
            valid_type = true;
        }
        else if (ArrowV *type = castAst(norm_type0, ArrowV))
        {
          if (getFormOf(type->a->out_type) == superset)
            valid_type = true;
        }

        if (valid_type)
        {
          Union *out = newValue(arena, Union, norm_type0);
          initSetNocheckin(out, &tag, subset_id);
          out0 = &out->v;
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
      if (superset->v.type == builtins.Set)
      {
        Union *out = newValue(arena, Union, &superset->v);
        initSetNocheckin(out, &tag, subset_id);
        out0 = &out->v;
      }
      else
        parseError(&tag, "constructors must construct a set member");
    }

    if (noError())
    {
      if (out0)
      {
        if (addGlobalBinding(&tag, out0))
          superset->subsets[subset_id] = &castAst(out0, Union)->s;
      }
      else
        invalidCodePath;
    }
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
      if (ArrowV *arrow = castAst(norm_type, ArrowV))
      {
        if (Constant *return_type = castAst(arrow->a->out_type, Constant))
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
    Union *superset = newSet(arena, Union, name, type);
    addGlobalBinding(name, &superset->v);

    if (requireChar('{', "open typedef body"))
    {
      Tokenizer tk_copy = *global_tokenizer;
      s32 expected_case_count = getCommaSeparatedListLength(&tk_copy);
      // NOTE: init here for recursive definition
      if (noError(&tk_copy))
      {
        Union **subsets = pushArray(arena, expected_case_count, Union*);
        superset->subset_count = 0;
        superset->subsets      = toSets(subsets);
        while (noError())
        {
          if (optionalChar('}'))
            break;
          else
          {
            parseUnionCase(arena, superset);
            if (!optionalChar(','))
            {
              requireChar('}', "to end the typedef; or you might want a comma ',' to delimit constructors");
              break;
            }
          }
        }

        if (noError())
        {
          assert(superset->subset_count == expected_case_count);
          assert(constantFromGlobalName(temp_arena, name));
        }
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
              auto interp_result = interpretFile(state, full_path, false);
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

          case Keyword_Print:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              Value *reduced = normalize(temp_arena, evaluate(temp_arena, parsing.ast));
              printAst(0, reduced, {.detailed=true});
              printToBuffer(0, ": ");
              printAst(0, parsing.type, {});
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
              printAst(0, parsing.type, {});
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
            else if (Function *fun = parseFunction(arena, name))
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

forward_declare
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
              printAst(0, (Ast*)attachment.p, {});
            } break;

            case AttachmentType_Value:
            {
              printAst(0, (Value*)attachment.p, {});
            } break;
          }
          if (attached_id != error->attachment_count-1) 
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
    {// Type and Set
      // Token superset_name = newToken("Type");
      builtins.Type = newValue(arena, BuiltinType, 0);
      builtins.Type->type = builtins.Type; // NOTE: circular types, might bite us
      if (!addGlobalBinding("Type", builtins.Type))
        invalidCodePath;

      builtins.Set = newValue(arena, BuiltinSet, builtins.Type);
      if (!addGlobalBinding("Set", builtins.Set))
        invalidCodePath;
    }

    {// more builtins
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), true);
      assert(success);

      ArrowV *equal_type = castAst(lookupGlobalName("equal_type"), ArrowV);
      builtins.equal = newValue(arena, BuiltinEqual, &equal_type->v);
      if (!addGlobalBinding("=", builtins.equal))
        invalidCodePath;

      builtins.True  = castAst(lookupGlobalName("True"), Union);
      builtins.truth = castAst(lookupGlobalName("truth"), Union);
      builtins.False = castAst(lookupGlobalName("False"), Union);
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
  Function   Function;
  FunctionV  FunctionV;
  StackRef   StackRef;
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
  MemoryArena *permanent_arena  = &permanent_arena_;

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

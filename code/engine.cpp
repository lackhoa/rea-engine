#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"

#define NULL_WHEN_ERROR(name) assert((bool)name == noError())

// NOTE: Eventually this will talk to the editor, but let's work in console mode for now.
// Important: all parsing must be aborted when the tokenizer encounters error.

#define VARIABLE_MATCHER(name) \
  b32 name(Environment env, Variable *in, void* opt)

typedef VARIABLE_MATCHER(variable_matcher);

#define SEARCH_VARIABLE                         \
internal b32                                    \
searchVariable(Environment env, Expression *in, variable_matcher *matcher, void *opt)

SEARCH_VARIABLE;

internal b32
searchVariableHalf(Environment env, Expression *in, variable_matcher *matcher, void *opt)
{
  b32 found = false;
  switch (in->cat)
  {
    case EC_Variable:
    {
      auto var = castExpression(in, Variable);
      found = matcher(env, var, opt);
    } break;

    case EC_Fork:
    {
      Fork *fork = castExpression(in, Fork);
      if (searchVariable(env, fork->subject, matcher, opt))
        found = true;
      else
      {
        for (s32 case_id = 0; case_id < fork->case_count; case_id++)
        {
          env.stack_offset++;
          if (searchVariable(env, fork->cases[case_id].body, matcher, opt))
          {
            found = true;
            break;
          }
        }
      }
    } break;

    case EC_Application:
    {
      auto app = castExpression(in, Application);
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

    case EC_ArrowType:
    {
      auto arrow = castExpression(in, ArrowType);
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
          if (searchVariable(env, arrow->params[param_id]->h.type, matcher, opt))
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

SEARCH_VARIABLE
{
  b32 found = false;
  if (in)
  {
    if (searchVariableHalf(env, in, matcher, opt))
      found = true;
    else
      found = searchVariable(env, in->type, matcher, opt);
  }
  return found;
}

VARIABLE_MATCHER(isFreeVariable)
{
  (void) opt;
  return (in->stack_delta - env.stack_offset > 0) && (in->stack_depth == 0);
}

inline b32
hasFreeVariable(Expression *in)
{
  Environment env = newEnvironment(global_temp_arena);
  return searchVariable(env, in, isFreeVariable, 0);
}

VARIABLE_MATCHER(isInstantiatedVariable)
{
  (void) opt; (void) env;
  return in->stack_depth != 0;
}

inline b32
hasInstantiated(Expression *in)
{
  Environment env = newEnvironment(global_temp_arena);
  return searchVariable(env, in, isInstantiatedVariable, 0);
}

VARIABLE_MATCHER(isDeeperVariable)
{
  (void) opt;
  return in->stack_depth > env.stack_depth;
}

inline b32
hasDeeperVariable(Environment env, Expression *in)
{
  return searchVariable(env, in, isDeeperVariable, 0);
}

inline b32
identicalB32(Expression *lhs, Expression *rhs)
{
  return identicalTrinary(lhs, rhs) == Trinary_True;
}

#if 0
inline b32
lessGrounded(Expression *a, Expression *b)
{
  s32 out = 0;
  switch (a->cat)
  {
    case EC_Variable:
    {
      switch (b->cat)
      {
        case EC_Variable: {out = false;} break;
        default:
      }
    } break;
  }
  return out;
}
#endif

inline b32
isCompositeConstructor(Expression *expression)
{
  auto app = castExpression(expression, Application);
  if (app)
    return app->op->cat == EC_Constructor;
  else
    return false;
}

#if 0
inline b32
canBeRewritten(Expression *in)
{
  return (in->cat == EC_Variable ||
          in->cat == EC_Application);
}
#endif

internal Trinary
compareExpressionList(Expression **lhs_list, Expression **rhs_list, s32 count)
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

// NOTE: values going in must be normalized
// NOTE: we need a trinary return value to detect if the comparison is false.
internal Trinary
identicalTrinary(Expression *lhs, Expression *rhs)
{
  Trinary out = Trinary_Unknown;

  if (lhs == rhs)
    out = Trinary_True;
  else if (lhs->cat == rhs->cat)
  {
    switch (lhs->cat)
    {
      case EC_Variable:
      {
        auto lvar = castExpression(lhs, Variable);
        auto rvar = castExpression(rhs, Variable);
        assert(lvar->stack_depth && rvar->stack_depth);
        if (lvar->stack_depth && rvar->stack_depth)
          out = Trinary_True;
      } break;

      case EC_Constructor:
      {
        if ((castExpression(lhs, Constructor))->id == (castExpression(rhs, Constructor))->id)
          out = Trinary_True;
        else
          out = Trinary_False;
      } break;

      case EC_ArrowType:
      {
        // todo: important: comparison of dependent types wouldn't work
        // if we compare the scopes. we can fix it by comparing
        // stack_delta (which we're not storing right now)
        auto larrow = castExpression(lhs,  ArrowType);
        auto rarrow = castExpression(rhs,  ArrowType);
        Trinary return_type_compare = identicalTrinary(larrow->return_type, rarrow->return_type);
        if (return_type_compare == Trinary_False)
          out = Trinary_False;
        else if (return_type_compare == Trinary_True)
        {
          auto param_count = larrow->param_count;
          if (rarrow->param_count == param_count)
          {
            auto lparam_types = pushArray(global_temp_arena, param_count, Expression*);
            auto rparam_types = pushArray(global_temp_arena, param_count, Expression*);

            for (s32 param_id = 0;
                 param_id < param_count;
                 param_id++)
            {
              lparam_types[param_id] = larrow->params[param_id]->h.type;
              rparam_types[param_id] = rarrow->params[param_id]->h.type;
            }

            out = compareExpressionList(lparam_types, rparam_types, param_count);
          }
          else
            out = Trinary_False;
        }
      } break;

      case EC_Fork:
      {
        out = Trinary_Unknown;
      } break;

      case EC_Application:
      {
        auto lapp = castExpression(lhs,  Application);
        auto rapp = castExpression(rhs,  Application);
        if ((lapp->op->cat == EC_Constructor)
            && (rapp->op->cat == EC_Constructor))
        {
          Trinary op_compare = identicalTrinary(lapp->op, rapp->op);
          if (op_compare == Trinary_False)
            out = Trinary_False;
          else
          {
            assert(op_compare == Trinary_True);
            assert(lapp->arg_count == rapp->arg_count);
            out = compareExpressionList(lapp->args, rapp->args, lapp->arg_count);
          }
        }
        Trinary op_compare = identicalTrinary(lapp->op, rapp->op);
        if (op_compare == Trinary_False)
        {
        }
      } break;

      case EC_Form:
      {
        out = Trinary_False;
      } break;

      default:
          todoIncomplete;
    }
  }
  else if (((lhs->cat == EC_Constructor) && isCompositeConstructor(rhs)) ||
           ((rhs->cat == EC_Constructor) && isCompositeConstructor(lhs)))
  {
    out = Trinary_False;
  }

  return out;
}

inline s32
switchCtorCount(Fork *myswitch)
{
  return castExpression(myswitch->subject->type, Form)->ctor_count;
}

internal void
printExpression(MemoryArena *buffer, Expression *exp, b32 detailed = false)
{
  unpackGlobals;

  b32 print_type = detailed ? true : false;
  switch (exp->cat)
  {
    case EC_Variable:
    {
      auto var = castExpression(exp, Variable);
      if (var->stack_depth)
        printToBuffer(buffer, "%.*s<%d>", var->name.length, var->name.chars, var->stack_depth);
      else
        printToBuffer(buffer, "%.*s[%d]", var->name.length, var->name.chars, var->stack_delta);
    } break;

    case EC_Application:
    {
      auto app = castExpression(exp, Application);

      printExpression(buffer, app->op);

      printToBuffer(buffer, "(");
      for (s32 arg_id = 0; arg_id < app->arg_count; arg_id++)
      {
        printExpression(buffer, app->args[arg_id]);
        if (arg_id < app->arg_count-1)
          printToBuffer(buffer, ", ");
      }
      printToBuffer(buffer, ")");
    } break;

    case EC_Fork:
    {
      Fork *fork = castExpression(exp, Fork);
      printToBuffer(buffer, "fork ");
      printExpression(buffer, fork->subject);
      printToBuffer(buffer, " {");
      auto form = castExpression(fork->subject->type, Form);
      for (s32 ctor_id = 0;
           ctor_id < form->ctor_count;
           ctor_id++)
      {
        ForkCase *casev = fork->cases + ctor_id;
        Constructor *ctor = form->ctors[ctor_id];
        switch (ctor->h.type->cat)
        {// print pattern
          case EC_Form:
          {
            printExpression(buffer, (Expression*)ctor);
          } break;

          case EC_ArrowType:
          {
            printExpression(buffer, (Expression*)ctor);
            printToBuffer(buffer, " ");
            ArrowType *signature = castExpression(ctor->h.type, ArrowType);
            for (s32 param_id = 0; param_id < signature->param_count; param_id++)
            {
              myprint(buffer, casev->params[param_id]->name);
              printToBuffer(buffer, " ");
            }
          } break;

          invalidCodePath;
        }

        printToBuffer(buffer, ": ");
        printExpression(buffer, casev->body);
        if (ctor_id != form->ctor_count-1)
          printToBuffer(buffer, ", ");
      }
      printToBuffer(buffer, "}");
    } break;

    case EC_Form:
    {
      auto mystruct = castExpression(exp, Form);
      myprint(buffer, mystruct->name);
    } break;

    case EC_Function:
    {
      print_type = false; // we print type in the following code
      auto proc = castExpression(exp, Function);
      myprint(buffer, proc->name);
      if (detailed)
      {
        printExpression(buffer, proc->h.type);
        printToBuffer(buffer, " { ");
        printExpression(buffer, proc->body);
        printToBuffer(buffer, " }");
      }
    } break;

    case EC_Constructor:
    {
      auto ctor = castExpression(exp, Constructor);
      myprint(buffer, ctor->name);
    } break;

    case EC_ArrowType:
    {
      auto arrow = castExpression(exp,  ArrowType);
      printToBuffer(buffer, "(");
      for (int param_id = 0;
           param_id < arrow->param_count;
           param_id++)
      {
        printExpression(buffer, (Expression*)arrow->params[param_id], true);
        if (param_id < arrow->param_count-1)
          printToBuffer(buffer, ", ");
      }
      printToBuffer(buffer, ") -> ");

      printExpression(buffer, arrow->return_type);
    } break;

    case EC_Builtin_identical:
    {
      printToBuffer(buffer, "identical");
    } break;

    case EC_Builtin_Set:
    {
      printToBuffer(buffer, "Set");
    } break;

    case EC_Builtin_Proc:
    {
      printToBuffer(buffer, "Proc");
    } break;

    case EC_Builtin_Prop:
    {
      printToBuffer(buffer, "Prop");
    } break;

    case EC_Builtin_Type:
    {
      printToBuffer(buffer, "Type");
    } break;

    case EC_Hole:
    {
      printToBuffer(buffer, "_");
    } break;

    default:
    {
      printToBuffer(buffer, "<unimplemented category: %u>", exp->cat);
    } break;
  }

  if (print_type)
  {
    printToBuffer(buffer, " : ");
    printExpression(buffer, exp->type);
  }
}

global_variable Bindings *global_bindings;

inline Bindings *
extendBindings(MemoryArena *arena, Bindings *outer)
{
  Bindings *out = pushStruct(arena, Bindings);
  for (int i = 0; i < arrayCount(out->table); i++)
  {// invalidate these slots
    Binding *slot = &out->table[i];
    slot->key.length = 0;
  }
  out->next    = outer;
  out->arena   = arena;
  return out;
}

struct LookupName { Binding* slot; b32 found; };

internal LookupName
lookupNameCurrentFrame(Bindings *bindings, String key, b32 add_if_missing)
{
  Binding *slot = 0;
  b32 found = false;
  u32 hash = stringHash(key);
  slot = bindings->table + (hash % arrayCount(bindings->table));
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

  LookupName out = { slot, found };
  return out;
}

inline b32
addBinding(Bindings *bindings, String key, Expression *value)
{
  auto lookup = lookupNameCurrentFrame(bindings, key, true);
  b32 succeed = false;
  if (!lookup.found)
  {
    lookup.slot->value = value;
    succeed = true;
  }
  return succeed;
}

inline b32
addGlobalName(String key, Expression *value)
{
  auto lookup = lookupNameCurrentFrame(global_bindings, key, true);
  b32 succeed = true;
  if (lookup.found)
    succeed = false;
  else
    lookup.slot->value = value;
  return succeed;
}

inline b32
addGlobalName(char *key, Expression *value)
{
  return addGlobalName(toString(key), value);
}

struct LookupNameRecursive { Expression *value; b32 found; };

inline LookupNameRecursive
lookupNameRecursive(MemoryArena *arena, Bindings *bindings, Token *token)
{
  Expression *value = {};
  b32 found = false;

  for (b32 stop = false, stack_delta = 0;
       !stop;
       stack_delta++)
  {
    LookupName lookup = lookupNameCurrentFrame(bindings, token->text, false);
    if (lookup.found)
    {
      found = true;
      stop = true;
      value = lookup.slot->value;
      if ((value->cat == EC_Variable) && (stack_delta != 0))
      {
        auto original_var = castExpression(value, Variable);
        assert(original_var->stack_delta == 0);
        auto var = pushStruct(arena, Variable);
        value = (Expression*) var;
        // todo: can we avoid this copying?
        *var = *original_var;
        var->stack_delta = stack_delta;
      }
    }
    else
    {
      if (bindings->next)
        bindings = bindings->next;
      else
        stop = true;
    }
  }

  LookupNameRecursive out = { value, found };
  return out;
}

inline b32
requireChar(Tokenizer *tk, char c, char *reason = 0)
{
  auto out = false;
  if (!reason)
    reason = "<no reason provided>";
  if (parsing(tk))
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
  if (parsing())
  {
    if (nextToken(tk).cat == tc)
      out = true;
    else
      tokenError(message);
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

internal b32
addGlobalNameBinding(String key, Expression *value)
{
  b32 succeed = false;
  LookupName lookup = lookupNameCurrentFrame(global_bindings, key, true);
  if (!lookup.found)
  {
    succeed = true;
    lookup.slot->value = value;
  }
  return succeed;
}

internal void
addBuiltinForm(MemoryArena *arena, char *name, const char **ctor_names, s32 ctor_count, Expression *type)
{
  Expression *exp = newExpressionNoCast(arena, Form, type);
  auto form_name = toString(name);
  if (!addGlobalNameBinding(form_name, exp))
    invalidCodePath;

  Form *form = castExpression(exp, Form);
  form->name = form_name;
  form->ctor_count = ctor_count;
  allocateArray(arena, form->ctor_count, form->ctors);

  for (auto ctor_id = 0; ctor_id < ctor_count; ctor_id++)
  {
    form->ctors[ctor_id] = newExpression(arena, Constructor, exp);
    auto ctor  = form->ctors[ctor_id];
    ctor->name = toString((char*)ctor_names[ctor_id]);
    ctor->id   = ctor_id;
    if (!addGlobalNameBinding(ctor->name, (Expression *)form->ctors[ctor_id]))
      invalidCodePath;
  }
}

struct OptionalU32 { b32 success; u32 value; };

#if 0
internal void
checkStack(Stack *stack)
{
#if REA_DIAGNOSTICS
  while (stack)
  {
    if (stack->args)
    {
      for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
      {
        auto arg = stack->args[arg_id];
        auto param_type = stack->signature->params[arg_id]->type;
        if (arg && (arg->cat != EC_Hole) && (param_type->cat != EC_Variable))
          assert(identicalB32(arg->type, param_type));
      }
    }
    stack = stack->next;
  }
#endif
}
#endif

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
  Expression *name(Environment env, Variable *in, void *opt)

typedef VARIABLE_TRANSFORMER(variable_transformer);

#define TRANSFORM_VARIABLES                     \
  inline Expression *                           \
  transformVariables(Environment env, Expression *in, variable_transformer *transformer, void *opt)

TRANSFORM_VARIABLES;

// note: this makes a copy (todo: #mem don't copy if not necessary)
inline Expression *
transformVariablesHalf(Environment env, Expression *in, variable_transformer *transformer, void *opt)
{
  Expression *out = 0;
  switch (in->cat)
  {
    case EC_Variable:
    {
      Variable *in_var = castExpression(in, Variable);
      out = transformer(env, in_var, opt);
    } break;

    case EC_Application:
    {
      Application *in_app  = castExpression(in, Application);
      Application *out_app = copyStruct(env.arena, in_app);
      out = (Expression*)out_app;
      out_app->op = transformVariables(env, in_app->op, transformer, opt);
      allocateArray(env.arena, out_app->arg_count, out_app->args);
      for (s32 arg_id = 0; arg_id < out_app->arg_count; arg_id++)
      {
        out_app->args[arg_id] = transformVariables(env, in_app->args[arg_id], transformer, opt);
      }
    } break;

    case EC_Fork:
    {
      Fork *in_fork  = castExpression(in, Fork);
      Fork *out_fork = copyStruct(env.arena, in_fork);
      out = (Expression*)out_fork;
      out_fork->subject = transformVariables(env, in_fork->subject, transformer, opt);
      allocateArray(env.arena, out_fork->case_count, out_fork->cases);
      Environment *outer_env = &env;
      for (s32 case_id = 0; case_id < out_fork->case_count; case_id++)
      {
        Environment env = *outer_env;
        env.stack_offset++;
        out_fork->cases[case_id].body = transformVariables(env, in_fork->cases[case_id].body, transformer, opt);
      }
    } break;

    case EC_Function:
    {
      Function *in_proc = castExpression(in, Function);
      Function *out_proc = copyStruct(env.arena, in_proc);
      out = (Expression*)out_proc;
      env.stack_offset++;
      out_proc->body = transformVariables(env, in_proc->body, transformer, opt);
    } break;

    default:
        out = in;
  }
  return out;
}

TRANSFORM_VARIABLES
{
  Expression *out = 0;
  if (in)
  {
    out       = transformVariablesHalf(env, in, transformer, opt);
    out->type = transformVariables(env, in->type, transformer, opt);
  }
  return out;
}

// todo #speed top-level functions don't need to be abstracted, since they
// don't contain any free variables.
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
  return (Expression*)out;
}

internal Expression *
abstractExpression(Environment env, Expression *in)
{
  return transformVariables(env, in, abstractInstantiated, 0);
}

// think of a function application
VARIABLE_TRANSFORMER(replaceCurrentLevelVariable)
{
  Expression **args = (Expression **)opt;
  if (env.stack_offset - in->stack_delta == 0)
    return args[in->id];
  else
    return (Expression*)in;
}

// think of a function application
internal Expression *
replaceCurrentLevel(Environment env, Expression *in, Expression **args)
{
  Expression *out = transformVariables(env, in, replaceCurrentLevelVariable, args);
  assert(identicalB32(in->type, out->type));
  return out;
}

// "in" is already normalized
internal Expression *
rewriteExpression(Environment *env, Expression *in)
{
  Expression *out = 0;
  // todo: find some way to early out in case expression can't be rewritten
  // if (canBeRewritten(in))
  // todo: #speed this is O(n)
  for (Rewrite *rewrite = env->rewrite;
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

internal Expression **
introduceVariables(Environment *env, s32 count, Variable **models)
{
  Variable **out = pushArray(env->temp_arena, count, Variable*);
  s32 stack_depth = ++env->stack_depth;
  for (s32 id = 0; id < count; id++)
  {
    Variable *model = models[id];
    Variable *dst = copyStruct(env->temp_arena, model);
    out[id] = dst;
    dst->stack_depth = stack_depth;
  }
  return (Expression**)out;
}

internal Expression **
introduceVariables(Environment *env, ArrowType *signature)
{
  return introduceVariables(env, signature->param_count, signature->params);
}

#if 0
internal Variable **
createAtoms(Environment *env, ArrowType *signature)
{
  return createAtoms(env, signature->param_count, signature->params);
}
#endif

#if 0
internal void
extendStack(Environment *env, ArrowType *signature, Expression **args)
{
  auto temp_arena = env->arena;

  if (!args)
    args = (Expression**)createAtoms(env, signature);

  Stack *stack     = pushStruct(arena, Stack);
  stack->next      = env->stack;
  stack->count     = signature->param_count;
  stack->signature = signature;
  stack->args      = args;

  env->stack       = stack;

#if REA_DIAGNOSTICS
  {
    for (s32 arg_id = 0; arg_id < stack->count; arg_id++)
    {
      assert(identicalB32(args[arg_id]->type, signature->params[arg_id]->header.type));
    }
  }
#endif
}
#endif

#if 0
internal void
extendStackEmpty(Environment *env)
{
  auto   arena = env->temp_arena;
  Stack *stack = pushStructZero(arena, Stack);
  stack->next  = env->stack;
  env->stack   = stack;
}
#endif

inline b32
hasType(Expression *in)
{
  b32 out;
  if (in->cat == EC_Builtin_Type)
    out = true;
  else
    out = (b32)in->type;
  return out;
}

// todo #speed don't pass the Environment in wholesale?
internal Expression *
normalize(Environment env, Expression *in)
{
  assert(!hasFreeVariable(in));
  assert(hasType(in));
  Expression *out = 0;
  unpackGlobals;

  switch (in->cat)
  {
    case EC_Application:
    {
      auto in_app = castExpression(in, Application);
      Expression **norm_args = pushArray(temp_arena, in_app->arg_count, Expression*);
      for (auto arg_id = 0;
           arg_id < in_app->arg_count;
           arg_id++)
      {
        Expression *in_arg = in_app->args[arg_id];
        norm_args[arg_id]  = normalize(env, in_arg);
      }

      Expression *norm_op = normalize(env, in_app->op);
      if (norm_op->cat == EC_Function)
      {// Function application
        Function  *proc     = castExpression(norm_op, Function);
        Expression *new_body = replaceCurrentLevel(env, proc->body, norm_args);
        out                  = normalize(env, new_body);
        assert(out->type);
      }
      else if (norm_op->cat == EC_Builtin_identical)
      {// special case for equality
        auto compare = identicalTrinary(norm_args[1], norm_args[2]);
        if (compare == Trinary_True)
          out = builtin_True;
        else if (compare == Trinary_False)
          out = builtin_False;
      }

      if (!out)
      {
        Application *out_app = copyStruct(env.arena, in_app);
        out = &out_app->h;

        out_app->op = norm_op;
        allocateArray(env.arena, out_app->arg_count, out_app->args);
        for (int arg_id = 0; arg_id < out_app->arg_count; arg_id++)
          out_app->args[arg_id] = norm_args[arg_id];
      }
    } break;

    case EC_Fork:
    {
      Fork *in_fork = castExpression(in, Fork);
      Expression *subject_norm = normalize(env, in_fork->subject);

      b32 subject_matched = false;
      switch (subject_norm->cat)
      {
        case EC_Constructor:
        {
          subject_matched = true;
          Constructor *ctor = castExpression(subject_norm, Constructor);
          out = normalize(env, in_fork->cases[ctor->id].body);
          assert(identicalB32(out->type, in->type));
        } break;

        case EC_Application:
        {
          Application *subject = castExpression(subject_norm, Application);
          if (Constructor *ctor = castExpression(subject->op, Constructor))
          {
            subject_matched = true;
            Expression *body = in_fork->cases[ctor->id].body;
            out = normalize(env, body);
            assert(identicalB32(out->type, in->type));

#if 0
            // note: since the fork case doesn't have its own signature, we
            // borrow the signature of the constructor.
            ArrowType *signature = castExpression(ctor->header.type, ArrowType);
            extendStack(&env, signature, subject->args);
#endif
          }
        } break;
      }

      if (!subject_matched)
        out = in;
    } break;

#if 0
    case EC_Function:
    {
      Procedure *in_proc  = castExpression(in, Procedure);
      Procedure *out_proc = copyStruct(arena, in_proc);
      out = (Expression*)out_proc;
      Environment new_env = env;
      new_env.stack_offset++;
      out_proc->body = normalize(arena, new_env, in_proc->body);
    } break;

    case EC_Variable:
    {
      Variable *in_var = castExpression(in, Variable);
      s32 stack_delta = in_var->stack_delta - env.stack_offset;
      if (in_var->atom)
        out = in;
      else if (stack_delta >= 0)
      {
        for (s32 id = 0; id < stack_delta; id++)
          stack = stack->next;
        assert(in_var->signature == stack->signature);
        out = stack->args[in_var->id];
        if (auto var = castExpression(out, Variable))
          assert(var->atom);
      }
      else
        out = in;
    } break;
#endif

    default:
    {
      out = in;
    } break;
  }

  auto out_before_rewritten = out; (void)out_before_rewritten;
  out = rewriteExpression(&env, out);
  assert(identicalB32(out->type, in->type));

  return out;
}

// todo: so what does the arena do exactly?
internal Expression *
normalizeStart(MemoryArena *arena, Expression *in)
{
  return normalize(newEnvironment(arena), in);
}

inline void
addRewrite(Environment *env, Expression *lhs, Expression *rhs)
{
  // todo #speed
  lhs = normalize(*env, lhs);
  rhs = normalize(*env, rhs);

  if (!identicalB32(lhs, rhs))
  {
    if ((lhs->cat == EC_Application)
        && (rhs->cat == EC_Application))
    {
      auto lapp = castExpression(lhs, Application);
      auto rapp = castExpression(rhs, Application);
      if ((lapp->op->cat == EC_Constructor)
          && (rapp->op->cat == EC_Constructor))
      {
        assert(identicalB32(lapp->op, rapp->op));
        for (s32 arg_id = 0; lapp->arg_count; arg_id++)
          addRewrite(env, lapp->args[arg_id], rapp->args[arg_id]);
      }
    }
    else
    {
      Rewrite *rewrite = newRewrite(env, lhs, rhs);
      env->rewrite = rewrite;
    }
  }
}

#define BUILD_EXPRESSION                        \
  internal Expression *                         \
  buildExpression(MemoryArena *arena, Bindings *bindings, Ast *ast0)

BUILD_EXPRESSION;

#if 0
inline b32
normalized(Environment env, Expression *in)
{
  Expression *norm = normalize(env, in);
  return identicalB32(in, norm);
}
#endif

// Expression accompanied by a stack, so that when you eval the expression in that stack it makes sense.
struct ExpressionWithStack
{
  Expression *expression;
  Stack      *stack;
};

internal b32
typecheck(Environment env, Expression *in0, Ast *ast0, Expression *instantiated_expected_type)
{
  unpackGlobals;
  b32 success = false;

  assert(!hasFreeVariable(instantiated_expected_type));
  if (in0->type)
  {
    if (instantiated_expected_type)
    {
      Expression *norm_expected_type = normalize(env, instantiated_expected_type);
      Expression *in_type = normalize(env, in0->type);
      if (!identicalB32(norm_expected_type, in_type))
      {
        parseError(ast0, "expression has wrong type");
        Expression *abstract_expected_type = abstractExpression(env, norm_expected_type);
        pushAttachment("expected", abstract_expected_type);
        Expression *abstract_in_type = abstractExpression(env, in_type);
        pushAttachment("got", abstract_in_type);
      }
    }
  }
  else
  {
    switch (in0->cat)
    {
      case EC_Fork:
      {
        Fork        *fork      = castExpression(in0, Fork);
        AstFork     *ast_fork  = castAst(ast0, AstFork);
        Environment *outer_env = &env;

        Form *form = castExpression(fork->subject->type, Form);

        Expression *instantiated_common_type = instantiated_expected_type;
        for (s32 case_id = 0;
             case_id < fork->case_count && noError();
             case_id++)
        {
          Environment  env  = *outer_env;

          ForkCase *casev    = fork->cases + case_id;
          Ast      *ast_body = ast_fork->bodies[case_id];

          Constructor *ctor     = form->ctors[case_id];
          Expression  *ctor_exp = (Expression*)ctor;
          switch (ctor->h.cat)
          {
            case EC_Constructor:
            {
              addRewrite(&env, fork->subject, ctor_exp);
              introduceVariables(&env, 0, 0);
            } break;

            case EC_Application:
            {
              ArrowType    *signature = castExpression(ctor->h.type, ArrowType);
              Expression  **params    = (Expression**)introduceVariables(&env, signature->param_count, casev->params);
              Application  *pattern   = newExpression(env.temp_arena, Application, signature->return_type);
              initApplication(pattern, ctor_exp, signature->param_count, params);

              addRewrite(&env, fork->subject, (Expression*)pattern);
            } break;

            default:
                invalidCodePath;
          }

          // "expected_type" might normalize to different things in different forks.
          typecheck(env, casev->body, ast_body, instantiated_common_type);
          if (!instantiated_common_type)
          {
            // fork body has more specific type than outer scope???
            assert(!hasDeeperVariable(*outer_env, instantiated_common_type));
            instantiated_common_type = normalize(env, casev->body->type);
          }
        }

        if (noError())
        {
          in0->type = abstractExpression(env, instantiated_common_type);
          assert(in0->type);
        }
      } break;

      case EC_Function:
      {
        // You probably always want to have type annotations for procedures.
        assert(instantiated_expected_type);

        Function  *in        = castExpression(in0, Function);
        ArrowType *signature = castExpression(instantiated_expected_type, ArrowType);

        Expression **new_vars    = introduceVariables(&env, signature);
        Expression  *return_type = replaceCurrentLevel(env, signature->return_type, new_vars);
        Expression  *body        = replaceCurrentLevel(env, in->body, new_vars);
        if (typecheck(env, body, ast0, return_type))
        {
          in0->type      = abstractExpression(env, instantiated_expected_type);
          in->body->type = body->type;
        }
      } break;

      case EC_Application:
      {
        Application *app       = castExpression(in0, Application);
        AstBranch   *branch    = castAst(ast0, AstBranch);
        s32          arg_count = app->arg_count;

        if (typecheck(env, app->op, branch->op, 0))
        {
          if (ArrowType *signature = castExpression(app->op->type, ArrowType))
          {
            if (signature->param_count == arg_count)
            {
              for (int arg_id = 0;
                   (arg_id < signature->param_count) && noError();
                   arg_id++)
              {
                Expression *arg     = app->args[arg_id];
                Ast        *arg_ast = branch->args[arg_id];
                Variable   *param   = signature->params[arg_id];

                if (arg->cat == EC_Hole)
                {}
                else if (param->h.type->cat == EC_Variable)
                {
                  Variable *param_type = castExpression(param->h.type, Variable);
                  Expression *lookup = app->args[param_type->id];
                  if (param_type->stack_delta != 0)
                    todoIncomplete;  // don't know what happens here.

                  if (lookup->cat == EC_Hole)
                  {
                    typecheck(env, arg, arg_ast, 0);
                    if (identicalB32(param_type->h.type, arg->type->type))
                    {
                      // NOTE: here we mutate the expression by writing back to
                      // the arg list.
                      app->args[param_type->id] = arg->type;
                    }
                    else
                    {
                      parseError(ast0, "the type of argument %d has wrong type", arg_id);
                      pushAttachment("got", arg->type->type);
                      pushAttachment("expected", param_type->h.type);
                    }
                  }
                  else
                    typecheck(env, arg, arg_ast, lookup);
                }
                else
                  typecheck(env, arg, arg_ast, param->h.type);
              }

              if (noError())
              {
                in0->type = signature->return_type;
                // now we have the type, recurse to avoid the cut&paste
                typecheck(env, in0, ast0, instantiated_expected_type);
              }
            }
            else
              parseError(ast0, "incorrect arg count: %d (procedure expected %d)", arg_count, signature->param_count);
          }
          else
          {
            parseError(branch->op, "operator must have an arrow type");
            pushAttachment("got type", app->op->type);
          }
        }
      } break;

      case EC_ArrowType:
      {
        ArrowType    *in  = castExpression(in0, ArrowType);
        AstArrowType *ast = castAst(ast0, AstArrowType);
        introduceVariables(&env, in);
        if (typecheck(env, in->return_type, ast->return_type, 0))
        {
          in0->type = builtin_Fun;
        }
      } break;

      default:
      {
        parseError(ast0, "#internal this expression should already have type");
      } break;
    }
  }

  if (noError())
  {
    assert(in0->type);
    assert(!hasInstantiated(in0->type));
    success = true;
  }
  return success;
}

internal b32
typecheck(MemoryArena *arena, Expression *in, Ast *ast, Expression *expected_type)
{
  return typecheck(newEnvironment(arena), in, ast, expected_type);
}

// todo: check that every case has been filled in
internal Fork *
buildFork(MemoryArena *arena, Bindings *outer_bindings, AstFork *ast)
{
  unpackGlobals;
  pushContext;
  Fork *out = 0;

  Expression *subject = buildExpression(arena, outer_bindings, ast->subject);

  if (parsing())
  {
    if (subject->type)
    {
      if (Form *subject_form = castExpression(subject->type, Form))
      {
        s32 case_count = ast->case_count;
        if (subject_form->ctor_count == case_count)
        {
          if (case_count == 0)
            parseError((Ast*)ast, "todo: cannot assign type to empty fork");
          else
          {
            ForkCase *cases = pushArrayZero(arena, case_count, ForkCase);
        
            for (s32 input_case_id = 0;
                 (input_case_id < case_count) && parsing();
                 input_case_id++)
            {
              Bindings *bindings = extendBindings(global_temp_arena, outer_bindings);

              Ast *ast_pattern = ast->patterns[input_case_id];
              Constructor *ctor = 0;
              Variable **params = 0;
              pushContextName("transform switch case pattern");
              switch (ast_pattern->cat)
              {
                case AC_AstLeaf:
                {
                  params = 0;
                  Expression *pattern = buildExpression(temp_arena, outer_bindings, ast_pattern);
                  if (parsing())
                  {
                    ctor = castExpression(pattern, Constructor);
                    if (ctor)
                    {
                      if (!identicalB32(pattern->type, subject->type))
                      {
                        parseError(ast_pattern, "constructor of wrong type (todo: support flexible return type)");
                        pushAttachment("expected type", subject->type);
                        pushAttachment("got type", pattern->type);
                      }
                    }
                    else
                      parseError(ast_pattern, "expected a member constructor");
                  }
                } break;

                case AC_AstBranch:
                {
                  AstBranch *branch = castAst(ast_pattern, AstBranch);
                  Expression *op = buildExpression(arena, outer_bindings, branch->op);

                  if (parsing())
                  {
                    ctor = castExpression(op, Constructor);
                    if (ctor)
                    {
                      if (ArrowType *ctor_sig = castExpression(op->type, ArrowType))
                      {
                        if (identicalB32(ctor_sig->return_type, subject->type))
                        {
                          s32 param_count = branch->arg_count;
                          if (param_count == ctor_sig->param_count)
                          {
                            allocateArrayZero(arena, param_count, params);
                            for (s32 param_id = 0; param_id < param_count; param_id++)
                            {// MARK: loop over pattern variables
                              Ast *ast_arg = branch->args[param_id];
                              if (AstLeaf *arg = castAst(ast_arg, AstLeaf))
                              {
                                String param_name = arg->h.token.text;
                                auto lookup = lookupNameCurrentFrame(bindings, param_name, true);
                                if (lookup.found)
                                  tokenError("reused parameter name");
                                else
                                {
                                  assert(ctor_sig->params[param_id]);
                                  // pattern variable: only the name is different
                                  Variable *param_src = ctor_sig->params[param_id];
                                  params[param_id] = copyStruct(arena, param_src);
                                  Variable *param = params[param_id];
                                  param->name = param_name;
                                  lookup.slot->value = (Expression*)param;
                                }
                              }
                              else
                                parseError(ast_arg, "expected pattern variable");
                            }
                          }
                          else
                            parseError(ast_pattern, "pattern has wrong amount of parameters (expected: %d, got: %d)", ctor_sig->param_count, param_count);
                        }
                        else
                        {
                          parseError(ast_pattern, "constructor has wrong type (todo: support more flexible return type)");
                          pushAttachment("expected type", subject->type);
                          pushAttachment("got type", ctor_sig->return_type);
                        }
                      }
                      else
                      {
                        parseError(branch->op, "expected a composite constructor");
                        pushAttachment("got type", op->type);
                      }
                    }
                    else
                      parseError(ast_pattern, "expected a constructor");
                  }
                } break;
              }
              popContext();

              Expression *body = 0;
              if (parsing())
              {
                pushContextName("fork case body building");
                Ast *ast_body = ast->bodies[input_case_id];
                body = buildExpression(arena, bindings, ast_body);
                popContext();
              }

              if (parsing())
                initForkCase(cases + ctor->id, body, params);
            }

            if (parsing())
            {
              out = newExpression(arena, Fork, 0);
              initFork(out, subject, case_count, cases);
            }
          }
        }
        else
          parseError((Ast*)ast, "wrong number of cases, expected: %d, got: %d",
                     subject_form->ctor_count, ast->case_count);
      }
      else
        parseError(ast->subject, "cannot fork this expression");
    }
    else
      parseError(ast->subject, "todo: fork subject has unknown type at the time of expression building");
  }

  popContext();
  return out;
}

struct ExpressionAndAst
{
  Expression *expression;
  Ast *ast;
  operator bool() { return (bool)ast; }
};

inline ExpressionAndAst
parseExpressionAndTypecheck(MemoryArena *arena, Bindings *bindings, Expression *expected_type)
{
  unpackGlobals;
  ExpressionAndAst out = {};
  if (Ast *ast = parseExpressionToAst(global_temp_arena))
  {
    if (Expression *expression = buildExpression(arena, bindings, ast))
    {
      if (typecheck(newEnvironment(arena), expression, ast, expected_type))
      {
        out.expression = expression;
        out.ast        = ast;
      }
    }
  }

  NULL_WHEN_ERROR(out);

  return out;
}

inline ExpressionAndAst
parseExpressionInferType(MemoryArena *arena, Bindings *bindings)
{
  return parseExpressionAndTypecheck(arena, bindings, 0);
}

inline Expression *
parseExpression(MemoryArena *arena)
{
  return parseExpressionInferType(arena, global_bindings).expression;
}

inline ExpressionAndAst
parseExpressionReturnAst(MemoryArena *arena)
{
  return parseExpressionInferType(arena, global_bindings);
}

BUILD_EXPRESSION
{
  Expression *out0 = 0;

  switch (ast0->cat)
  {
    case AC_AstLeaf:
    {
      AstLeaf *ast = castAst(ast0, AstLeaf);
      if (equal(&ast->h.token, '_'))
        out0 = hole_expression;
      else
      {
        auto lookup = lookupNameRecursive(arena, bindings, &ast->h.token);
        if (lookup.found)
          out0 = lookup.value;
        else
          parseError(ast0, "unbound identifier in expression");
      }
    } break;

    case AC_AstBranch:
    {
      AstBranch *ast = castAst(ast0, AstBranch);
      Expression *op = buildExpression(arena, bindings, ast->op);
      if (parsing())
      {
        s32 arg_count = ast->arg_count;
        Expression **args = pushArray(arena, arg_count, Expression*);
        for (s32 arg_id = 0;
             (arg_id < arg_count) && parsing();
             arg_id++)
        {
          args[arg_id] = buildExpression(arena, bindings, ast->args[arg_id]);
        }
        if (parsing())
        {
          Application *app = newExpression(arena, Application, 0);
          initApplication(app, op, arg_count, args);
          out0 = (Expression*)app;
        }
      }
    } break;

    case AC_AstArrowType:
    {
      AstArrowType *ast = castAst(ast0, AstArrowType);
      ArrowType *out = newExpression(arena, ArrowType, 0);

      // introduce own bindings
      Bindings *outer_bindings = bindings;
      Bindings *bindings       = extendBindings(arena, outer_bindings);

      // build parameters
      Variable **params = pushArray(arena, ast->param_count, Variable*);
      for (s32 param_id = 0;
           param_id < ast->param_count && noError();
           param_id++)
      {
        Parameter *ast_param = ast->params + param_id;
        if (Expression *param_type = buildExpression(arena, bindings, ast_param->type))
        {
          Variable *param = params[param_id] = newExpression(arena, Variable, param_type);
          initVariable(param, ast_param->name, param_id, out);
          addBinding(bindings, param->name, (Expression*)param);
        }
      }

      // parse return type
      if (Expression *return_type = buildExpression(arena, bindings, ast->return_type))
      {
        initArrowType(out, ast->param_count, params, return_type);
        out0 = (Expression *)out;
      }
    } break;

    case AC_AstFork:
    {
      out0 = (Expression *)buildFork(arena, bindings, castAst(ast0, AstFork));
    } break;
  }

  NULL_WHEN_ERROR(out0);
  return out0;
}

inline Expression *
buildExpressionGlobal(MemoryArena *arena, Ast *ast)
{
  return buildExpression(arena, global_bindings, ast);
}

internal AstFork *
parseFork(MemoryArena *arena)
{
  unpackGlobals;
  pushContext;

  AstFork *out = 0;
  Token token = tk->last_token;
  Ast *subject = parseExpressionToAst(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *tk;
    s32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (parsing(&tk_copy))
    {
      s32 actual_case_count = 0;
      Ast **patterns = pushArray(arena, case_count, Ast*);
      Ast **bodies   = pushArray(arena, case_count, Ast*);

      for (b32 stop = false;
           !stop && parsing();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContextName("fork case");
          auto input_case_id = actual_case_count++;
          patterns[input_case_id] = parseExpressionToAst(arena);
          if (parsing())
          {
            pushContextName("fork body");
            if (requireChar(':', "syntax: CASE: BODY"))
            {
              auto body = parseExpressionToAst(arena);
              bodies[input_case_id] = body;
              if (parsing())
              {
                if (!optionalChar(','))
                {
                  requireChar('}', "to end fork expression; or you might need ',' to end the fork case");
                  stop = true;
                }
              }
            }
            popContext();
          }
          popContext();
        }
      }

      if (noError())
      {
        assert(case_count == actual_case_count);
        out = newAstFork(arena, &token, subject, case_count, patterns, bodies);
      }
    }
  }
  popContext();

  return out;
}

internal ParameterList *
parseParameterList(MemoryArena *arena)
{
  unpackGlobals;
  pushContext;
  ParameterList *out = 0;

  if (requireChar('('))
  {
    Tokenizer tk_copy = *tk;
    s32 param_count = getCommaSeparatedListLength(&tk_copy);
    if (parsing(&tk_copy))
    {
      Parameter *params = pushArray(arena, param_count, Parameter);

      s32 parsed_param_count = 0;
      s32 typeless_run = 0;
      Token typeless_token;
      for (b32 stop = false;
           !stop && parsing();
           )
      {
        Token param_name_token = nextToken();
        if (equal(&param_name_token, ')'))
          stop = true;

        else if (isIdentifier(&param_name_token))
        {
          s32 param_id = parsed_param_count++;

          if (optionalChar(tk, ':'))
          {
            if (Ast *param_type = parseExpressionToAst(arena))
            {
              initParameter(params + param_id, &param_name_token, param_type);
              if (typeless_run)
              {
                for (s32 offset = 1; offset <= typeless_run; offset++)
                  params[param_id - offset].type = param_type;
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
            initParameter(params + param_id, &param_name_token, 0);
          }
          else
            stop = true;
        }
        else
          tokenError("expected parameter name");
      }
      if (parsing())
      {
        assert(parsed_param_count == param_count);
        if (typeless_run)
        {
          parseError(&typeless_token, "please provide types for all parameters");
          // TODO: print out "typeless_token"
        }
        else
        {
          out = pushStruct(arena, ParameterList);
          *out = ParameterList{param_count, params};
        }
      }
    }
  }

  popContext();
  assert(noError() == (bool)out);
  return out;
}

internal AstArrowType *
parseArrowType(MemoryArena *arena)
{
  unpackGlobals;
  AstArrowType *out = 0;
  pushContext;

  if (ParameterList *params = parseParameterList(arena))
  {
    if (requireCategory(TC_Arrow, "syntax: (...) -> ReturnType"))
    {
      Token arrow_token = tk->last_token;
      if (Ast *return_type = parseExpressionToAst(arena))
      {
        out = newAst(arena, AstArrowType, &arrow_token);
        initAstArrowType(out, params->count, params->items, return_type);
      }
    }
  }

  popContext();
  assert(noError() == (bool)out);
  return out;
}

// todo: this "constructor" is quite ridiculously involved.
internal AstBranch *
newAstBranch(MemoryArena *arena, Ast *op, s32 arg_count, Ast **args)
{
  AstBranch *out = newAst(arena, AstBranch, &op->token);

  if (AstLeaf *op_leaf = castAst(op, AstLeaf))
  {
    // todo: fake equality macro
    if (equal(&op_leaf->h.token, '='))
    {
      assert(arg_count == 2);
      // todo: omg manually creating token...
      Token identical_token = newToken(toString("identical"), 0, 0, TC_Alphanumeric);
      Token hole_token = newToken(toString("_"), 0, 0, TC_Alphanumeric);

      op          = (Ast*)newAstLeaf(arena, &identical_token);
      arg_count   = 3;

      Ast **new_args = pushArray(arena, arg_count, Ast*);
      new_args[0] = (Ast*)newAstLeaf(arena, &hole_token);
      new_args[1] = args[0];
      new_args[2] = args[1];
      args        = new_args;
    }
  }

  out->arg_count = arg_count;
  out->args      = args;
  out->op        = op;

  return out;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  unpackGlobals;
  pushContext;

  Ast *out = 0;
  Token token1 = nextToken(tk);
  if (Keyword keyword = matchKeyword(&token1))
  {
    switch (keyword)
    {
      case Keyword_Fork:
      {
        out = (Ast *)parseFork(arena);
      } break;

      default:
          tokenError("keyword not part of expression");
    }
  }
  else if (isIdentifier(&token1))
  {
    out = (Ast *)newAstLeaf(arena, &token1);
  }
  else if (equal(&token1, '('))
  {
    out = parseExpressionToAst(arena);
    requireChar(')');
  }
  else
    tokenError("expected start of expression");

  if (parsing())
  {
    Token funcall = peekNext(tk);
    if (equal(&funcall, '('))
    {// function call syntax, let's keep going
      nextToken();
      Ast *op = out;

      Tokenizer tk_copy = *tk;
      s32 expected_arg_count = getCommaSeparatedListLength(&tk_copy);

      if (parsing(&tk_copy))
      {
        auto args = pushArray(arena, expected_arg_count, Ast*);
        AstBranch *branch = newAstBranch(arena, op, expected_arg_count, args);
        out = (Ast *)branch;
        s32 parsed_arg_count = 0;
        for (s32 stop = false;
             parsing () && !stop;
             )
        {
          if (optionalChar(')'))
            stop = true;
          else
          {
            s32 arg_id = parsed_arg_count++;
            auto arg = parseExpressionToAst(arena);
            if (parsing())
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
        if (parsing())
        {
          assert(parsed_arg_count == expected_arg_count);
        }
      }
    }
  }

  if (parsing()) {assert(out);} else out = 0;

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
  unpackGlobals;
  pushContext;

  Ast *out = 0;
  if (seesArrowExpression())
  {
    out = (Ast*)parseArrowType(arena);
  }
  else
  {
    if (Ast *operand = parseOperand(arena))
    {
      // (a+b) * c
      //     ^
      for (b32 stop = false; !stop && parsing();)
      {
        Token op_token = peekNext();
        if (isIdentifier(&op_token))
        {// infix operator syntax
          // (a+b) * c
          //        ^
          AstLeaf *op = newAstLeaf(arena, &op_token);
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
              operand = (Ast*)newAstBranch(arena, (Ast*)op, 2, args);
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
  popContext();
  return out;
}

inline Ast *
parseExpressionToAst(MemoryArena *arena)
{
  return parseExpressionToAstMain(arena, ParseExpressionOptions{});
}

internal Constructor *
parseConstructorDef(MemoryArena *arena, Form *form, s32 ctor_id)
{
  unpackGlobals;
  pushContext;
  Constructor *out = newExpression(arena, Constructor, 0);

  Token ctor_token = nextToken(tk);
  if (isIdentifier(&ctor_token))
  {
    LookupName ctor_lookup = lookupNameCurrentFrame(global_bindings, ctor_token.text, true);
    if (ctor_lookup.found)
      tokenError("redefinition of constructor name");
    else
    {
      out->id   = ctor_id;
      out->name = ctor_token.text;

      ctor_lookup.slot->value = (Expression*)out;

      if (optionalChar('('))
      {
        Tokenizer tk_copy = *tk;
        auto expected_arg_count = getCommaSeparatedListLength(&tk_copy);
        if (parsing(&tk_copy))
        {
          ArrowType *signature = newExpression(arena, ArrowType, builtin_Fun);
          Variable **params = pushArray(arena, expected_arg_count, Variable*);
          s32 param_count = 0;
          for (s32 stop = false; !stop && parsing(); )
          {
            if (optionalChar(')'))
              stop = true;
            else
            {
              Expression *param_type = parseExpression(arena);
              if (parsing())
              {
                s32       param_id = param_count++;
                Variable *param    = newExpression(arena, Variable, param_type);

                initVariable(param, toString("no_name"), param_id, signature);

                signature->params[param_id] = param;
                if (!optionalChar(','))
                {
                  requireChar(')', "expected ')' or ','");
                  stop = true;
                }
              }
            }
          }
          if (parsing())
          {
            assert(param_count == expected_arg_count);
            // NOTE: we assume that "mystruct" is a well-typed expression.
            // Right now all constructors return mystruct, but in future they
            // can return whatever.
            initArrowType(signature, param_count, params, (Expression*)form);
            out->h.type = (Expression*)signature;
          }
        }
      }
      else
        out->h.type = (Expression*)form;
    }
  }
  else
    tokenError("expected an identifier as constructor name");

  if (parsing()) {assert(out);} else out = 0;
  popContext();
  return out;
}

internal void
parseTypedef(MemoryArena *arena)
{
  unpackGlobals;
  pushContext;

  Token type_name = nextToken(tk);
  if (isIdentifier(&type_name))
  {
    // NOTE: the type is in scope of its own constructor.
    LookupName lookup = lookupNameCurrentFrame(global_bindings, type_name.text, true);
    if (lookup.found)
      tokenError("redefinition of type");
    else if (requireChar(':'))
    {
      Expression *type_of_type = parseExpression(arena);
      if (parsing())
      {
        Form *form = newExpression(arena, Form, type_of_type);
        lookup.slot->value = (Expression*)form;

        form->name = type_name.text;

        requireChar(tk, '{');

        Tokenizer tk_copy = *tk;
        s32 expected_case_count = getCommaSeparatedListLength(&tk_copy);
        if (parsing())
        {
          allocateArray(arena, expected_case_count, form->ctors);

          for (s32 stop = 0;
               !stop && parsing();)
          {
            if (optionalChar('}'))
              stop = true;
            else
            {
              s32 ctor_id = form->ctor_count++;
              form->ctors[ctor_id] = parseConstructorDef(arena, form, ctor_id);
              if (!optionalChar(','))
              {
                requireChar('}', "to end the typedef; or you might want a comma ',' to delimit constructors");
                stop = true;
              }
            }
          }

          if (parsing())
          {
            assert(form->ctor_count == expected_case_count);
            assert(lookupNameCurrentFrame(global_bindings, type_name.text, false).found);
          }
        }
      }
    }
  }

  popContext();
}

// todo this is currently only top level definition
internal void
parseFunctionDefinition(MemoryArena *arena, Token *name)
{
  unpackGlobals;
  pushContext;

  assert(isIdentifier(name));
  if (equal(name, "andWithFalse"))
  {
    breakhere;
  }
  auto define_slot = lookupNameCurrentFrame(global_bindings, name->text, true);
  if (define_slot.found)
    tokenError("re-definition");
  else if (auto [signature0, signature_ast] = parseExpressionReturnAst(arena))
  {
    if (ArrowType *signature = castExpression(signature0, ArrowType))
    {
      // "signature" is only an annotation, "fun" hasn't earned that type yet.
      Function *fun = newExpression(arena, Function, 0);
      define_slot.slot->value = (Expression*)fun;

      // note: we have to rebuild the function's local bindings (todo: parse
      // signature+body together?)
      Bindings *local_bindings = extendBindings(arena, global_bindings);
      for (s32 param_id = 0;
           param_id < signature->param_count;
           param_id++)
      {
        Variable *param = signature->params[param_id];
        b32 add = addBinding(local_bindings, param->name, (Expression*)param);
        assert(add);
      }

      if (requireChar('{', "open function body"))
      {
        if (Ast *body_ast = parseExpressionToAst(arena))
        {
          Expression *body = buildExpression(arena, local_bindings, body_ast);
          if (requireChar('}'))
          {
            initFunction(fun, name->text, body);
            if (typecheck(arena, (Expression*)fun, body_ast, (Expression*)signature))
            {
              assert(fun->body->type);
            }
          }
        }
      }
    }
    else
      parseError(signature_ast, "function definition requires an arrow type");
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
  FileList *file_list;
};

internal b32
interpretFile(EngineState *state, MemoryArena *arena, FilePath input_path, b32 is_root_file = false);

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state, MemoryArena *arena)
{
  pushContext;
  auto temp_arena = global_temp_arena;

  while (parsing())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
#endif

    Token token = nextToken(); 
    if (equal(&token, '\0'))
    {}
    else if (equal(&token, '#'))
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
            char *load_path = myprint(path_buffer, global_tokenizer->directory);
            myprint(path_buffer, file.text);
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
              auto interp_result = interpretFile(state, arena, full_path);
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
          case Keyword_Typedef:
              parseTypedef(arena);
              break;

          case Keyword_Print:
          {
            Expression *exp = parseExpression(temp_arena);
            if (parsing())
            {
              auto buffer = subArena(temp_arena, 256);
              Expression *reduced = normalizeStart(temp_arena, exp);
              printExpression(&buffer, reduced, true);
              printf("%s\n", buffer.base);
            }
            requireChar(';');
          } break;

          case Keyword_PrintRaw:
          {
            Expression *exp = parseExpression(temp_arena);
            if (parsing())
            {
              auto buffer = subArena(temp_arena, 256);
              printExpression(&buffer, exp, true);
              printf("%s\n", buffer.base);
            }
            requireChar(';');
          } break;

          case Keyword_Check:
          {
            pushContextName("typecheck");
            Ast *ast = parseExpressionToAst(temp_arena);
            
            if (Expression *exp = buildExpressionGlobal(temp_arena, ast))
            {
              if (optionalChar(':'))
              {
                if (Expression *expected_type = parseExpression(temp_arena))
                  typecheck(temp_arena, exp, ast, expected_type);
              }
              else
                typecheck(temp_arena, exp, ast, 0);
            }
            
            requireChar(';');
            popContext();
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
            Expression *value = parseExpression(arena);
            Expression *norm  = normalizeStart(arena, value);
            if (parsing())
            {
              if (!addGlobalName(name->text, norm))
                tokenError(name, "redefinition of global name");
            }
            requireChar(';');
            popContext();
          } break;

          case TC_DoubleColon:
          {
            parseFunctionDefinition(arena, name);
          } break;

          default:
          {
            tokenError("unexpected token");
          } break;
        }
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

internal void
initializeEngine(MemoryArena *arena)
{
  global_temp_arena_ = subArena(arena, megaBytes(2));
  global_temp_arena  = &global_temp_arena_;
  allocate(arena, global_bindings);
  global_bindings->arena = arena;

  addGlobalName("identical", builtin_identical);
  addGlobalName("Set"      , builtin_Set);
  addGlobalName("Prop"     , builtin_Prop);
  addGlobalName("Proc"     , builtin_Fun);

  const char *true_members[] = {"truth"};
  addBuiltinForm(arena, "True", true_members, 1, builtin_Set);
  builtin_True  = lookupNameCurrentFrame(global_bindings, toString("True"), false).slot->value;
  builtin_truth = lookupNameCurrentFrame(global_bindings, toString("truth"), false).slot->value;

  addBuiltinForm(arena, "False", (const char **)0, 0, builtin_Set);
  builtin_False = lookupNameCurrentFrame(global_bindings, toString("False"), false).slot->value;
}

internal b32
interpretFile(EngineState *state, MemoryArena *arena, FilePath input_path, b32 is_root_file)
{
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

    parseTopLevel(state, arena);
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
        printf(" (");
        for (int attached_id = 0;
             attached_id < error->attached_count;
             attached_id++)
        {
          auto attachment = error->attached[attached_id];
          printf("%s: ", attachment.string);
          printExpression(0, attachment.expression);
          if (attached_id != error->attached_count-1) 
            printf(", ");
        }
        printf(")");
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
    checkArena(global_temp_arena);

  return success;
}

internal b32
beginInterpreterSession(MemoryArena *arena, char *initial_file)
{
  initializeEngine(arena);
  auto state = pushStruct(arena, EngineState);
  auto input_path = platformGetFileFullPath(arena, initial_file);
  b32 success = interpretFile(state, arena, input_path, true);

  for (FileList *file_list = state->file_list;
       file_list;
       file_list = file_list->next)
  {
    platformFreeFileMemory(file_list->first_content);
  }
    
  checkArena(arena);
  return success;
}

int
engineMain(EngineMemory *memory)
{
  assert(arrayCount(keywords)       == Keywords_Count_);
  assert(arrayCount(metaDirectives) == MetaDirective_Count_);

  int success = true;

  auto init_arena_ = newArena(memory->storage_size, memory->storage);
  auto init_arena = &init_arena_;

  allocate(init_arena, builtin_identical);
  allocate(init_arena, builtin_identical_macro);
  allocate(init_arena, builtin_True);
  allocate(init_arena, builtin_truth);
  allocate(init_arena, builtin_False);
  allocate(init_arena, builtin_Set);
  allocate(init_arena, builtin_Prop);
  allocate(init_arena, builtin_Fun);
  allocate(init_arena, builtin_Type);
  allocate(init_arena, hole_expression);

  builtin_identical->cat       = EC_Builtin_identical;
#if 0
  builtin_identical_macro->cat = EC_Macro;
#endif

  builtin_Set->cat  = EC_Builtin_Set;
  builtin_Prop->cat = EC_Builtin_Prop;
  builtin_Fun->cat = EC_Builtin_Proc;
  builtin_Type->cat = EC_Builtin_Type;

  builtin_Set->type  = builtin_Type;
  builtin_Prop->type = builtin_Type;
  builtin_Fun->type = builtin_Type;

  hole_expression->cat = EC_Hole;

  {
    // Here we give 'identical' a type (A: Set, a:A, b:A) -> Prop.
    // TODO: so we can't prove equality between props.
    builtin_identical->type = newExpressionNoCast(init_arena, ArrowType, 0);
    auto signature = castExpression(builtin_identical->type, ArrowType);
    signature->param_count = 3;
    signature->return_type = builtin_Set;

    allocateArray(init_arena, 3, signature->params);
    auto args = signature->params;

    args[0] = newExpression(init_arena, Variable, builtin_Set);
    initVariable(args[0], toString("A"), 0, signature);

    args[1] = newExpression(init_arena, Variable, (Expression*)args[0]);
    initVariable(args[1], toString("a"), 1, signature);

    args[2] = newExpression(init_arena, Variable, (Expression*)args[0]);
    initVariable(args[2], toString("b"), 2, signature);
  }

  auto interp_arena_ = subArena(init_arena, getArenaFree(init_arena));
  auto interp_arena = &interp_arena_;

#if 1
  if (!beginInterpreterSession(interp_arena, "../data/basics.rea"))
    success = false;
  resetZeroArena(interp_arena);
#endif

#if 0
  if (!beginInterpreterSession(interp_arena, "../data/nat.rea"))
    success = false;
  resetZeroArena(interp_arena);
#endif

#if 0
  if (!beginInterpreterSession(interp_arena, "../data/test.rea"))
    success = false;
  resetZeroArena(interp_arena);
#endif

  return success;
}

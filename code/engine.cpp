#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_builtins.h"
#include "print.cpp"

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

// Important: all parsing must be aborted when the tokenizer encounters error.

#define VARIABLE_MATCHER(name) \
  b32 name(Environment env, Variable *in, void* opt)

typedef VARIABLE_MATCHER(variable_matcher);

inline void
myprint(char *str)
{
  printToBuffer(0, str);
}

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
identicalB32(Ast *lhs, Ast *rhs)
{
  return identicalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeForm(Ast *in0)
{
  if (Composite *in = castAst(in0, Composite))
    return castAst(in->op, Form) != 0;
  else
    return false;
}

internal Trinary
compareExpressionList(Ast **lhs_list, Ast **rhs_list, s32 count)
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
identicalTrinary(Ast *lhs0, Ast *rhs0) // TODO: turn the args into values
{
  Trinary out = Trinary_Unknown;

  if (!lhs0 | !rhs0)
    out = Trinary_False;
  else if (lhs0 == rhs0)
    out = Trinary_True;
  else if (lhs0->cat == rhs0->cat)
  {
    switch (lhs0->cat)
    {
      case AC_Variable:
      {
        Variable* lhs = castAst(lhs0, Variable);
        Variable* rhs = castAst(rhs0, Variable);
        // NOTE: I'm pretty sure this comparison is correct rn, but who knows.
        out = (Trinary)(lhs->id == rhs->id &&
                        lhs->stack_delta == rhs->stack_delta);
      } break;

      case AC_StackRef:
      {
        StackRef* lvar = castAst(lhs0, StackRef);
        StackRef* rvar = castAst(rhs0, StackRef);
        if ((lvar->stack_depth)
            && (lvar->stack_depth == rvar->stack_depth)
            && (lvar->id == rvar->id))
          out = Trinary_True;
      } break;

      case AC_Form:
      {
        out = (Trinary)(castAst(lhs0, Form)->ctor_id == castAst(rhs0, Form)->ctor_id);
      } break;

      case AC_ArrowV:
      {
        // todo: important: comparison of dependent types wouldn't work, since
        // we don't know how to compare variables yet.
        ArrowV* larrow = castAst(lhs0, ArrowV);
        ArrowV* rarrow = castAst(rhs0, ArrowV);
        Trinary return_type_compare = identicalTrinary(larrow->return_type, rarrow->return_type);
        if (return_type_compare == Trinary_False)
          out = Trinary_False;
        else if (return_type_compare == Trinary_True)
        {
          s32 param_count = larrow->param_count;
          if (rarrow->param_count == param_count)
            out = compareExpressionList(larrow->param_types, rarrow->param_types, param_count);
          else
            out = Trinary_False;
        }
      } break;

      case AC_CompositeV:
      {
        CompositeV *lhs = castAst(lhs0, CompositeV);
        CompositeV *rhs = castAst(rhs0, CompositeV);

        Trinary op_compare = identicalTrinary(lhs->op, rhs->op);
        if ((op_compare == Trinary_False) &&
            (lhs->op->cat == AC_Form) &&
            (rhs->op->cat == AC_Form))
        {
          out = Trinary_False;
        }
        else if (op_compare == Trinary_True)
        {
          assert(lhs->arg_count == rhs->arg_count);
          out = compareExpressionList(lhs->args, rhs->args, lhs->arg_count);
        }
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

inline b32
addLocalBinding(LocalBindings *bindings, String key, s32 id)
{
  auto lookup = lookupNameCurrentFrame(bindings, key, true);
  b32 succeed = false;
  if (!lookup.found)
  {
    lookup.slot->value = LocalBindingValue{id};
    succeed = true;
  }
  return succeed;
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
addGlobalBinding(String key, Value *value)
{
  auto lookup = lookupNameCurrentFrame(global_bindings, key);
  b32 succeed = true;
  if (lookup.found)
    succeed = false;
  else
    lookup.slot->value = value;
  return succeed;
}

inline b32
addGlobalBinding(char *key, Value *value)
{
  return addGlobalBinding(toString(key), value);
}

struct LookupNameRecursive { Ast *expr; b32 found; };

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

inline Ast *
constantFromGlobalName(MemoryArena *arena, Token *token)
{
  Ast *out0 = 0;
  auto lookup = lookupNameCurrentFrame(global_bindings, token->text);
  if (lookup.found)
  {
    Constant *out = newAst(arena, Constant, token);
    initConstant(out, lookup.slot->value);
    out0 = &out->a;
  }
  return out0;
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
optionalCategory(TokenCategory tc, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (parsing())
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
addBuiltinForm(MemoryArena *arena, char *name, Ast *type, const char **ctor_names, s32 ctor_count)
{
  Token form_name = newToken(name);
  Form *form = newValue(arena, Form, &form_name, type);

  Form *ctors = pushArray(arena, ctor_count, Form);
  for (s32 ctor_id = 0; ctor_id < ctor_count; ctor_id++)
  {
    Form *ctor = ctors + ctor_id;
    Token ctor_name = newToken(ctor_names[ctor_id]);
    initValue(&ctor->v, AC_Form, &ctor_name, &form->v.a);
    initForm(ctor, ctor_id);
    if (!addGlobalBinding(ctor_name, &ctor->v))
      invalidCodePath;
  }

  initForm(form, ctor_count, ctors, getNextFormId());
  if (!addGlobalBinding(form_name.text, &form->v))
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

#if 0
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

// think of a function application
internal Ast *
replaceCurrentLevel(Environment env, Ast *in, Ast **args)
{
  Ast *out = transformVariables(env, in, replaceCurrentLevelVariable, args);
  // assert(identicalB32(in->type, out->type));
  return out;
}

internal Ast *
rewriteExpression(Environment *env, Ast *in)
{
  Ast *out = 0;
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

internal Ast **
introduce(Environment *env, s32 count, Token *names, Ast **types)
{
  assert(count < arrayCount(env->stack->args));
  s32 stack_depth = env->stack_depth+1;
  StackRef **refs = pushArray(temp_arena, count, StackRef *);
  for (s32 id = 0; id < count; id++)
  {
    StackRef *ref = refs[id] = newValue(temp_arena, StackRef, names+id, types[id]);
    ref->name        = names[id];
    ref->id          = id;
    ref->stack_depth = stack_depth;
  }
  extendStack(env, count, (Ast**)refs);
  return env->stack->args;
}

internal Ast **
introduce(Environment *env, Arrow *signature)
{
  return introduce(env, signature->param_count, signature->param_names, signature->param_types);
}

inline void
printRewrites(Environment env)
{
  for (Rewrite *rewrite = env.rewrite; rewrite; rewrite = rewrite->next)
  {
    printAst(0, rewrite->lhs, {});
    printToBuffer(0, " => ");
    printAst(0, rewrite->rhs, {});
    if (rewrite->next)
      printToBuffer(0, ", ");
  }
  myprint();
}

inline Ast *
parseExpression(MemoryArena *arena);

// todo #speed don't pass the Environment in wholesale?
internal Ast *
normalize(Environment env, Ast *in0)
{
  b32 INTRODUCE_PATH = false;
  Ast *out0 = {};

  switch (in0->cat)
  {
    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = &in->value->a;
    } break;

    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      if (in->stack_delta >= env.stack_offset)
      {
        Stack *stack = env.stack;
        for (s32 delta = 0;
             delta < in->stack_delta - env.stack_offset;
             delta++)
          stack = stack->outer;
        assert(in->id < stack->arg_count);
        out0 = stack->args[in->id];
      }
      else
        out0 = in0;
    } break;

    case AC_CompositeV:
    case AC_Composite:
    {
      Composite *in = polyAst(in0, Composite, CompositeV);

      Ast **norm_args = pushArray(temp_arena, in->arg_count, Ast*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        norm_args[arg_id] = normalize(env, in_arg);
      }

      Ast *norm_op = normalize(env, in->op);
      // todo: we don't expand if there is any free variable. (eg for arrow
      // types this would not normalize the return type).
      if (env.stack_offset == 0)
      {
        if (norm_op->cat == AC_FunctionV)
        {// Function application
          FunctionV *fun = castAst(norm_op, FunctionV);
          Environment fun_env = env;
          extendStack(&fun_env, in->arg_count, norm_args);
          // note: this might fail, in which case we back out.
          out0 = normalize(fun_env, fun->body);
        }
        else
        {
          assert(norm_op->cat == AC_Form);
          if (norm_op == &builtin_identical->v.a)
          {// special case for equality
            Ast *lhs = norm_args[1];
            Ast *rhs = norm_args[2];
            Trinary compare = identicalTrinary(lhs, rhs);
            if (compare == Trinary_True)
              out0 = &builtin_True->v.a;
            else if (compare == Trinary_False)
              out0 = &builtin_False->v.a;
          }
        }
      }

      if (!out0)
      {
        CompositeV *out = copyStruct(env.arena, in);
        out->a.cat = AC_CompositeV;
        out0 = &out->a;
        out->op = norm_op;
        allocateArray(env.arena, out->arg_count, out->args);
        for (int arg_id = 0; arg_id < out->arg_count; arg_id++)
          out->args[arg_id] = norm_args[arg_id];

        // annotate the type
        ArrowV *signature = castAst(toValue(norm_op)->type, ArrowV);
        out->v.type = normalize(env, signature->return_type);
      }
    } break;

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
      }
      // note: we fail if the fork is undetermined
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      ArrowV *out = copyStruct(env.arena, in);
      out->a.cat  = AC_ArrowV;
      out->v.type = &builtin_Type->v.a;
      out0 = &out->a;

      Environment signature_env = env;
      if (INTRODUCE_PATH)
      {
        introduce(&signature_env, out);
        out->return_type = normalize(signature_env, in->return_type);
      }
      else
      {
        signature_env.stack_offset++;
        out->return_type = normalize(signature_env, in->return_type);
      }

      allocateArray(env.arena, out->param_count, out->param_types);
      for (s32 param_id = 0; param_id < out->param_count; param_id++)
      {
        Ast *norm_param_type = normalize(signature_env, in->param_types[param_id]);
        out->param_types[param_id] = norm_param_type;
      }
    } break;

    case AC_IncompleteFork:  // todo this can happen for recursive function, which is ugly
    {
      out0 = 0;
    } break;

    case AC_ArrowV:  // todo why aren't we handling this?
    case AC_FunctionV:
    case AC_StackRef:
    case AC_DummyHole:
    case AC_Form:
    {
      out0 = in0;
    } break;

    invalidDefaultCase;
  }

  if (out0)
  {
    Ast *before_rewrite = out0;
    out0 = rewriteExpression(&env, out0);
    if (out0 != before_rewrite)
      out0 = normalize(env, out0); // do another iteration

    if (env.stack_offset == 0)
      // TODO: this hole is ruining my life!
      if (out0 != &dummy_hole)
        assert(isValue(out0));
  }

  return out0;
}

inline Ast *
normalize(MemoryArena *arena, Ast *in0)
{
  return normalize(newEnvironment(arena), in0);
}

internal Ast *
normalizeStart(MemoryArena *arena, Ast *in)
{
  return normalize(newEnvironment(arena), in);
}

inline b32
normalized(Environment env, Ast *in)
{
  Ast *norm = normalize(env, in);
  return identicalB32(in, norm);
}

internal void
addRewrite(Environment *env, Ast *lhs0, Ast *rhs0)
{
  assert(normalized(*env, lhs0));
  assert(normalized(*env, rhs0));
  if (!identicalB32(lhs0, rhs0))
  {
    b32 added = false;

    if (Composite *lhs = castAst(lhs0, Composite))
      if (Composite *rhs = castAst(rhs0, Composite))
    {
      if ((lhs->op->cat == AC_Form) &&
          (rhs->op->cat == AC_Form))
      {
        assert(identicalB32(lhs->op, rhs->op));
        for (s32 arg_id = 0; lhs->arg_count; arg_id++)
          addRewrite(env, lhs->args[arg_id], rhs->args[arg_id]);
        added = true;
      }
    }

    if (!added)
    {
      Rewrite *rewrite = newRewrite(env, lhs0, rhs0);
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

// NOTE: the output as well as "expected_type" are instantiated, but expression
// types are abstract.
internal Ast *
typecheck(Environment env, Ast *in0, Ast *expected_type)
{
  Ast *actual = 0;
  switch (in0->cat)
  {
    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      actual = in->value->type;
    } break;

    case AC_Variable:
    {
      Ast *norm = normalize(env, in0);
      if (Value *value = toValue(norm))
        actual = value->type;
    } break;

    case AC_IncompleteFork:
    {
      IncompleteFork *in = castAst(in0, IncompleteFork);

      if (Ast *subject_type = typecheck(env, in->subject, 0))
      {
        if (Form *form = castAst(subject_type, Form))
        {
          s32 case_count = in->case_count;
          if (form->ctor_count == case_count)
          {
            if (case_count == 0)
              parseError(&in->a, "todo: cannot assign type to empty fork");
            else
            {
              ForkParameters  *correct_params = pushArray(env.arena, case_count, ForkParameters, true);
              Ast            **correct_bodies = pushArray(env.arena, case_count, Ast *, true);

              for (s32 input_case_id = 0;
                   (input_case_id < case_count) && noError();
                   input_case_id++)
              {
                Token          *ctor_token    = &in->parsing->ctors[input_case_id].a.token;
                ForkParameters *parsed_params = in->parsing->params + input_case_id;
                Token          *param_names   = parsed_params->names;
                s32             param_count   = parsed_params->count;
                if (Value *lookup = lookupGlobalName(ctor_token->text))
                {
                  if (Form *ctor = castValue(lookup, Form))
                  {
                    if (param_count == 0)
                    {
                       if (!identicalB32(ctor->v.type, subject_type)) 
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
                        if (identicalB32(&getFormOf(ctor_sig->return_type)->v.a,
                                         &getFormOf(subject_type)->v.a))
                        {
                          if (param_count != ctor_sig->param_count)
                            parseError(ctor_token, "pattern has wrong amount of parameters (expected: %d, got: %d)", ctor_sig->param_count, param_count);
                        }
                        else
                        {
                          parseError(ctor_token, "composite constructor has wrong return type");
                          pushAttachment("expected type", subject_type);
                          pushAttachment("got type", ctor_sig->return_type);
                        }
                      }
                      else
                      {
                        parseError(ctor_token, "expected a composite constructor");
                        pushAttachment("got type", &ctor_sig->a);
                      }
                    }

                    if (noError())
                    {
                      Ast *input_body = in->parsing->bodies[input_case_id];
                      if (correct_bodies[ctor->ctor_id])
                      {
                        parseError(input_body, "fork case handled twice");
                        pushAttachment("constructor", &ctor->v.a);
                      }
                      else
                      {
                        correct_params[ctor->ctor_id].count = param_count;
                        correct_params[ctor->ctor_id].names = param_names;
                        correct_bodies[ctor->ctor_id]       = input_body;
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

                // call typecheck again since we just got promoted
                assert(in->bodies);
                actual = typecheck(env, &in->a, expected_type);
              }
            }
          }
          else
            parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                       form->ctor_count, in->case_count);
        }
        else
          parseError(in->subject, "cannot fork this expression");
      }
    } break;

    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Form *form = in->form;
      Ast *common_type = expected_type;
      Ast *norm_subject = normalize(env, in->subject);
        
      for (s32 case_id = 0;
           case_id < in->case_count && noError();
           case_id++)
      {
        Environment fork_env = env;
        ForkParameters *params = in->params + case_id;
        Form *ctor     = form->ctors + case_id;
        Ast  *ctor_exp = &ctor->v.a;

        switch (ctor->v.type->cat)
        {
          case AC_Form:
          {// member
            addRewrite(&fork_env, norm_subject, ctor_exp);
            introduce(&fork_env, 0, 0, 0);
          } break;

          case AC_ArrowV:
          {// composite
            ArrowV  *signature  = castAst(ctor->v.type, ArrowV);
            Ast    **stack_refs = introduce(&fork_env, signature->param_count, params->names, signature->param_types);
            // NOTE: we could add a type here, but not sure if we need it.
            CompositeV *pattern = newValue(temp_arena, CompositeV, &ctor->v.a.token, 0);

            pattern->op        = ctor_exp;
            pattern->arg_count = signature->param_count;
            pattern->args      = stack_refs;

            addRewrite(&fork_env, norm_subject, &pattern->a);
          } break;

          default:
              invalidCodePath;
        }

        if (Ast *body_type = typecheck(fork_env, in->bodies[case_id], common_type))
        {
          if (!common_type)
          {
            // fork body has more specific type than outer scope???
            common_type = body_type;
          }
        }
      }

      if (noError())
      {
        actual = common_type;
      }
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      if (in->op == &dummy_sequence)
      {
        for (s32 item_id = 0; item_id < in->arg_count; item_id++)
        {
          Ast *item0 = in->args[item_id];
          if (Composite *item = castAst(item0, Composite))
          {
            if (item->op == &dummy_rewrite)
            {
              if (item->arg_count == 1)
              {
                if (Ast *rewrite_rule0 = typecheck(env, item->args[0], 0))
                {
                  b32 rule_valid = false;
                  Ast *norm_rule0 = normalize(env, rewrite_rule0);
                  if (CompositeV *norm_rule = castAst(norm_rule0, CompositeV))
                  {
                    if (norm_rule->op == &builtin_identical->v.a)
                    {
                      rule_valid = true;
                      addRewrite(&env, norm_rule->args[1], norm_rule->args[2]);
                    }
                  }
                  if (!rule_valid)
                  {
                    parseError(item0, "invalid rewrite rule, can only be equality");
                    pushAttachment("got", norm_rule0);
                  }
                }
              }
              else if (item->arg_count == 2)
              {
                Ast *lhs = item->args[0];
                Ast *norm_lhs = lhs;
                Ast *norm_rhs = normalize(env, item->args[1]);
                while (noError())
                {
                  Ast *before = norm_lhs;
                  norm_lhs = normalize(env, norm_lhs);
                  if (identicalB32(norm_lhs, norm_rhs))
                  {
                    addRewrite(&env, normalize(env, lhs), norm_rhs);
                    break;
                  }
                  else if (identicalB32(norm_lhs, before))
                  {
                    parseError(item0, "failed to prove legitimacy of rewrite rule");
                  }
                }
              }
              else
                invalidCodePath;
            }
          }
        }
        if (noError())
        {
          // typechecking is done on the last item
          actual = typecheck(env, in->args[in->arg_count-1], expected_type);
        }
      }
      else if (in->op == &dummy_rewrite)
      {
        parseError(in0, "This is a command and have no type");
      }
      else
      {
        s32 arg_count = in->arg_count;
        if (Ast *op_type = typecheck(env, in->op, 0))
        {
          if (ArrowV *signature = castAst(op_type, ArrowV))
          {
            if (signature->param_count == arg_count)
            {
              Environment signature_env = env;
              signature_env.arena = temp_arena;
              extendStack(&signature_env, arg_count, 0);
              Ast **stack_frame = signature_env.stack->args;
              for (int arg_id = 0;
                   (arg_id < arg_count) && noError();
                   arg_id++)
              {// Type inference for the arguments. todo: the hole stuff is
               // kinda hard-coded only for the equality.
                Ast *arg = in->args[arg_id];
                if (arg == &dummy_hole)
                  stack_frame[arg_id] = 0;
                else
                {
                  Ast *param_type = signature->param_types[arg_id];
                  Ast *norm_param_type = normalize(signature_env, param_type);
                  // NOTE: we must typecheck the args first before attempting to
                  // normalize it! Since forks can't be built before typechecking.
                  Ast *arg_type = typecheck(env, arg, norm_param_type);
                  stack_frame[arg_id] = normalize(env, arg);
                  if (norm_param_type == 0)
                  {
                    Variable *param_type_var = castAst(param_type, Variable);
                    assert(param_type_var->stack_delta == 0);
                    stack_frame[param_type_var->id] = arg_type;
                  }
                }
              }
              
              if (noError())
              {
                Ast **norm_args = pushArray(temp_arena, arg_count, Ast*);
                for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
                {
                  norm_args[arg_id] = normalize(env, in->args[arg_id]);
                }
                extendStack(&env, arg_count, norm_args);
                actual = signature->return_type;
              }
            }
            else
              parseError(in0, "incorrect arg count: %d (signature expected %d)", arg_count, signature->param_count);
          }
          else
          {
            parseError(in->op, "operator must have an arrow type");
            pushAttachment("got type", op_type);
          }
        }
      }
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);
      // NOTE: notice how short this is! (Not saying it's correct.)
      // It's thanks to "introduce". Let's hope that it works?
      introduce(&env, in);
      if (typecheck(env, in->return_type, 0))
        actual = &builtin_Type->v.a;  // todo: #theory it's not a form but somehow is a type?
    } break;

    invalidDefaultCase;
  }

  Ast *out = 0;
  if (noError())
  {
    assert(actual);
    Ast *norm_actual = normalize(env, actual);
    b32 matched = true;
    if (expected_type)
    {
      Ast *norm_expected = normalize(env, expected_type);
      if (!identicalB32(norm_expected, norm_actual))
      {
        matched = false;
        parseError(in0, "actual type differs from expected type");
        typecheck(env, in0, 0);
        pushAttachment("expected", norm_expected);
        pushAttachment("got", norm_actual);
      }
    }
    if (matched)
      out = norm_actual;
  }
  else
    out = 0;

  return out;
}

internal Ast *
typecheck(MemoryArena *arena, Ast *in, Ast *expected_type)
{
  Ast *out = typecheck(newEnvironment(arena), in, expected_type);
  return out;
}

struct ExpressionParsing
{
  Ast *expression;
  Ast *type;
  operator bool() { return (bool)expression; }
};

// note: Manipulation may be done in-place, but we might also allocate new
// memory, so beware!
internal Ast *
buildAst(MemoryArena *arena, LocalBindings *bindings, Ast *in0)
{
  Ast *out0 = 0;

  switch (in0->cat)
  {
    case AC_DummyRewrite:
    case AC_DummySequence:
    case AC_DummyHole:
    {
      out0 = in0;
    } break;

    case AC_Identifier:
    {
      auto lookup = lookupLocalName(arena, bindings, &in0->token);
      if (lookup.found)
        out0 = lookup.expr;
      else
      {
        if (Ast *constant = constantFromGlobalName(arena, &in0->token))
          out0 = constant;
        else
          parseError(in0, "unbound identifier in expression");
      }
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      b32 build_op = true;
      if ((in->op->cat == AC_Identifier) &&
          equal(in->op->token, "="))
      {// todo: special built-in notation for equality
        assert(in->arg_count == 2);
        Ast **new_args = pushArray(arena, 3, Ast*);
        new_args[0] = &dummy_hole;
        new_args[1] = in->args[0];
        new_args[2] = in->args[1];
        // note: this is just a temporary hack to have a constant expr as the
        // operator, and not the whole form.
        Token identical_token = in->op->token;
        identical_token.text  = toString("identical");
        Ast *identical = constantFromGlobalName(arena, &identical_token);
        assert(identical);
        initComposite(in, identical, 3, new_args);
        build_op = false;
      }

      if (build_op)
        in->op = buildAst(arena, bindings, in->op);

      if (noError())
      {
        for (s32 arg_id = 0;
             (arg_id < in->arg_count) && noError();
             arg_id++)
        {
          in->args[arg_id] = buildAst(arena, bindings, in->args[arg_id]);
        }
        if (noError())
          out0 = in0;
      }
    } break;

    case AC_Arrow:
    {
      Arrow *in = castAst(in0, Arrow);

      // introduce own bindings
      LocalBindings *local_bindings = extendBindings(arena, bindings);

      // build parameters
      for (s32 param_id = 0;
           param_id < in->param_count && noError();
           param_id++)
      {
        if (Ast *param_type = buildAst(arena, local_bindings, in->param_types[param_id]))
        {
          in->param_types[param_id] = param_type;
          addLocalBinding(local_bindings, in->param_names[param_id], param_id);
        }
      }

      if (noError())
      {
        if ((in->return_type = buildAst(arena, local_bindings, in->return_type)))
          out0 = in0;
      }
    } break;

#if 0
    case AC_IncompleteFork:
    {
      IncompleteFork *in = castAst(in0, IncompleteFork);
      IncompleteFork *out = in;

      LocalBindings *outer_bindings = bindings;
      if (Ast *subject = buildAst(arena, outer_bindings, in->subject))
      {
        if (Ast *subject_type = typecheck(newEnvironment(arena), subject, 0))
        {
          if (Form *form = castAst(subject_type, Form))
          {
            s32 case_count = in->case_count;
            if (form->ctor_count == case_count)
            {
              if (case_count == 0)
                parseError(&in->a, "todo: cannot assign type to empty fork");
              else
              {
                ForkParameters  *params = pushArray(arena, case_count, ForkParameters, true);
                Ast            **bodies = pushArray(arena, case_count, Ast *, true);
        
                for (s32 input_case_id = 0;
                     (input_case_id < case_count) && parsing();
                     input_case_id++)
                {
                  LocalBindings *local_bindings = extendBindings(temp_arena, outer_bindings);

                  Token *ctor_token = &in->parsing->ctors[input_case_id].a.token;
                  ForkParameters *parsed_params = in->parsing->params + input_case_id;
                  Token *param_names = parsed_params->names;
                  s32 param_count = parsed_params->count;
                  if (Value *lookup = lookupGlobalName(ctor_token->text))
                  {
                    if (Form *ctor = castValue(lookup, Form))
                    {
                      if (param_count == 0)
                      {
                        if (!identicalB32(ctor->v.type, subject_type))
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
                          if (identicalB32(&getFormOf(ctor_sig->return_type)->v.a,
                                           &getFormOf(subject_type)->v.a))
                          {
                            if (param_count == ctor_sig->param_count)
                            {
                              for (s32 param_id = 0; param_id < param_count; param_id++)
                              {// MARK: loop over pattern variables
                                if (!addLocalBinding(local_bindings, param_names[param_id], param_id))
                                  tokenError("reused parameter name");
                              }
                            }
                            else
                              parseError(ctor_token, "pattern has wrong amount of parameters (expected: %d, got: %d)", ctor_sig->param_count, param_count);
                          }
                          else
                          {
                            parseError(ctor_token, "composite constructor has wrong return type");
                            pushAttachment("expected type", subject_type);
                            pushAttachment("got type", ctor_sig->return_type);
                          }
                        }
                        else
                        {
                          parseError(ctor_token, "expected a composite constructor");
                          pushAttachment("got type", &ctor_sig->a);
                        }
                      }

                      if (noError())
                      {
                        pushContextName("fork case body building");
                        if (Ast *body = buildAst(arena, local_bindings, in->parsing->bodies[input_case_id]))
                        {
                          if (bodies[ctor->ctor_id])
                          {
                            parseError(in->parsing->bodies[input_case_id], "fork case handled twice");
                            pushAttachment("constructor", &ctor->v.a);
                          }
                          else
                          {
                            params[ctor->ctor_id].count = param_count;
                            params[ctor->ctor_id].names = param_names;
                            bodies[ctor->ctor_id]       = body;
                          }
                        }
                        popContext();
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
                  out->a.cat   = AC_Fork;
                  out->form    = form;
                  out->subject = subject;
                  // bookmark: we won't be building the real fork here.
                  out->params  = params;
                  out->bodies  = bodies;
                }
              }
            }
            else
              parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                         form->ctor_count, in->case_count);
          }
          else
            parseError(in->subject, "cannot fork this expression");
        }
      }

      out0 = &out->a;
    } break;
#endif

    case AC_IncompleteFork:
    {
      IncompleteFork *in = castAst(in0, IncompleteFork);
      out0 = in0;

      in->subject = buildAst(arena, bindings, in->subject);

      if (noError())
      {
        s32 case_count = in->case_count;
        LocalBindings *outer_bindings = bindings;
        for (s32 input_case_id = 0;
             (input_case_id < case_count) && parsing();
             input_case_id++)
        {
          LocalBindings *bindings = extendBindings(temp_arena, outer_bindings);

          ForkParameters *parsed_params = in->parsing->params + input_case_id;
          for (s32 param_id = 0; param_id < parsed_params->count; param_id++)
          {// MARK: loop over pattern variables
            if (!addLocalBinding(bindings, parsed_params->names[param_id], param_id))
              tokenError("reused parameter name");
          }

          if (noError())
          {
            in->parsing->bodies[input_case_id] =
              buildAst(arena, bindings, in->parsing->bodies[input_case_id]);
          }
        }
      }
    } break;

    case AC_Let:
    {
      todoIncomplete;
#if 0
      Let *in = castAst(in0, Let);
      in->rhs = buildAst(arena, bindings, in->rhs);
      if (!addBinding(bindings, in->lhs.a.token, in->rhs))
        parseError(&in->lhs.a, "local name redefinition");
      out0 = in0;
#endif
    } break;

    invalidDefaultCase;
  }

  NULL_WHEN_ERROR(out0);
  return out0;
}

inline ExpressionParsing
parseExpressionAndTypecheck(MemoryArena *arena, LocalBindings *bindings, Ast *expected_type)
{
  ExpressionParsing out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    if (Ast *expression = buildAst(arena, bindings, ast))
    {
      if (Ast *type = typecheck(newEnvironment(arena), expression, expected_type))
      {
        out.expression = expression;
        out.type       = type;
      }
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Ast *
parseExpression(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0).expression;
}

inline ExpressionParsing
parseExpressionFull(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0);
}

inline Ast *
buildAstGlobal(MemoryArena *arena, Ast *ast)
{
  return buildAst(arena, 0, ast);
}

internal Composite *
parseRewrite(MemoryArena *arena)
{
  Composite *out = 0;
  Token token = global_tokenizer->last_token;
  if (Ast *lhs_or_proof = parseExpressionToAst(arena))
  {
    out = newAst(arena, Composite, &token);
    out->op = &dummy_rewrite;
    if (optionalCategory(TC_StrongArrow))
    {
      if (Ast *rhs = parseExpressionToAst(arena))
      {
        out->arg_count = 2;
        allocateArray(arena, out->arg_count, out->args);
        out->args[0] = lhs_or_proof;
        out->args[1] = rhs;
      }
    }
    else
    {
      out->arg_count = 1;
      allocateArray(arena, out->arg_count, out->args);
      out->args[0] = lhs_or_proof;
    }
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline Ast *
parseSequence(MemoryArena *arena)
{
  Token first_token = global_tokenizer->last_token;
  Ast *out0 = 0;
  s32 count = 0;
  AstList *list = 0;
  while (parsing())
  {
    // todo #speed make a way to rewind the state of the tokenizer
    Tokenizer tk_save = *global_tokenizer;
    b32 commit = true;
    Token token = nextToken();
    if (isExpressionEndMarker(&token))
      break;
    else
    {
      Ast *ast = 0;
      if (Keyword keyword = matchKeyword(&token))
      {
        switch (keyword)
        {
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
          case TC_ColonEqual:
          {
            pushContextName("definition");
            if (Ast *rhs = parseExpressionToAst(arena))
            {
              Let *assignment = newAst(arena, Let, &after_name);
              ast = &assignment->a;
              initAst(&assignment->lhs.a, AC_Identifier, name);
              assignment->rhs = rhs;
            }
            popContext();
          } break;

          default:
          {
            commit = false;
          } break;
        }
      }

      if (commit) {assert(ast);}
      else
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
        if (!optionalChar(';'))
          break;
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
        Composite *out = newAst(arena, Composite, &first_token);
        out->arg_count = count;
        out->args      = items;
        out->op        = &dummy_sequence;
        out0 = &out->a;
      }
    }
  }
  return out0;
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

  s32         param_count;
  Token      *param_names;
  Ast       **param_types;
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
           !stop && parsing();
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
    Token arrow_token = global_tokenizer->last_token;
    if (Ast *return_type = parseExpressionToAst(arena))
    {
      out = newAst(arena, Arrow, &arrow_token);
      out->param_count = param_count;
      out->return_type = return_type;
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

  if (parsing())
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
             parsing () && !stop;
             )
        {
          if (optionalChar(')'))
            stop = true;
          else
          {
            s32 arg_id = parsed_arg_count++;
            Ast *arg = parseExpressionToAst(arena);
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
      for (b32 stop = false; !stop && parsing();)
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
    if (addGlobalBinding(ctor_token.text, &out->v))
    {
      if (optionalChar(':'))
      {
        if (Ast *parsed_type = parseExpressionFull(arena).expression)
        {
          Ast *norm_type0 = normalize(arena, parsed_type);
          b32 valid_type = false;
          if (Form *type = castAst(norm_type0, Form))
          {
            if (type == form)
              valid_type = true;
          }
          else if (ArrowV *type = castAst(norm_type0, ArrowV))
          {
            if (getFormOf(type->return_type) == form)
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
        if (form->v.type == &builtin_Set->v.a)
        {
          initValue(&out->v, AC_Form, &ctor_token, &form->v.a);
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
    if (addGlobalBinding(form_name.text, &form->v))
    {
      Ast *type = &builtin_Set->v.a;
      if (optionalChar(':'))
      {// type override
        b32 valid_type = false;
        if (ExpressionParsing type_parsing = parseExpressionFull(arena))
        {
          Ast *norm_type = normalize(arena, type_parsing.expression);
          if (ArrowV *arrow = castAst(norm_type, ArrowV))
          {
            if (arrow->return_type == &builtin_Set->v.a)
              valid_type = true;
          }
          else if (norm_type == &builtin_Set->v.a)
            valid_type = true;

          if (valid_type)
            type = norm_type;
          else
          {
            parseError(type_parsing.expression, "form has invalid type");
            pushAttachment("type", norm_type);
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

// note: currently only top level definition
internal void
parseFunction(MemoryArena *arena, Token *name)
{
  pushContext;

  assert(isIdentifier(name));
  char *debug_name = "dependentTypeTest";
  if (equal(toString(debug_name), name->text))
    breakhere;

  if (auto parsing = parseExpressionFull(arena))
  {
    Ast *signature0 = normalize(arena, parsing.expression);
    if (ArrowV *signature = castAst(signature0, ArrowV))
    {
      FunctionV *funv = newValue(arena, FunctionV, name, signature0);
      if (addGlobalBinding(name->text, &funv->v))
      {
        // note: we have to rebuild the function's local bindings
        LocalBindings *fun_bindings = extendBindings(arena, 0);
        for (s32 param_id = 0;
             param_id < signature->param_count;
             param_id++)
        {
          b32 add = addLocalBinding(fun_bindings, signature->param_names[param_id], param_id);
          assert(add);
        }

        if (requireChar('{', "open function body"))
        {
          if (Ast *body_ast = parseSequence(arena))
          {
            Ast *body = buildAst(arena, fun_bindings, body_ast);
            if (requireChar('}'))
            {
              funv->body = body;
              // NOTE: this is typechecking code, but due to the weird binding
              // that must be done for recursive functions, we can't leave it to
              // the "typecheck", which only works on expression.
              Environment env = newEnvironment(arena);
              introduce(&env, signature);
              Ast *expected_body_type = normalize(env, signature->return_type);
              typecheck(env, funv->body, expected_body_type);
            }
          }
        }
      }
      else
        tokenError("re-definition");
    }
    else
      parseError(&signature->a, "function definition requires an arrow type");
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

  while (parsing())
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
          case Keyword_Typedef:
              parseTypedef(arena);
              break;

          case Keyword_Print:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              Ast *reduced = normalizeStart(temp_arena, parsing.expression);
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
              printAst(0, parsing.expression, {.detailed=true});
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
            if (Ast *ast = parseExpressionToAst(temp_arena))
            {
              if (Ast *exp = buildAstGlobal(temp_arena, ast))
              {
                if (optionalChar(':'))
                {
                  if (Ast *expected_type = parseExpression(temp_arena))
                    typecheck(temp_arena, exp, expected_type);
                }
                else
                  typecheck(temp_arena, exp, 0);
              }
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
              Ast *norm = normalizeStart(arena, value);
              if (!addGlobalBinding(name->text, toValue(norm)))
                tokenError(name, "redefinition of global name");
              requireChar(';');
            }
          } break;

          case TC_DoubleColon:
          {
            parseFunction(arena, name);
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

    const char *builtin_Type_members[] = {"Set"};
    builtin_Type = addBuiltinForm(arena, "Type", 0, builtin_Type_members, 1);
    builtin_Set  = castValue(lookupGlobalName("Set"), Form);
    builtin_Type->v.type = &builtin_Type->v.a; // note: circular types are gonna bite us

    {// Equality
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), true);
      assert(success);
      builtin_identical = castValue(lookupGlobalName("identical"), Form);
    }

    const char *true_members[] = {"truth"};
    addBuiltinForm(arena, "True", &builtin_Set->v.a, true_members, 1);
    builtin_True  = castValue(lookupGlobalName("True"), Form);
    builtin_truth = castValue(lookupGlobalName("truth"), Form);

    addBuiltinForm(arena, "False", &builtin_Set->v.a, (const char **)0, 0);
    builtin_False = castValue(lookupGlobalName("False"), Form);
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

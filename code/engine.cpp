#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_builtins.h"

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

// Important: all parsing must be aborted when the tokenizer encounters error.

#define VARIABLE_MATCHER(name) \
  b32 name(Environment env, Variable *in, void* opt)

typedef VARIABLE_MATCHER(variable_matcher);

internal b32
searchVariable(Environment env, Ast *in, variable_matcher *matcher, void *opt)
{
  b32 found = false;
  switch (in->cat)
  {
    case AC_Variable:
    {
      Variable *var = castAst(in, Variable);
      if (!(found = matcher(env, var, opt)))
      {
        searchVariable(env, var->type, matcher, opt);
      }
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
          if (searchVariable(env, fork->cases[case_id].body, matcher, opt))
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

    case AC_ArrowType:
    {
      auto arrow = castAst(in, ArrowType);
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
          if (searchVariable(env, arrow->params[param_id]->type, matcher, opt))
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
identicalTrinary(Ast *lhs0, Ast *rhs0)
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
      case AC_StackRef:
      {
        auto lvar = castAst(lhs0, StackRef);
        auto rvar = castAst(rhs0, StackRef);
        if ((lvar->stack_depth)
            && (lvar->stack_depth == rvar->stack_depth)
            && (lvar->id == rvar->id))
          out = Trinary_True;
      } break;

      case AC_Form:
      {
        if (castAst(lhs0, Form)->ctor_id ==
            castAst(rhs0, Form)->ctor_id)
          out = Trinary_True;
        else
          out = Trinary_False;
      } break;

      case AC_ArrowType:
      {
        // todo: important: comparison of dependent types wouldn't work
        auto larrow = castAst(lhs0, ArrowType);
        auto rarrow = castAst(rhs0, ArrowType);
        Trinary return_type_compare = identicalTrinary(larrow->return_type, rarrow->return_type);
        if (return_type_compare == Trinary_False)
          out = Trinary_False;
        else if (return_type_compare == Trinary_True)
        {
          auto param_count = larrow->param_count;
          if (rarrow->param_count == param_count)
          {
            auto lparam_types = pushArray(temp_arena, param_count, Ast*);
            auto rparam_types = pushArray(temp_arena, param_count, Ast*);

            for (s32 param_id = 0;
                 param_id < param_count;
                 param_id++)
            {
              lparam_types[param_id] = larrow->params[param_id]->type;
              rparam_types[param_id] = rarrow->params[param_id]->type;
            }

            out = compareExpressionList(lparam_types, rparam_types, param_count);
          }
          else
            out = Trinary_False;
        }
      } break;

      case AC_Composite:
      {
        Composite *lhs = castAst(lhs0,  Composite);
        Composite *rhs = castAst(rhs0,  Composite);
        {
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
        }
      } break;

      case AC_Fork:
      {
        Fork *lhs = castAst(lhs0, Fork);
        Fork *rhs = castAst(rhs0, Fork);
        if (identicalB32(lhs->subject, rhs->subject))
        {
          b32 found_mismatch = false;
          for (s32 case_id = 0; case_id < lhs->case_count; case_id++)
          {
            if (!identicalB32(lhs->cases[case_id].body, rhs->cases[case_id].body))
              found_mismatch = true;
          }
          if (!found_mismatch)
            out = Trinary_True;
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

struct PrintOptions{b32 detailed; b32 print_type;};

internal char*
printAst(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{
  char *out = buffer ? (char*)getArenaNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
      case AC_StackRef:
      {
        StackRef *in = castAst(in0, StackRef);
        printToBuffer(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
      } break;
      case AC_Constant:
      {
        Constant *in = castAst(in0, Constant);
        printToBuffer(buffer, in->h.token);
      } break;

      case AC_Variable:
      {
        Variable *in = castAst(in0, Variable);
#if 0
        printToBuffer(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
#else
        printToBuffer(buffer, in->h.token);
#endif

        if (opt.detailed || opt.print_type)
        {
          printToBuffer(buffer, ": ");
          printAst(buffer, in->type, new_opt);
        }
      } break;

      case AC_Composite:
      {
        Composite *in = castAst(in0, Composite);

        if (in->op == dummy_sequence)
        {
          for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
          {
            printAst(buffer, in->args[arg_id], new_opt);
            if (arg_id < in->arg_count-1)
              printToBuffer(buffer, "; ");
          }
        }
        else if (in->op == dummy_rewrite)
        {
          printToBuffer(buffer, "rewrite ");
          if (in->arg_count == 1)
          {
            printAst(buffer, in->args[0], new_opt);
          }
          else if (in->arg_count == 2)
          {
            printAst(buffer, in->args[0], new_opt);
            printToBuffer(buffer, " => ");
            printAst(buffer, in->args[1], new_opt);
          }
        }
        else
        {
          printAst(buffer, in->op, new_opt);

          printToBuffer(buffer, "(");
          for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
          {
            printAst(buffer, in->args[arg_id], new_opt);
            if (arg_id < in->arg_count-1)
              printToBuffer(buffer, ", ");
          }
          printToBuffer(buffer, ")");
        }
      } break;

      case AC_Fork:
      {
        Fork *fork = castAst(in0, Fork);
        printToBuffer(buffer, "fork ");
        printAst(buffer, fork->subject, new_opt);
        printToBuffer(buffer, " {");
        Form *form = fork->form;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          ForkCase *casev = fork->cases + ctor_id;
          Form *ctor = form->ctors + ctor_id;
          switch (ctor->h.type->cat)
          {// print pattern
            case AC_Form:
            {
              printAst(buffer, &ctor->h.a, new_opt);
            } break;

            case AC_ArrowType:
            {
              printAst(buffer, &ctor->h.a, new_opt);
              printToBuffer(buffer, " ");
              ArrowType *signature = castAst(ctor->h.type, ArrowType);
              for (s32 param_id = 0; param_id < signature->param_count; param_id++)
              {
                printToBuffer(buffer, &casev->params[param_id]->h.token);
                printToBuffer(buffer, " ");
              }
            } break;

            invalidDefaultCase;
          }

          printToBuffer(buffer, ": ");
          printAst(buffer, casev->body, new_opt);
          if (ctor_id != form->ctor_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, "}");
      } break;

      case AC_Form:
      {
        Form *in = castAst(in0, Form);
        if (opt.detailed && in != builtin_Type)
        {
          printToBuffer(buffer, &in0->token);

          if (opt.print_type)
          {
            printToBuffer(buffer, ": ");
            printAst(buffer, in->h.type, new_opt);
          }

          if (in->ctor_count)
          {
            printToBuffer(buffer, " {");
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Form *ctor = in->ctors + ctor_id;
              printToBuffer(buffer, &ctor->h.a.token);
              printToBuffer(buffer, ": ");
              printAst(buffer, ctor->h.type, new_opt);
            }
            printToBuffer(buffer, " }");
          }
        }
        else
          printToBuffer(buffer, &in0->token);
      } break;

      case AC_Function:
      {
        Function *in = castAst(in0, Function);
        printToBuffer(buffer, &in0->token);
        if (opt.detailed)
        {
          printToBuffer(buffer, " { ");
          printAst(buffer, in->body, new_opt);
          printToBuffer(buffer, " }");
        }
      } break;

      case AC_ArrowType:
      {
        auto arrow = castAst(in0,  ArrowType);
        printToBuffer(buffer, "(");
        for (int param_id = 0;
             param_id < arrow->param_count;
             param_id++)
        {
          Variable *param = arrow->params[param_id];
          printToBuffer(buffer, &param->h.token);
          printToBuffer(buffer, ": ");
          printAst(buffer, param->type, new_opt);
          if (param_id < arrow->param_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ") -> ");

        printAst(buffer, arrow->return_type, new_opt);
      } break;

      case AC_DummyHole:
      {
        printToBuffer(buffer, "_");
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
myprint(Ast *expr)
{
  printAst(0, expr, {});
}

inline void
myprint(char *str)
{
  printToBuffer(0, str);
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

global_variable ValueBindings global_bindings;

struct LookupName { Binding* slot; b32 found; };

internal LookupName
lookupNameCurrentFrame(Bindings *bindings, String key, b32 add_if_missing)
{
  Binding *slot = 0;
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

  LookupName out = { slot, found };
  return out;
}

inline b32
addBinding(Bindings *bindings, String key, Ast *value)
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
addGlobalBinding(String key, Ast *value)
{
  auto lookup = lookupNameCurrentFrame(global_bindings.v, key, true);
  b32 succeed = true;
  if (lookup.found)
    succeed = false;
  else
    lookup.slot->value = value;
  return succeed;
}

inline b32
addGlobalBinding(char *key, Ast *value)
{
  return addGlobalBinding(toString(key), value);
}

struct LookupNameRecursive { Ast *expr; b32 found; };

inline LookupNameRecursive
lookupLocalName(MemoryArena *arena, Bindings *bindings, Token *token)
{
  Ast *expr = {};
  b32 found = false;

  for (s32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupName lookup = lookupNameCurrentFrame(bindings, token->text, false);
    if (lookup.found)
    {
      found = true;
      Ast *value = lookup.slot->value;
      if (Variable *original_var = castAst(value, Variable))
      {
        Variable *var = newAst(arena, Variable, token);
        initVariable(var, original_var->id, original_var->type);
        var->stack_delta = stack_delta;
        expr = &var->h;
      }
      else
        expr = value;
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
  auto lookup = lookupNameCurrentFrame(global_bindings.v, token->text, false);
  if (lookup.found)
  {
    // Everything in the global scope becomes identifier.
    Constant *out = newAst(arena, Constant, token);
    initIdentifier(out, lookup.slot->value);
    out0 = &out->h;
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
    initValue(&ctor->h, VC_Form, &ctor_name, &form->h.a);
    initForm(ctor, ctor_id);
    if (!addGlobalBinding(ctor_name, &ctor->h.a))
      invalidCodePath;
  }

  initForm(form, ctor_count, ctors, getNextFormId());
  if (!addGlobalBinding(form_name.text, &form->h.a))
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

#define TRANSFORM_VARIABLES                     \
  inline Expression *                           \
  transformVariables(Environment env, Expression *in, variable_transformer *transformer, void *opt)

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
      out0 = &out->h;
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
      out0 = &out_fork->h;
      out_fork->subject = transformVariables(env, in_fork->subject, transformer, opt);
      allocateArray(env.arena, out_fork->case_count, out_fork->cases);
      env.stack_offset++;
      for (s32 case_id = 0;
           case_id < out_fork->case_count;
           case_id++)
      {
        out_fork->cases[case_id] = in_fork->cases[case_id];
        out_fork->cases[case_id].body = transformVariables(env, in_fork->cases[case_id].body, transformer, opt);
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
    return &in->h;
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
introduce(Environment *env, s32 count, Variable **models)
{
  StackRef **refs = pushArray(env->temp_arena, count, StackRef*);
  s32 stack_depth = env->stack_depth+1;
  for (s32 id = 0; id < count; id++)
  {
    Variable *model = models[id];
    StackRef *ref = refs[id] = newValue(env->arena, StackRef, &model->h.token, model->type);
    ref->name = model->h.token;
    ref->id = model->id;
    ref->stack_depth = stack_depth;
  }
  extendStack(env, count, (Ast**)refs);
  return (Ast**)refs;
}

internal Ast **
introduce(Environment *env, ArrowType *signature)
{
  return introduce(env, signature->param_count, signature->params);
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
  printNewline();
}

inline Ast *
parseExpression(MemoryArena *arena);

// todo #speed don't pass the Environment in wholesale?
internal Ast *
normalize(Environment env, Ast *in0, b32 force_expand=false)
{
  Ast *out0 = {};

  switch (in0->cat)
  {
    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = in->value;
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

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);

      Ast **norm_args = pushArray(temp_arena, in->arg_count, Ast*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Ast *in_arg = in->args[arg_id];
        norm_args[arg_id] = normalize(env, in_arg);
      }

      Ast *norm_op = normalize(env, in->op);
      if (norm_op->cat == AC_Function)
      {// Function application
        Function *fun = castAst(norm_op, Function);
        Environment fun_env = env;
        extendStack(&fun_env, in->arg_count, norm_args);
        // note: this might fail, in which case we back out.
        out0 = normalize(fun_env, fun->body);
      }
      else if ((norm_op == &builtin_identical->h.a) &&
               env.stack_offset == 0  // todo: questionable?
               )
      {// special case for equality
        Ast *lhs = norm_args[1];
        Ast *rhs = norm_args[2];
        Trinary compare = identicalTrinary(lhs, rhs);
        if (compare == Trinary_True)
          out0 = &builtin_True->h.a;
        else if (compare == Trinary_False)
          out0 = &builtin_False->h.a;
        else if (isCompositeForm(lhs)
                 && isCompositeForm(rhs))
        {// Leibniz' principle
          Composite *lapp = castAst(lhs, Composite);
          Composite *rapp = castAst(rhs, Composite);
          assert(identicalB32(lapp->op, rapp->op)); // if they aren't equal then it'd already be false.
          Composite *out = copyStruct(env.arena, in);
          out0 = &out->h;
          if (lapp->arg_count > 1)
          {
            todoIncomplete;  // we need "and" expression
          }
          else
          {
            allocateArray(env.arena, 3, out->args);
            out->args[0] = in->args[0];
            out->args[1] = lapp->args[0];
            out->args[2] = rapp->args[0];
          }
        }
      }

      if (!out0)
      {
        Composite *out_app = copyStruct(env.arena, in);
        out0 = &out_app->h;

        out_app->op = norm_op;
        allocateArray(env.arena, out_app->arg_count, out_app->args);
        for (int arg_id = 0; arg_id < out_app->arg_count; arg_id++)
          out_app->args[arg_id] = norm_args[arg_id];
      }
    } break;

    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Ast *norm_subject = normalize(env, in->subject);

      Environment *outer_env = &env;
      Environment env = *outer_env;
      switch (norm_subject->cat)
      {
        case AC_Form:
        {
          Form *ctor = castAst(norm_subject, Form);
          extendStack(&env, 0, 0);
          out0 = normalize(env, in->cases[ctor->ctor_id].body);
        } break;

        case AC_Composite:
        {
          Composite *subject = castAst(norm_subject, Composite);
          if (Form *ctor = castAst(subject->op, Form))
          {
            Ast *body = in->cases[ctor->ctor_id].body;
            extendStack(&env, subject->arg_count, subject->args);
            out0 = normalize(env, body);
          }
        } break;
      }
      // note: we fail if the fork is undetermined
    } break;

    case AC_ArrowType:
    {
      ArrowType *in = castAst(in0, ArrowType);
      ArrowType *out = copyStruct(env.arena, in);
      out0 = &out->h;
      env.stack_offset++;
      out->return_type = normalize(env, in->return_type);
      allocateArray(env.arena, out->param_count, out->params);
      for (s32 param_id = 0; param_id < out->param_count; param_id++)
      {
        Variable *param = out->params[param_id] = copyStruct(env.arena, in->params[param_id]);
        param->type = normalize(env, param->type);
      }
    } break;

    default:
    {
      out0 = in0;
    } break;
  }

  if (out0)
  {
    Ast *before_rewrite = out0;
    out0 = rewriteExpression(&env, out0);
    if (out0 != before_rewrite)
      out0 = normalize(env, out0); // do another iteration
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
    printExpression(0, lhs, {});
    printToBuffer(0, " -> ");
    printExpression(0, rhs, {});
    printNewline();
#endif
  }
}

struct CallStack
{
  Function  *first;
  CallStack *next;
};

#if 0
internal b32
isFullyTyped(Expression *in0, CallStack *call_stack)
{
  assert(hasType(in0));
  b32 out = true;
  switch (in0->cat)
  {
    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      if (!isFullyTyped(in->subject, call_stack))
        out = false;
      else
      {
        for (s32 case_id = 0; case_id < in->case_count; case_id++)
        {
          if (!isFullyTyped(in->cases[case_id].body, call_stack))
          {
            out = false;
            break;
          }
        }
      }
    } break;

    case AC_Function:
    {
      Function *in = castAst(in0, Function);

      b32 found = false;
      for (CallStack *stack = call_stack; stack && !found; stack = stack->next)
      {
        if (stack->first == in)
          found = true;
      }

      if (!found)
      {
        CallStack new_call_stack = {};
        new_call_stack.first = in;
        new_call_stack.next = call_stack;

        out = isFullyTyped(in->body, &new_call_stack);
      }
    } break;

    case AC_Application:
    {
      Application *in = castAst(in0, Application);
      if (!isFullyTyped(in->op, call_stack))
        out = false;
      else
      {
        for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
          if (!isFullyTyped(in->args[arg_id], call_stack))
          {
            out = false;
            break;
          }
      }
    } break;

    case AC_ArrowType:
    {
      ArrowType *in = castAst(in0, ArrowType);
      out = isFullyTyped(in->return_type, call_stack);
    }
  }
  return out;
}
#endif

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
  return &out->h;
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

inline Ast *
typeOfValue(Ast *value)
{
  Ast *out = 0;
  Ast *in0 = value;
  switch (in0->cat)
  {
    case AC_Form:
    {
      Form *in = castAst(in0, Form);
      out = in->h.type;
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      out = in->type;
    } break;

    case AC_Function:
    {
      Function *in = castAst(in0, Function);
      out = in->h.type;
    } break;

    invalidDefaultCase;
  }
  return out;
}

// NOTE: the output as well as "expected_type" are instantiated, but expression
// types are abstract.
internal Ast *
typecheck(Environment env, Ast *in0, Ast *expected_type)
{
  Ast *out0 = 0;

  switch (in0->cat)
  {
    case AC_Constant:
    {
      Constant *in = castAst(in0, Constant);
      out0 = typeOfValue(in->value);
    } break;

    case AC_Form:
    {
      Form *in = castAst(in0, Form);
      out0 = in->h.type;
    } break;

    case AC_Variable:
    {
      Variable *in = castAst(in0, Variable);
      out0 = in->type;
    } break;

    case AC_Fork:
    {
      Fork *in = castAst(in0, Fork);
      Environment *outer_env = &env;

      Form *form = in->form;

      Ast *common_type = expected_type;
      Ast *norm_subject = normalize(env, in->subject);
        
      for (s32 case_id = 0;
           case_id < in->case_count && noError();
           case_id++)
      {
        Environment  env = *outer_env;

        ForkCase *casev    = in->cases + case_id;

        Form *ctor     = form->ctors + case_id;
        Ast  *ctor_exp = &ctor->h.a;

        switch (ctor->h.type->cat)
        {
          case AC_Form:
          {// member
            normalize(env, in->subject);
            addRewrite(&env, norm_subject, ctor_exp);
            introduce(&env, 0, 0);
          } break;

          case AC_ArrowType:
          {// composite
            ArrowType   *signature = castAst(ctor->h.type, ArrowType);
            Ast **params    = introduce(&env, signature->param_count, casev->params);
            Composite   *pattern   = newAst(env.temp_arena, Composite, &ctor->h.token);
            initComposite(pattern, ctor_exp, signature->param_count, params);
            addRewrite(&env, norm_subject, &pattern->h);
          } break;

          default:
              invalidCodePath;
        }

        if (Ast *body_type = typecheck(env, casev->body, common_type))
        {
          if (!common_type)
          {
            // fork body has more specific type than outer scope???
            common_type = body_type;
          }
        }
      }

      if (noError())
        out0 = common_type;
    } break;

    case AC_Function:
    {
      Function *in = castAst(in0, Function);
      if (in->h.type)
        out0 = in->h.type;
      else if (expected_type)
      {
        if (ArrowType *expected_signature = castAst(expected_type, ArrowType))
        {
          introduce(&env, expected_signature);
          // Grant the function its type first, since the function body may call itself.
          in->h.type = &expected_signature->h;
          Ast *expected_body_type = normalize(env, expected_signature->return_type);
          if (typecheck(env, in->body, expected_body_type))
            out0 = expected_type;
        }
        else
        {
          parseError(in0, "function must have arrow type");
          pushAttachment("expected type", expected_type);
        }
      }
      else
        parseError(in0, "#bug all functions should have type annotation");
    } break;

    case AC_Composite:
    {
      Composite *in = castAst(in0, Composite);
      if (in->type)
        out0 = in->type;
      else if (in->op == dummy_sequence)
      {
        for (s32 id = 0; id < in->arg_count; id++)
        {
          Ast *item0 = in->args[id];
          if (Composite *item = castAst(item0, Composite))
          {
            if (item->op == dummy_rewrite)
            {
              if (item->arg_count == 1)
              {
                if (Ast *rewrite_rule0 = typecheck(env, item->args[0], 0))
                {
                  b32 rule_valid = false;
                  Ast *norm_rule0 = normalize(env, rewrite_rule0);
                  if (Composite *norm_rule = castAst(norm_rule0, Composite))
                  {
                    if (norm_rule->op == &builtin_identical->h.a)
                    {
                      rule_valid = true;
                      addRewrite(&env, norm_rule->args[1], norm_rule->args[2]);
                    }
                  }
                  if (!rule_valid)
                    parseError(item0, "invalid rewrite rule, can only be equality");
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
                  norm_lhs = normalize(env, norm_lhs, true);
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
          out0 = typecheck(env, in->args[in->arg_count-1], expected_type);
        }
      }
      else if (in->op == dummy_rewrite)
      {
        // NOTE: questionable hack, but what's the harm.
        out0 = &builtin_True->h.a;
      }
      else
      {
        s32 arg_count = in->arg_count;
        if (Ast *op_type = typecheck(env, in->op, 0))
        {
          if (ArrowType *signature = castAst(op_type, ArrowType))
          {
            if (signature->param_count == arg_count)
            {
              Environment signature_env = env;
              env.arena = temp_arena;
              Ast **stack_frame = pushArray(temp_arena, arg_count, Ast*, true);
              extendStack(&signature_env, arg_count, stack_frame);
              for (int arg_id = 0;
                   (arg_id < arg_count) && noError();
                   arg_id++)
              {// Type inference for the arguments. todo: the hole stuff is
               // kinda hard-coded only for the equality.
                Ast *arg   = in->args[arg_id];
                Variable   *param = signature->params[arg_id];

                if (arg->cat != AC_DummyHole)
                {
                  Ast *norm_param_type = normalize(signature_env, param->type);
                  Ast *arg_type = typecheck(env, arg, norm_param_type);
                  stack_frame[arg_id] = normalize(env, arg);
                  if (norm_param_type == 0)
                  {
                    Variable *param_type_var = castAst(param->type, Variable);
                    assert(param_type_var->stack_delta == 0);
                    stack_frame[param_type_var->id] = arg_type;
                  }
                }
              }
              
              if (noError())
              {
                Ast **norm_args = pushArray(env.arena, arg_count, Ast*);
                for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
                {
                  norm_args[arg_id] = normalize(env, in->args[arg_id]);
                }
                extendStack(&env, arg_count, norm_args);
                out0 = normalize(env, signature->return_type);
                // nocheckin: this is NOT cool... we are caching the unabstracted type.
                in->type = out0;
              }
            }
            else
              parseError(in0, "incorrect arg count: %d (procedure expected %d)", arg_count, signature->param_count);
          }
          else
          {
            parseError(in->op, "operator must have an arrow type");
            pushAttachment("got type", op_type);
          }
        }
      }
    } break;

    case AC_ArrowType:
    {
      ArrowType *in = castAst(in0, ArrowType);
      introduce(&env, in);
      if (typecheck(env, in->return_type, 0))
        out0 = &builtin_Type->h.a;  // todo: #theory it's not a form but somehow is a type?
    } break;

    invalidDefaultCase;
  }

  Ast *out = 0;
  if (noError())
  {
    assert(out0);
    Ast *norm_actual = normalize(env, out0);
    b32 matched = true;
    if (expected_type)
    {
      Ast *norm_expected = normalize(env, expected_type);
      if (!identicalB32(norm_expected, norm_actual))
      {
        matched = false;
        parseError(in0, "actual type differs from expected type");
        pushAttachment("expected", norm_expected);
        pushAttachment("got", norm_actual);
      }
    }
    if (matched)
      out = norm_actual;
  }
  else
  {
    assert(!out0);
  }

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
buildExpression(MemoryArena *arena, Bindings *bindings, Ast *in0)
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
      {// NOTE: special built-in notation for equality
        assert(in->arg_count == 2);
        Ast **new_args = pushArray(arena, 3, Ast*);
        new_args[0] = hole_expression;
        new_args[1] = in->args[0];
        new_args[2] = in->args[1];
        // todo: still nervous about putting the whole form there...
        initComposite(in, &builtin_identical->h.a, 3, new_args);
        build_op = false;
      }

      if (build_op)
        in->op = buildExpression(arena, bindings, in->op);

      if (noError())
      {
        for (s32 arg_id = 0;
             (arg_id < in->arg_count) && noError();
             arg_id++)
        {
          in->args[arg_id] = buildExpression(arena, bindings, in->args[arg_id]);
        }
        if (noError())
          out0 = in0;
      }
    } break;

    case AC_ArrowType:
    {
      ArrowType *in = castAst(in0, ArrowType);

      // introduce own bindings
      Bindings *outer_bindings = bindings;
      Bindings *bindings       = extendBindings(arena, outer_bindings);

      // build parameters
      for (s32 param_id = 0;
           param_id < in->param_count && noError();
           param_id++)
      {
        Variable *param = in->params[param_id];
        if ((param->type = buildExpression(arena, bindings, param->type)))
          addBinding(bindings, param->h.token.text, &param->h);
      }

      if (noError())
      {
        if ((in->return_type = buildExpression(arena, bindings, in->return_type)))
          out0 = in0;
      }
    } break;

    case AC_AbstractFork:
    {
      AbstractFork *in = castAst(in0, AbstractFork);
      Fork *out = 0;

      Bindings *outer_bindings = bindings;
      if (Ast *subject = buildExpression(arena, outer_bindings, in->subject))
      {
        if (Ast *subject_type = typecheck(newEnvironment(arena), subject, 0))
        {
          if (Form *form = castAst(subject_type, Form))
          {
            s32 case_count = in->case_count;
            if (form->ctor_count == case_count)
            {
              if (case_count == 0)
                parseError(&in->h, "todo: cannot assign type to empty fork");
              else
              {
                ForkCase *cases = pushArray(arena, case_count, ForkCase, true);
        
                for (s32 input_case_id = 0;
                     (input_case_id < case_count) && parsing();
                     input_case_id++)
                {
                  Bindings *bindings = extendBindings(temp_arena, outer_bindings);

                  Ast *ast_pattern = in->patterns[input_case_id];
                  Form *ctor = 0;
                  Variable **params;
                  s32 param_count;
                  pushContextName("transform switch case pattern");
                  switch (ast_pattern->cat)
                  {
                    case AC_Identifier:
                    {
                      params = 0;
                      param_count = 0;
                      if (Ast *pattern = buildExpression(temp_arena, outer_bindings, ast_pattern))
                      {
                        Ast *norm_pattern = normalize(temp_arena, pattern);
                        if ((ctor = castAst(norm_pattern, Form)))
                        {
                          if (!identicalB32(ctor->h.type, subject_type))
                          {
                            parseError(ast_pattern, "constructor of wrong type");
                            pushAttachment("expected type", subject_type);
                            pushAttachment("got type", ctor->h.type);
                          }
                        }
                        else
                          parseError(ast_pattern, "expected a member constructor");
                      }
                    } break;

                    case AC_Composite:
                    {
                      Composite *branch = castAst(ast_pattern, Composite);
                      if (Ast *op0 = buildExpression(arena, outer_bindings, branch->op))
                      {
                        Ast *op = normalize(temp_arena, op0);
                        if ((ctor = castAst(op, Form)))
                        {
                          if (ArrowType *ctor_sig = castAst(ctor->h.type, ArrowType))
                          {
                            if (identicalB32(&getFormOf(ctor_sig->return_type)->h.a, &getFormOf(subject_type)->h.a))
                            {
                              param_count = branch->arg_count;
                              if (param_count == ctor_sig->param_count)
                              {
                                allocateArray(arena, param_count, params, true);
                                for (s32 param_id = 0; param_id < param_count; param_id++)
                                {// MARK: loop over pattern variables
                                  Ast *ast_arg = branch->args[param_id];
                                  if (Identifier *arg = castAst(ast_arg, Identifier))
                                  {
                                    Token *param_name = &arg->h.token;
                                    auto lookup = lookupNameCurrentFrame(bindings, param_name->text, true);
                                    if (lookup.found)
                                      tokenError("reused parameter name");
                                    else
                                    {
                                      assert(ctor_sig->params[param_id]);
                                      // pattern variable: only the name is different
                                      Variable *param_src = ctor_sig->params[param_id];
                                      params[param_id] = copyStruct(arena, param_src);
                                      Variable *param = params[param_id];
                                      param->h.token = *param_name;
                                      lookup.slot->value = &param->h;
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
                              parseError(ast_pattern, "composite constructor has wrong return type");
                              pushAttachment("expected type", subject_type);
                              pushAttachment("got type", ctor_sig->return_type);
                            }
                          }
                          else
                          {
                            parseError(branch->op, "expected a composite constructor");
                            pushAttachment("got type", &ctor_sig->h);
                          }
                        }
                        else
                          parseError(ast_pattern, "expected a composite constructor");
                      }
                    } break;

                    invalidDefaultCase;
                  }
                  popContext();

                  Ast *body = 0;
                  if (noError())
                  {
                    pushContextName("fork case body building");
                    Ast *ast_body = in->bodies[input_case_id];
                    body = buildExpression(arena, bindings, ast_body);
                    popContext();
                  }

                  if (noError())
                  {
                    // we could error out sooner but whatevs.
                    if (cases[ctor->ctor_id].body)
                    {
                      parseError(in->bodies[input_case_id], "fork case handled twice");
                      pushAttachment("constructor", &ctor->h.a);
                    }
                    else
                      initForkCase(cases + ctor->ctor_id, body, params, param_count);
                  }
                }

                if (noError())
                {
                  out = newAst(arena, Fork, &in->h.token);
                  initFork(out, form, subject, case_count, cases);
                }
              }
            }
            else
              parseError(&in->h, "wrong number of cases, expected: %d, got: %d",
                         form->ctor_count, in->case_count);
          }
          else
            parseError(in->subject, "cannot fork this expression");
        }
      }

      out0 = &out->h;
    } break;

    invalidDefaultCase;
  }

  NULL_WHEN_ERROR(out0);
  return out0;
}

inline ExpressionParsing
parseExpressionAndTypecheck(MemoryArena *arena, Bindings *bindings, Ast *expected_type)
{
  ExpressionParsing out = {};
  if (Ast *ast = parseExpressionToExpression(arena))
  {
    if (Ast *expression = buildExpression(arena, bindings, ast))
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
buildExpressionGlobal(MemoryArena *arena, Ast *ast)
{
  return buildExpression(arena, 0, ast);
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
    Token next = peekNext();
    if (isExpressionEndMarker(&next))
      break;
    else if (Ast *expr = parseExpressionToExpression(arena))
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->first = expr;
      new_list->next  = list;
      list = new_list;
      if (!optionalChar(';'))
        break;
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
        out->op        = dummy_sequence;
        out0 = &out->h;
      }
    }
  }
  return out0;
}

internal AbstractFork *
parseFork(MemoryArena *arena)
{
  pushContext;

  AbstractFork *out = 0;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpressionToExpression(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *global_tokenizer;
    s32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      s32 actual_case_count = 0;
      Ast **patterns = pushArray(arena, case_count, Ast*);
      Ast **bodies   = pushArray(arena, case_count, Ast*);

      for (b32 stop = false;
           !stop && noError();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContextName("fork case");
          auto input_case_id = actual_case_count++;
          patterns[input_case_id] = parseExpressionToExpression(arena);
          if (noError())
          {
            pushContextName("fork body");
            if (requireChar(':', "syntax: CASE: BODY"))
            {
              if (Ast *body = parseSequence(arena))
              {
                bodies[input_case_id] = body;
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
        out = newAst(arena, AbstractFork, &token);
        out->subject    = subject;
        out->case_count = case_count;
        out->patterns   = patterns;
        out->bodies     = bodies;
      }
    }
  }
  popContext();

  return out;
}

internal ArrowType *
parseArrowType(MemoryArena *arena)
{
  ArrowType *out = 0;
  pushContext;

  Variable **params;
  s32        param_count;
  if (requireChar('('))
  {
    Tokenizer tk_copy = *global_tokenizer;
    param_count = getCommaSeparatedListLength(&tk_copy);
    if (parsing(&tk_copy))
    {
      params = pushArray(arena, param_count, Variable*);

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
          Variable *param = params[param_id] = newAst(arena, Variable, &param_name_token);
          param->id = param_id;

          if (optionalChar(':'))
          {
            if (Ast *param_type = parseExpressionToExpression(arena))
            {
              param->type = param_type;
              if (typeless_run)
              {
                for (s32 offset = 1; offset <= typeless_run; offset++)
                  params[param_id - offset]->type = param_type;
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
    if (Ast *return_type = parseExpressionToExpression(arena))
    {
      out = newAst(arena, ArrowType, &arrow_token);
      initArrowType(out, param_count, params, return_type);
    }
  }

  popContext();
  NULL_WHEN_ERROR(out);
  return out;
}

internal Composite *
parseRewrite(MemoryArena *arena)
{
  Composite *out = 0;
  Token token = global_tokenizer->last_token;
  if (Ast *lhs_or_proof = parseExpressionToExpression(arena))
  {
    out = newAst(arena, Composite, &token);
    out->op = dummy_rewrite;
    if (optionalCategory(TC_StrongArrow))
    {
      if (Ast *rhs = parseExpressionToExpression(arena))
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
        out = &parseFork(arena)->h;
      } break;

      case Keyword_Rewrite:
      {
        out = &parseRewrite(arena)->h;
      } break;

      default:
          tokenError("keyword not part of expression");
    }
  }
  else if (isIdentifier(&token1))
  {
    if (equal(&token1, '_'))
      // todo: this doesn't preserve identifier location
      out = hole_expression;
    else
      out = &(newAst(arena, Identifier, &token1))->h;
  }
  else if (equal(&token1, '('))
  {
    out = parseExpressionToExpression(arena);
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
        out = &branch->h;
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
            Ast *arg = parseExpressionToExpression(arena);
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
  pushContext;

  Ast *out = 0;
  if (seesArrowExpression())
  {
    out = &parseArrowType(arena)->h;
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
              initComposite(new_operand, &op->h, 2, args);
              operand = &new_operand->h;
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
parseExpressionToExpression(MemoryArena *arena)
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
    if (addGlobalBinding(ctor_token.text, &out->h.a))
    {
      if (optionalChar(':'))
      {
        if (Ast *parsed_type = parseExpressionFull(arena).expression)
        {
          Ast *type0 = normalize(arena, parsed_type);
          b32 valid_type = false;
          if (Form *type = castAst(type0, Form))
          {
            if (type == form)
              valid_type = true;
          }
          else if (ArrowType *type = castAst(type0, ArrowType))
          {
            if (getFormOf(type->return_type) == form)
              valid_type = true;
          }

          if (valid_type)
          {
            initValue(&out->h, VC_Form, &ctor_token, type0);
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
        if (form->h.type == &builtin_Set->h.a)
        {
          initValue(&out->h, VC_Form, &ctor_token, &form->h.a);
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
    if (addGlobalBinding(form_name.text, &form->h.a))
    {
      Ast *type = &builtin_Set->h.a;
      if (optionalChar(':'))
      {// type override
        b32 valid_type = false;
        if (ExpressionParsing type_parsing = parseExpressionFull(arena))
        {
          Ast *norm_type = normalize(temp_arena, type_parsing.expression);
          if (ArrowType *arrow = castAst(norm_type, ArrowType))
          {
            if (arrow->return_type == &builtin_Set->h.a)
              valid_type = true;
          }
          else if (norm_type == &builtin_Set->h.a)
            valid_type = true;

          if (valid_type)
            type = type_parsing.expression;
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
          initValue(&form->h, VC_Form, &form_name, type);
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
  char *debug_name = "andWithFalse";
  if (equal(toString(debug_name), name->text))
    breakhere;

  if (auto [signature0, _] = parseExpressionFull(arena))
  {
    if (ArrowType *signature = castAst(signature0, ArrowType))
    {
      Function *fun = newAst(arena, Function, name);
      if (addGlobalBinding(name->text, &fun->h.a))
      {
        // note: we have to rebuild the function's local bindings
        Bindings *fun_bindings = extendBindings(arena, 0);
        for (s32 param_id = 0;
             param_id < signature->param_count;
             param_id++)
        {
          Variable *param = signature->params[param_id];
          b32 add = addBinding(fun_bindings, param->h.token.text, &param->h);
          assert(add);
        }

        if (requireChar('{', "open function body"))
        {
          if (Ast *body_ast = parseSequence(arena))
          {
            Ast *body = buildExpression(arena, fun_bindings, body_ast);
            if (requireChar('}'))
            {
              fun->body = body;
              typecheck(arena, &fun->h.a, &signature->h);
            }
          }
        }
      }
      else
        tokenError("re-definition");
    }
    else
      parseError(&signature->h, "function definition requires an arrow type");
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
              printNewline();
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
              printNewline();
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
            pushContextName("typecheck");
            Ast *ast = parseExpressionToExpression(temp_arena);

            if (Ast *exp = buildExpressionGlobal(temp_arena, ast))
            {
              if (optionalChar(':'))
              {
                if (Ast *expected_type = parseExpression(temp_arena))
                  typecheck(temp_arena, exp, expected_type);
              }
              else
                typecheck(temp_arena, exp, 0);
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
            Ast *value = parseExpression(arena);
            Ast *norm  = normalizeStart(arena, value);
            if (parsing())
            {
              if (!addGlobalBinding(name->text, norm))
                tokenError(name, "redefinition of global name");
            }
            requireChar(';');
            popContext();
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

inline Ast *
lookupGlobalName(char *name)
{
  return lookupNameCurrentFrame(global_bindings.v, toString(name), false).slot->value;
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
    global_bindings = toValueBindings(pushStruct(arena, Bindings));
    global_bindings.v->arena = arena;

    const char *builtin_Type_members[] = {"Set"};
    builtin_Type = addBuiltinForm(arena, "Type", 0, builtin_Type_members, 1);
    builtin_Set  = castAst(lookupGlobalName("Set"), Form);
    builtin_Type->h.type = &builtin_Type->h.a; // note: circular types are gonna bite us

    allocate(arena, dummy_sequence, true);
    dummy_sequence->cat = AC_DummySequence;

    allocate(arena, dummy_rewrite, true);
    dummy_rewrite->cat = AC_DummyRewrite;

    allocate(arena, hole_expression);
    hole_expression->cat = AC_DummyHole;


    {// Equality
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), true);
      assert(success);
      builtin_identical = castAst(lookupGlobalName("identical"), Form);
    }

    const char *true_members[] = {"truth"};
    addBuiltinForm(arena, "True", &builtin_Set->h.a, true_members, 1);
    builtin_True  = castAst(lookupGlobalName("True"), Form);
    builtin_truth = castAst(lookupGlobalName("truth"), Form);

    addBuiltinForm(arena, "False", &builtin_Set->h.a, (const char **)0, 0);
    builtin_False = castAst(lookupGlobalName("False"), Form);
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

int
engineMain()
{
  astdbg whatever = {};
  (void)whatever;

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

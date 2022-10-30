#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"
#include "engine.h"
#include "rea_builtins.h"

#define NULL_WHEN_ERROR(name) assert((bool)name == noError())

// Important: all parsing must be aborted when the tokenizer encounters error.

#define VARIABLE_MATCHER(name) \
  b32 name(Environment env, Variable *in, void* opt)

typedef VARIABLE_MATCHER(variable_matcher);

internal b32
searchVariable(Environment env, Expression *in, variable_matcher *matcher, void *opt)
{
  b32 found = false;
  switch (in->cat)
  {
    case EC_Variable:
    {
      Variable *var = castExpression(in, Variable);
      if (!(found = matcher(env, var, opt)))
      {
        searchVariable(env, var->type, matcher, opt);
      }
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
hasAnyVariable(Expression *in)
{
  Environment env = newEnvironment(global_temp_arena);
  return searchVariable(env, in, isAnyVariable, 0);
}

VARIABLE_MATCHER(isFreeVariable)
{
  (void) opt;
  return (in->stack_delta >= env.stack_offset) && (in->stack_depth == 0);
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

VARIABLE_MATCHER(isDeepVariable)
{
  (void) opt;
  return in->stack_depth > env.stack_depth;
}

inline b32
hasDeepVariable(Environment env, Expression *in)
{
  return searchVariable(env, in, isDeepVariable, 0);
}

inline b32
identicalB32(Expression *lhs, Expression *rhs)
{
  return identicalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeForm(Expression *expression)
{
  if (auto app = castExpression(expression, Application))
    return app->op->cat == EC_Form;
  else
    return false;
}

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
identicalTrinary(Expression *lhs0, Expression *rhs0)
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
      case EC_Variable:
      {
        auto lvar = castExpression(lhs0, Variable);
        auto rvar = castExpression(rhs0, Variable);
        if ((lvar->stack_depth)
            && (lvar->stack_depth == rvar->stack_depth)
            && (lvar->id == rvar->id))
          out = Trinary_True;
      } break;

      case EC_Form:
      {
        if ((castExpression(lhs0, Form))->ctor_id ==
            (castExpression(rhs0, Form))->ctor_id)
          out = Trinary_True;
        else
          out = Trinary_False;
      } break;

      case EC_ArrowType:
      {
        // todo: important: comparison of dependent types wouldn't work
        // if we compare the scopes. we can fix it by comparing
        // stack_delta (which we're not storing right now)
        auto larrow = castExpression(lhs0, ArrowType);
        auto rarrow = castExpression(rhs0, ArrowType);
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
              lparam_types[param_id] = larrow->params[param_id]->type;
              rparam_types[param_id] = rarrow->params[param_id]->type;
            }

            out = compareExpressionList(lparam_types, rparam_types, param_count);
          }
          else
            out = Trinary_False;
        }
      } break;

      case EC_Application:
      {
        Application *lhs = castExpression(lhs0,  Application);
        Application *rhs = castExpression(rhs0,  Application);
        {
          Trinary op_compare = identicalTrinary(lhs->op, rhs->op);
          if ((op_compare == Trinary_False) &&
              (lhs->op->cat == EC_Form) &&
              (rhs->op->cat == EC_Form))
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

      case EC_Fork:
      {
        Fork *lhs = castExpression(lhs0, Fork);
        Fork *rhs = castExpression(rhs0, Fork);
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

      default:
          todoIncomplete;
    }
  }
  else if (((lhs0->cat == EC_Form) && isCompositeForm(rhs0)) ||
           ((rhs0->cat == EC_Form) && isCompositeForm(lhs0)))
  {
    out = Trinary_False;
  }

  return out;
}

inline void
printAst(Ast *ast0)
{
  MemoryArena *buffer = 0;
  switch (ast0->cat)
  {
    case AC_AstLeaf:
    {
      AstLeaf *in = castAst(ast0, AstLeaf);
      printToBuffer(buffer, in->h.token.text);
    } break;

    case AC_AstBranch:
    {
      AstBranch *in = castAst(ast0, AstBranch);
      printAst(in->op);
      printToBuffer(buffer, "(");
      for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
      {
        printAst(in->args[arg_id]);
        printToBuffer(buffer, ",");
      }
      printToBuffer(buffer, ")");
    } break;

    case AC_AstFork:
    {
      AstFork *in = castAst(ast0, AstFork);
      (void)in;
      printToBuffer(buffer, "fork");
    } break;

    case AC_AstArrowType:
    {
      AstArrowType *in = castAst(ast0, AstArrowType);
      (void)in;
      printToBuffer(buffer, "arrow");
    } break;

    invalidDefaultCase;
  }
}

struct PrintOptions{b32 detailed; b32 print_type;};

internal char*
printExpression(MemoryArena *buffer, Expression *in0, PrintOptions opt)
{
  unpackGlobals;
  char *out = buffer ? (char*)getArenaNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
      case EC_Constant:
      {
        Constant *in = castExpression(in0, Constant);
        printToBuffer(buffer, in->h.token.text);
      } break;

      case EC_Variable:
      {
        Variable *in = castExpression(in0, Variable);
#if 0
        if (in->stack_depth)
          printToBuffer(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
        else
          printToBuffer(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
#else
        printToBuffer(buffer, "%.*s", in->name.text.length, in->name.text.chars);
#endif

        if (opt.detailed || opt.print_type)
        {
          printToBuffer(buffer, ": ");
          printExpression(buffer, in->type, new_opt);
        }
      } break;

      case EC_Application:
      {
        Application *in = castExpression(in0, Application);

        printExpression(buffer, in->op, new_opt);

        printToBuffer(buffer, "(");
        for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
        {
          printExpression(buffer, in->args[arg_id], new_opt);
          if (arg_id < in->arg_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ")");

        if (opt.detailed || opt.print_type)
        {
          printToBuffer(buffer, ": ");
          printExpression(buffer, in->type, new_opt);
        }
      } break;

      case EC_Fork:
      {
        Fork *fork = castExpression(in0, Fork);
        printToBuffer(buffer, "fork ");
        printExpression(buffer, fork->subject, new_opt);
        printToBuffer(buffer, " {");
        Form *form = fork->form;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          ForkCase *casev = fork->cases + ctor_id;
          Form *ctor = form->ctors + ctor_id;
          switch (ctor->type->cat)
          {// print pattern
            case EC_Form:
            {
              printExpression(buffer, (Expression*)ctor, new_opt);
            } break;

            case EC_ArrowType:
            {
              printExpression(buffer, (Expression*)ctor, new_opt);
              printToBuffer(buffer, " ");
              ArrowType *signature = castExpression(ctor->type, ArrowType);
              for (s32 param_id = 0; param_id < signature->param_count; param_id++)
              {
                printToBuffer(buffer, &casev->params[param_id]->name);
                printToBuffer(buffer, " ");
              }
            } break;

            invalidDefaultCase;
          }

          printToBuffer(buffer, ": ");
          printExpression(buffer, casev->body, new_opt);
          if (ctor_id != form->ctor_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, "}");
      } break;

      case EC_Form:
      {
        Form *in = castExpression(in0, Form);
        if (equal(&in->name, "identical"))
          breakhere;
        if (opt.detailed && in != builtin_Type)
        {
          printToBuffer(buffer, &in->name);

          if (opt.print_type)
          {
            printToBuffer(buffer, ": ");
            printExpression(buffer, in->type, new_opt);
          }

          printToBuffer(buffer, " {");
          for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
          {
            Form *ctor = in->ctors + ctor_id;
            printToBuffer(buffer, &ctor->name);
            printToBuffer(buffer, ": ");
            printExpression(buffer, (Expression*)ctor->type, new_opt);
          }
          printToBuffer(buffer, " }");
        }
        else
          printToBuffer(buffer, &in->name);
      } break;

      case EC_Function:
      {
        Function *in = castExpression(in0, Function);
        printToBuffer(buffer, &in->name);
        if (opt.detailed)
        {
          printToBuffer(buffer, " { ");
          printExpression(buffer, in->body, new_opt);
          printToBuffer(buffer, " }");
        }
      } break;

      case EC_ArrowType:
      {
        auto arrow = castExpression(in0,  ArrowType);
        printToBuffer(buffer, "(");
        for (int param_id = 0;
             param_id < arrow->param_count;
             param_id++)
        {
          Variable *param = arrow->params[param_id];
          printToBuffer(buffer, &param->name);
          printToBuffer(buffer, ": ");
          printExpression(buffer, param->type, new_opt);
          if (param_id < arrow->param_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ") -> ");

        printExpression(buffer, arrow->return_type, new_opt);
      } break;

      case EC_Hole:
      {
        printToBuffer(buffer, "_");
      } break;

      case EC_Sequence:
      {
        Sequence *in = castExpression(in0, Sequence);
        for (s32 id = 0; id < in->count; id++)
        {
          printExpression(buffer, in->items[id], new_opt);
          if (id != in->count-1)
            printToBuffer(buffer, "; ");
        }
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
myprint(Expression *expr)
{
  printExpression(0, expr, {});
}

inline void
myprint(char *str)
{
  printToBuffer(0, str);
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
addGlobalBinding(String key, Expression *value)
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
addGlobalBinding(char *key, Expression *value)
{
  return addGlobalBinding(toString(key), value);
}

struct LookupNameRecursive { Expression *expr; b32 found; };

inline LookupNameRecursive
lookupLocalName(MemoryArena *arena, Bindings *bindings, Token *token)
{
  Expression *expr = {};
  b32 found = false;

  for (s32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupName lookup = lookupNameCurrentFrame(bindings, token->text, false);
    if (lookup.found)
    {
      found = true;
      Expression *value = lookup.slot->value;
      if (Variable *original_var = castExpression(value, Variable))
      {
        Variable *var = newExpression(arena, Variable, token);
        initVariable(var, token, original_var->id, original_var->type);
        var->stack_delta = stack_delta;
        expr = (Expression*)var;
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

inline Expression *
constantFromGlobalName(MemoryArena *arena, Token *token)
{
  Expression *out0 = 0;
  auto lookup = lookupNameCurrentFrame(global_bindings.v, token->text, false);
  if (lookup.found)
  {
    // Everything in the global scope becomes identifier.
    Expression *value = lookup.slot->value;
    Constant *out = newExpression(arena, Constant, token);
    initIdentifier(out, value);
    out0 = (Expression*)out;
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
addBuiltinForm(MemoryArena *arena, char *name, Expression *type, const char **ctor_names, s32 ctor_count)
{
  Token form_name = newToken(name);
  Form *form = newExpression(arena, Form, &form_name);

  Form *ctors = pushArray(arena, ctor_count, Form);
  for (s32 ctor_id = 0; ctor_id < ctor_count; ctor_id++)
  {
    Form *ctor = ctors + ctor_id;
    Token ctor_name = newToken(ctor_names[ctor_id]);
    initForm(ctor, &ctor_name, (Expression*)form, ctor_id);
    if (!addGlobalBinding(ctor->name.text, (Expression *)ctor))
      invalidCodePath;
  }

  initForm(form, &form_name, type, ctor_count, ctors, getNextFormId());
  if (!addGlobalBinding(form_name.text, (Expression*)form))
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
  Expression *name(Environment env, Variable *in, void *opt)

typedef VARIABLE_TRANSFORMER(variable_transformer);

#define TRANSFORM_VARIABLES                     \
  inline Expression *                           \
  transformVariables(Environment env, Expression *in, variable_transformer *transformer, void *opt)

// note: this makes a copy (todo: #mem don't copy if not necessary)
// todo cheesing out on functions right now
inline Expression *
transformVariables(Environment env, Expression *in0, variable_transformer *transformer, void *opt)
{
  Expression *out0 = 0;
  switch (in0->cat)
  {
    case EC_Variable:
    {
      Variable *in_var = castExpression(in0, Variable);
      out0 = transformer(env, in_var, opt);
    } break;

    case EC_Application:
    {
      Application *in  = castExpression(in0, Application);
      Application *out = copyStruct(env.arena, in);
      out0 = (Expression*)out;
      out->op = transformVariables(env, in->op, transformer, opt);
      allocateArray(env.arena, out->arg_count, out->args);
      for (s32 arg_id = 0; arg_id < out->arg_count; arg_id++)
      {
        out->args[arg_id] = transformVariables(env, in->args[arg_id], transformer, opt);
      }
    } break;

    case EC_Fork:
    {
      Fork *in_fork  = castExpression(in0, Fork);
      Fork *out_fork = copyStruct(env.arena, in_fork);
      out0 = (Expression*)out_fork;
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
  if (env.stack_offset == in->stack_delta)
    return args[in->id];
  else
    return (Expression*)in;
}

// think of a function application
internal Expression *
replaceCurrentLevel(Environment env, Expression *in, Expression **args)
{
  Expression *out = transformVariables(env, in, replaceCurrentLevelVariable, args);
  // assert(identicalB32(in->type, out->type));
  return out;
}

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
  Variable **atoms = pushArray(env->temp_arena, count, Variable*);
  s32 stack_depth = env->stack_depth+1;
  for (s32 id = 0; id < count; id++)
  {
    Variable *model = models[id];
    Variable *dst = copyStruct(env->temp_arena, model);
    atoms[id] = dst;
    dst->stack_depth = stack_depth;
  }
  extendStack(env, count, (Expression**)atoms);
  return (Expression**)atoms;
}

internal Expression **
introduceVariables(Environment *env, ArrowType *signature)
{
  return introduceVariables(env, signature->param_count, signature->params);
}

inline void
printRewrites(Environment env)
{
  for (Rewrite *rewrite = env.rewrite; rewrite; rewrite = rewrite->next)
  {
    printExpression(0, rewrite->lhs, {});
    printToBuffer(0, " => ");
    printExpression(0, rewrite->rhs, {});
    if (rewrite->next)
      printToBuffer(0, ", ");
  }
  printNewline();
}

inline Expression *
parseExpression(MemoryArena *arena);

// todo #speed don't pass the Environment in wholesale?
internal Expression *
normalize(Environment env, Expression *in0, b32 force_expand=false)
{
  Expression *out0 = 0;
  unpackGlobals;

  switch (in0->cat)
  {
    case EC_Constant:
    {
      Constant *in = castExpression(in0, Constant);
      out0 = in->value;
      if (in->value->cat != EC_Form)
        breakhere;
    } break;

    case EC_Variable:
    {
      Variable *in = castExpression(in0, Variable);
      if (!in->stack_depth
          && in->stack_delta >= env.stack_offset)
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

    case EC_Application:
    {
      Application *in = castExpression(in0, Application);

      Expression **norm_args = pushArray(temp_arena, in->arg_count, Expression*);
      for (auto arg_id = 0;
           arg_id < in->arg_count;
           arg_id++)
      {
        Expression *in_arg = in->args[arg_id];
        norm_args[arg_id]  = normalize(env, in_arg);
      }

      Expression *norm_op = normalize(env, in->op);
      if (norm_op->cat == EC_Function)
      {// Function application
        b32 has_any_variable = false;
        if (!force_expand)
        {
          for (s32 arg_id = 0;
               arg_id < in->arg_count && !has_any_variable;
               arg_id++)
          {
            if (hasAnyVariable(norm_args[arg_id]))
              has_any_variable = true;
          }
        }
        if (force_expand || !has_any_variable)
        {
          Function *fun = castExpression(norm_op, Function);
          Environment new_env = env;
          extendStack(&new_env, in->arg_count, norm_args);
          out0 = normalize(new_env, fun->body);
        }
      }
      else if (norm_op == (Expression*)builtin_identical)
      {// special case for equality
        Expression *lhs = norm_args[1];
        Expression *rhs = norm_args[2];
        Trinary compare = identicalTrinary(lhs, rhs);
        if (compare == Trinary_True)
          out0 = builtin_True;
        else if (compare == Trinary_False)
          out0 = builtin_False;
        else if (isCompositeForm(lhs)
                 && isCompositeForm(rhs))
        {// Leibniz' principle
          Application *lapp = castExpression(lhs, Application);
          Application *rapp = castExpression(rhs, Application);
          assert(identicalB32(lapp->op, rapp->op)); // if they aren't equal then it'd already be false.
          Application *out = copyStruct(env.arena, in);
          out0 = (Expression*)out;
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
        Application *out_app = copyStruct(env.arena, in);
        out0 = &out_app->h;

        out_app->op = norm_op;
        allocateArray(env.arena, out_app->arg_count, out_app->args);
        for (int arg_id = 0; arg_id < out_app->arg_count; arg_id++)
          out_app->args[arg_id] = norm_args[arg_id];
      }
    } break;

    case EC_Fork:
    {
      Fork *in = castExpression(in0, Fork);
      Expression *norm_subject = normalize(env, in->subject);

      Environment *outer_env = &env;
      Environment env = *outer_env;
      b32 subject_matched = false;
      switch (norm_subject->cat)
      {
        case EC_Form:
        {
          subject_matched = true;
          Form *ctor = castExpression(norm_subject, Form);
          extendStack(&env, 0, 0);
          out0 = normalize(env, in->cases[ctor->ctor_id].body);
        } break;

        case EC_Application:
        {
          Application *subject = castExpression(norm_subject, Application);
          if (Form *ctor = castExpression(subject->op, Form))
          {
            subject_matched = true;
            Expression *body = in->cases[ctor->ctor_id].body;
            extendStack(&env, subject->arg_count, subject->args);
            out0 = normalize(env, body);
          }
        } break;
      }

      if (!subject_matched)
      {
        Fork *out = copyStruct(env.arena, in);
        out->subject = norm_subject;
        out0 = (Expression*)out;
      }

#if 0
      if (!subject_matched)
      {
        Fork *out = copyStruct(env.arena, in);
        out0 = (Expression*)out;
        out->subject = norm_subject;
        allocateArray(env.arena, out->case_count, out->cases);
        Environment *outer_env = &env;
        for (s32 case_id = 0; case_id < out->case_count; case_id++)
        {
          Environment env = *outer_env;
          Form *ctor = in->form->ctors + case_id;
          switch (ctor->type->cat)
          {
            case EC_Form:
            {
              extendStack(&env, 0, 0);
            } break;

            case EC_ArrowType:
            {
              introduceVariables(&env,
                                 castExpression(ctor->type, ArrowType)->param_count,
                                 in->cases[case_id].params);
            } break;

            invalidDefaultCase;
          }
          out->cases[case_id]      = in->cases[case_id];
          out->cases[case_id].body = normalize(env, in->cases[case_id].body);
        }
      }
#endif
    } break;

    case EC_ArrowType:
    {
      ArrowType *in = castExpression(in0, ArrowType);
      ArrowType *out = copyStruct(env.arena, in);
      out0 = (Expression*)out;
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

  Expression *before_rewrite = out0;
  out0 = rewriteExpression(&env, out0);
  if (out0 != before_rewrite)
    out0 = normalize(env, out0); // do another iteration

  return out0;
}

inline Expression *
normalize(MemoryArena *arena, Expression *in0)
{
  return normalize(newEnvironment(arena), in0);
}

// todo: so what does the arena do exactly?
internal Expression *
normalizeStart(MemoryArena *arena, Expression *in)
{
  return normalize(newEnvironment(arena), in);
}

inline b32
normalized(Environment env, Expression *in)
{
  Expression *norm = normalize(env, in);
  return identicalB32(in, norm);
}

inline void
addRewrite(Environment *env, Expression *lhs0, Expression *rhs0)
{
  assert(normalized(*env, lhs0));
  assert(normalized(*env, rhs0));
  if (!identicalB32(lhs0, rhs0))
  {
    b32 added = false;

    if (Application *lhs = castExpression(lhs0, Application))
      if (Application *rhs = castExpression(rhs0, Application))
    {
      if ((lhs->op->cat == EC_Form) &&
          (rhs->op->cat == EC_Form))
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

#define BUILD_EXPRESSION                        \
  internal Expression *                         \
  buildExpression(MemoryArena *arena, Bindings *bindings, Ast *ast0)

BUILD_EXPRESSION;

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
    case EC_Fork:
    {
      Fork *in = castExpression(in0, Fork);
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

    case EC_Function:
    {
      Function *in = castExpression(in0, Function);

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

    case EC_Application:
    {
      Application *in = castExpression(in0, Application);
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

    case EC_ArrowType:
    {
      ArrowType *in = castExpression(in0, ArrowType);
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
  return (Expression*)out;
}

inline Expression *
rebaseDownExpr(MemoryArena *arena, Expression *in)
{
  s32 adjustment = +1;
  Expression *out = transformVariables(newEnvironment(arena), in, rebaseVariable, &adjustment);
  return out;
}

inline Expression *
rebaseUpExpr(MemoryArena *arena, Expression *in)
{
  s32 adjustment = -1;
  return transformVariables(newEnvironment(arena), in, rebaseVariable, &adjustment);
}

// TODO: oh man this is just a dispatch function. Really wished everything had
// type, huh?
inline Expression *
typeOfValue(Expression *in0)
{
  Expression *out = 0;
  switch (in0->cat)
  {
    case EC_Form:
    {
      Form *in = castExpression(in0, Form);
      out = in->type;
    } break;

    case EC_Application:
    {
      Application *in = castExpression(in0, Application);
      out = in->type;
    } break;

    case EC_Function:
    {
      Function *in = castExpression(in0, Function);
      out = (Expression*)in->signature;
    } break;

    invalidDefaultCase;
  }
  return out;
}

// NOTE: the output as well as "expected_type" are instantiated, but expression
// types are abstract.
internal Expression *
typecheck(Environment env, Expression *in0, Expression *expected_type)
{
  unpackGlobals;
  Expression *out0 = 0;

  switch (in0->cat)
  {
    case EC_Constant:
    {
      Constant *in = castExpression(in0, Constant);
      out0 = typeOfValue(in->value);
    } break;

    case EC_Form:
    {
      Form *in = castExpression(in0, Form);
      out0 = in->type;
    } break;

    case EC_Variable:
    {
      Variable *in = castExpression(in0, Variable);
      out0 = in->type;
    } break;

    case EC_Fork:
    {
      Fork *in = castExpression(in0, Fork);
      Environment *outer_env = &env;

      Form *form = in->form;

      Expression *common_type = expected_type;
      Expression *norm_subject = normalize(env, in->subject);
        
      for (s32 case_id = 0;
           case_id < in->case_count && noError();
           case_id++)
      {
        Environment  env = *outer_env;

        ForkCase *casev    = in->cases + case_id;

        Form       *ctor     = form->ctors + case_id;
        Expression *ctor_exp = (Expression*)ctor;

        switch (ctor->type->cat)
        {
          case EC_Form:
          {// member
            addRewrite(&env, norm_subject, ctor_exp);
            introduceVariables(&env, 0, 0);
          } break;

          case EC_ArrowType:
          {// composite
            ArrowType    *signature = castExpression(ctor->type, ArrowType);
            Expression  **params    = (Expression**)introduceVariables(&env, signature->param_count, casev->params);
            Application  *pattern   = newExpression(env.temp_arena, Application, &ctor->h.token);
            initApplication(pattern, ctor_exp, signature->param_count, params);
            addRewrite(&env, norm_subject, (Expression*)pattern);
          } break;

          default:
              invalidCodePath;
        }

        if (Expression *body_type = typecheck(env, casev->body, common_type))
        {
          if (!common_type)
          {
            // fork body has more specific type than outer scope???
            assert(!hasDeepVariable(*outer_env, body_type));
            common_type = body_type;
          }
        }
      }

      if (noError())
        out0 = common_type;
    } break;

    case EC_Function:
    {
      Function *in = castExpression(in0, Function);
      if (in->signature)
        out0 = (Expression*)in->signature;
      else if (expected_type)
      {
        if (ArrowType *expected_signature = castExpression(expected_type, ArrowType))
        {
          introduceVariables(&env, expected_signature);
          // Grant the function its type first, since the function body may call itself.
          in->signature = expected_signature;
          Expression *expected_body_type = normalize(env, expected_signature->return_type);
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

    case EC_Application:
    {
      Application *in = castExpression(in0, Application);
      if (in->type)
        out0 = in->type;
      else
      {
        s32 arg_count = in->arg_count;
        if (Expression *op_type = typecheck(env, in->op, 0))
        {
          if (ArrowType *signature = castExpression(op_type, ArrowType))
          {
            if (signature->param_count == arg_count)
            {
              // todo #memory we have a memory corruption here when using
              // temp_arena for signature_env.
              Environment signature_env = env;
              env.arena = temp_arena;
              Expression **stack_frame = pushArrayZero(temp_arena, arg_count, Expression*);
              extendStack(&signature_env, arg_count, stack_frame);
              for (int arg_id = 0;
                   (arg_id < arg_count) && noError();
                   arg_id++)
              {// Type inference for the arguments. todo: the hole stuff is
               // kinda hard-coded only for the equality.
                Expression *arg   = in->args[arg_id];
                Variable   *param = signature->params[arg_id];

                if (arg->cat != EC_Hole)
                {
                  Expression *norm_param_type = normalize(signature_env, param->type);
                  Expression *arg_type = typecheck(env, arg, norm_param_type);
                  stack_frame[arg_id] = normalize(env, arg);
                  if (norm_param_type == 0)
                  {
                    Variable *param_type_var = castExpression(param->type, Variable);
                    assert(param_type_var->stack_delta == 0);
                    stack_frame[param_type_var->id] = arg_type;
                  }
                }
              }
              
              if (noError())
              {
                Expression **norm_args = pushArray(env.arena, arg_count, Expression*);
                for (s32 arg_id = 0; arg_id < arg_count; arg_id++)
                {
                  norm_args[arg_id] = normalize(env, in->args[arg_id]);
                }
                extendStack(&env, arg_count, norm_args);
                out0 = normalize(env, signature->return_type);
                // TODO #speed we could choose to hold off this typing, since
                // most applications aren't referred to anyway.
                in->type = abstractExpression(env, out0);
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

    case EC_ArrowType:
    {
      ArrowType *in = castExpression(in0, ArrowType);
      introduceVariables(&env, in);
      if (typecheck(env, in->return_type, 0))
        out0 = (Expression*)builtin_Type;  // todo: it's not a form but somehow is a type?

    } break;

    case EC_Sequence:
    {
      Sequence *in = castExpression(in0, Sequence);
      for (s32 id = 0; id < in->count-1; id++)
      {
        Expression *item0 = in->items[id];
        if (item0->cat == EC_RewriteCommand)
        {
          RewriteCommand *item = castExpression(item0, RewriteCommand);
          if (item->lhs)
          {
            // todo: just try some rewrite rule here
            Expression *norm_lhs = item->lhs;
            Expression *norm_rhs = normalize(env, item->rhs);
            while (noError())
            {
              Expression *before = norm_lhs;
              norm_lhs = normalize(env, norm_lhs, true);
              if (identicalB32(norm_lhs, norm_rhs))
              {
                addRewrite(&env, normalize(env, item->lhs), norm_rhs);
                break;
              }
              else if (identicalB32(norm_lhs, before))
              {
                parseError(item0, "failed to prove legitimacy of rewrite rule");
              }
            }
          }
          else
          {
            if (Expression *rewrite_rule0 = typecheck(env, item->proof, 0))
            {
              b32 rule_valid = false;
              Expression *norm_rule0 = normalize(env, rewrite_rule0);
              if (Application *norm_rule = castExpression(norm_rule0, Application))
              {
                if (norm_rule->op == (Expression*)builtin_identical)
                {
                  rule_valid = true;
                  addRewrite(&env, norm_rule->args[1], norm_rule->args[2]);
                }
              }
              if (!rule_valid)
                parseError(item0, "invalid rewrite rule, can only be equality");
            }
          }
        }
      }
      if (noError())
      {
        // typechecking is done on the last item
        out0 = typecheck(env, in->items[in->count-1], expected_type);
      }
    } break;

    invalidDefaultCase;
  }

  Expression *out = 0;
  if (noError())
  {
    assert(out0);
    Expression *norm_actual = normalize(env, out0);
    b32 matched = true;
    if (expected_type)
    {
      Expression *norm_expected = normalize(env, expected_type);
      if (!identicalB32(norm_expected, norm_actual))
      {
        matched = false;
        identicalB32(norm_expected, norm_actual);
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

internal Expression *
typecheck(MemoryArena *arena, Expression *in, Expression *expected_type)
{
  Expression *out = typecheck(newEnvironment(arena), in, expected_type);
  return out;
}

struct ExpressionParsing
{
  Expression *expression;
  Ast        *ast;
  Expression *type;
  operator bool() { return (bool)ast; }
};

inline ExpressionParsing
parseExpressionAndTypecheck(MemoryArena *arena, Bindings *bindings, Expression *expected_type)
{
  unpackGlobals;
  ExpressionParsing out = {};
  if (Ast *ast = parseExpressionToAst(global_temp_arena))
  {
    if (Expression *expression = buildExpression(arena, bindings, ast))
    {
      if (Expression *type = typecheck(newEnvironment(arena), expression, expected_type))
      {
        out.expression = expression;
        out.ast        = ast;
        out.type       = type;
      }
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline Expression *
parseExpression(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0).expression;
}

inline ExpressionParsing
parseExpressionFull(MemoryArena *arena)
{
  return parseExpressionAndTypecheck(arena, 0, 0);
}

internal Expression *
a2e(MemoryArena *arena, Ast *ast0)
{
  Expression *out0 = 0;
  switch (ast0->cat)
  {
    case AC_AstLeaf:
    {
      AstLeaf *in = castAst(ast0, AstLeaf);
      if (equal(&in->h.token, '_'))
        out0 = hole_expression;
      else
      {
        out0 = (Expression *)newExpression(arena, Identifier, &ast0->token);
      }
    } break;

    case AC_AstBranch:
    {
      AstBranch *ast = castAst(ast0, AstBranch);
      if (Expression *op = a2e(arena, ast->op))
      {
        s32 arg_count = ast->arg_count;
        Expression **args = pushArray(arena, arg_count, Expression*);
        for (s32 arg_id = 0;
             (arg_id < arg_count) && noError();
             arg_id++)
        {
          args[arg_id] = a2e(arena, ast->args[arg_id]);
        }
        if (noError())
        {
          Application *out = newExpression(arena, Application, &ast->h.token);
          initApplication(out, op, arg_count, args);
          out0 = (Expression*)out;
        }
      }
    } break;

    case AC_AstArrowType:
    {
      AstArrowType *ast = castAst(ast0, AstArrowType);
      ArrowType *out = newExpression(arena, ArrowType, &ast0->token);

      Variable **params = pushArray(arena, ast->param_count, Variable*);
      for (s32 param_id = 0;
           param_id < ast->param_count && noError();
           param_id++)
      {
        Parameter *ast_param = ast->params + param_id;
        Variable *param = params[param_id] = newExpression(arena, Variable, &ast_param->name);
        initVariable(param, &ast_param->name, param_id, a2e(arena, ast_param->type));
      }

      initArrowType(out, ast->param_count, params, a2e(arena, ast->return_type));
      out0 = (Expression *)out;
    } break;

    case AC_AstSequence:
    {
      AstSequence *ast = castAst(ast0, AstSequence);
      s32          count = ast->count;
      Expression **items = pushArray(arena, count, Expression*);
      for (s32 id = 0; (id < count) && noError(); id++)
      {
        items[id] = a2e(arena, ast->items[id]);
      }
      if (noError())
      {
        Sequence *out = newExpression(arena, Sequence, &ast0->token);
        initSequence(out, count, items);
        out0 = (Expression*)out;
      }
    } break;

    case AC_AstRewriteCommand:
    {
      AstRewriteCommand *ast = castAst(ast0, AstRewriteCommand);
      if (ast->lhs)
      {
        if (Expression *lhs = a2e(arena, ast->lhs))
          if (Expression *rhs = a2e(arena, ast->rhs))
          {
            RewriteCommand *out = newExpression(arena, RewriteCommand, &ast0->token);
            out->lhs   = lhs;
            out->rhs   = rhs;
            out->proof = 0;
            out0 = (Expression*)out;
          }
      }
      else if (Expression *proof = a2e(arena, ast->proof))
      {
        RewriteCommand *out = newExpression(arena, RewriteCommand, &ast0->token);
        out->lhs   = 0;
        out->rhs   = 0;
        out->proof = proof;
        out0 = (Expression*)out;
      }
    } break;

    case AC_AstFork:
    {
      AbstractFork *out = newExpression(arena, AbstractFork, &ast0->token);
      AstFork      *ast = castAst(ast0, AstFork);

      out->subject = a2e(arena, ast->subject);
      s32 case_count = ast->case_count;
      out->case_count = case_count;
      allocateArray(arena, case_count, out->patterns);
      allocateArray(arena, case_count, out->bodies);
      for (s32 input_case_id = 0;
           (input_case_id < case_count) && parsing();
           input_case_id++)
      {
        out->patterns[input_case_id] = a2e(arena, ast->patterns[input_case_id]);
        out->bodies[input_case_id]   = a2e(arena, ast->bodies[input_case_id]);
      }
      out0 = (Expression*)out;
    } break;

    invalidDefaultCase;
  }
  return out0;
}

// note: Manipulation may be done in-place, but we might also allocate new
// memory, so beware!
internal Expression *
buildExpression(MemoryArena *arena, Bindings *bindings, Expression *in0)
{
  unpackGlobals;
  Expression *out0 = in0;

  switch (in0->cat)
  {
    case EC_Hole:
    {
      out0 = hole_expression;
    } break;

    case EC_Identifier:
    {
      auto lookup = lookupLocalName(arena, bindings, &in0->token);
      if (lookup.found)
        out0 = lookup.expr;
      else
      {
        if (Expression *constant = constantFromGlobalName(arena, &in0->token))
          out0 = constant;
        else
          parseError(in0, "unbound identifier in expression");
      }
    } break;

    case EC_Application:
    {
      Application *in = castExpression(in0, Application);
      if ((in->op = buildExpression(arena, bindings, in->op)))
      {
        s32 arg_count = in->arg_count;
        for (s32 arg_id = 0;
             (arg_id < arg_count) && noError();
             arg_id++)
        {
          in->args[arg_id] = buildExpression(arena, bindings, in->args[arg_id]);
        }
        if (noError())
          out0 = in0;
      }
    } break;

    case EC_ArrowType:
    {
      ArrowType *in = castExpression(in0, ArrowType);

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
          addBinding(bindings, param->name.text, (Expression*)param);
      }

      if (noError())
      {
        if ((in->return_type = buildExpression(arena, bindings, in->return_type)))
          out0 = in0;
      }
    } break;

    case EC_Sequence:
    {
      Sequence *in = castExpression(in0, Sequence);
      for (s32 id = 0; id < in->count && noError(); id++)
      {
        in->items[id] = buildExpression(arena, bindings, in->items[id]);
      }
      if (noError())
        out0 = in0;
    } break;

    case EC_RewriteCommand:
    {
      RewriteCommand *in = castExpression(in0, RewriteCommand);
      if (in->lhs)
      {
        if (Expression *lhs = buildExpression(arena, bindings, in->lhs))
          if (Expression *rhs = buildExpression(arena, bindings, in->rhs))
          {
            in->lhs = lhs;
            in->rhs = rhs;
            out0 = in0;
          }
      }
      else if (Expression *proof = buildExpression(arena, bindings, in->proof))
      {
        in->proof = proof;
        out0 = in0;
      }
    } break;

    case EC_AbstractFork:
    {
      AbstractFork *in = castExpression(in0, AbstractFork);
      Fork *out = 0;

      Bindings *outer_bindings = bindings;
      if (Expression *subject = buildExpression(arena, outer_bindings, in->subject))
      {
        if (Expression *subject_type = typecheck(newEnvironment(arena), subject, 0))
        {
          if (Form *form = castExpression(subject_type, Form))
          {
            s32 case_count = in->case_count;
            if (form->ctor_count == case_count)
            {
              if (case_count == 0)
                parseError((Ast*)in, "todo: cannot assign type to empty fork");
              else
              {
                ForkCase *cases = pushArrayZero(arena, case_count, ForkCase);
        
                for (s32 input_case_id = 0;
                     (input_case_id < case_count) && parsing();
                     input_case_id++)
                {
                  Bindings *bindings = extendBindings(global_temp_arena, outer_bindings);

                  Expression *ast_pattern = in->patterns[input_case_id];
                  Form *ctor = 0;
                  Variable **params;
                  s32 param_count;
                  pushContextName("transform switch case pattern");
                  switch (ast_pattern->cat)
                  {
                    case EC_Identifier:
                    {
                      params = 0;
                      param_count = 0;
                      if (Expression *pattern = buildExpression(temp_arena, outer_bindings, ast_pattern))
                      {
                        Expression *norm_pattern = normalize(temp_arena, pattern);
                        if ((ctor = castExpression(norm_pattern, Form)))
                        {
                          if (!identicalB32(ctor->type, subject_type))
                          {
                            parseError(ast_pattern, "constructor of wrong type");
                            pushAttachment("expected type", subject_type);
                            pushAttachment("got type", ctor->type);
                          }
                        }
                        else
                          parseError(ast_pattern, "expected a member constructor");
                      }
                    } break;

                    case EC_Application:
                    {
                      Application *branch = castExpression(ast_pattern, Application);
                      if (Expression *op0 = buildExpression(arena, outer_bindings, branch->op))
                      {
                        Expression *op = normalize(temp_arena, op0);
                        if ((ctor = castExpression(op, Form)))
                        {
                          if (ArrowType *ctor_sig = castExpression(ctor->type, ArrowType))
                          {
                            if (identicalB32(ctor_sig->return_type, subject_type))
                            {
                              param_count = branch->arg_count;
                              if (param_count == ctor_sig->param_count)
                              {
                                allocateArrayZero(arena, param_count, params);
                                for (s32 param_id = 0; param_id < param_count; param_id++)
                                {// MARK: loop over pattern variables
                                  Expression *ast_arg = branch->args[param_id];
                                  if (Identifier *arg = castExpression(ast_arg, Identifier))
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
                                      param->name = *param_name;
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
                              parseError(ast_pattern, "composite constructor has wrong return type (todo: support more flexible return type)");
                              pushAttachment("expected type", subject_type);
                              pushAttachment("got type", ctor_sig->return_type);
                            }
                          }
                          else
                          {
                            parseError(branch->op, "expected a composite constructor");
                            pushAttachment("got type", (Expression*)ctor_sig);
                          }
                        }
                        else
                          parseError(ast_pattern, "expected a composite constructor");
                      }
                    } break;

                    invalidDefaultCase;
                  }
                  popContext();

                  Expression *body = 0;
                  if (noError())
                  {
                    pushContextName("fork case body building");
                    Expression *ast_body = in->bodies[input_case_id];
                    body = buildExpression(arena, bindings, ast_body);
                    popContext();
                  }

                  if (noError())
                  {
                    // we could error out sooner but whatevs.
                    if (cases[ctor->ctor_id].body)
                    {
                      parseError(in->bodies[input_case_id], "fork case handled twice");
                      pushAttachment("constructor", (Expression*)ctor);
                    }
                    else
                      initForkCase(cases + ctor->ctor_id, body, params, param_count);
                  }
                }

                if (noError())
                {
                  out = newExpression(arena, Fork, &in->h.token);
                  initFork(out, form, subject, case_count, cases);
                }
              }
            }
            else
              parseError((Ast*)in, "wrong number of cases, expected: %d, got: %d",
                         form->ctor_count, in->case_count);
          }
          else
            parseError(in->subject, "cannot fork this expression");
        }
      }

      out0 = (Expression *)out;
    } break;

    invalidDefaultCase;
  }

  NULL_WHEN_ERROR(out0);
  return out0;
}

BUILD_EXPRESSION
{
  return buildExpression(arena, bindings, a2e(arena, ast0));
}

inline Expression *
buildExpressionGlobal(MemoryArena *arena, Ast *ast)
{
  return buildExpression(arena, 0, ast);
}

inline Ast *
parseSequence(MemoryArena *arena)
{
  unpackGlobals;
  Token first_token = tk->last_token;
  Ast *out = 0;
  s32 count = 0;
  AstList *list = 0;
  while (parsing())
  {
    Token next = peekNext();
    if (isExpressionEndMarker(&next))
      break;
    else if (Ast *expr = parseExpressionToAst(arena))
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->first = expr;
      new_list->next = list;
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
      {
        out = list->first;
        // bookmark: maybe these expressions can have type void?
        if (out->cat == AC_AstRewriteCommand)
          parseError(&first_token, "command cannot stand alone");
      }
      else
      {
        Ast **items = pushArray(arena, count, Ast*);
        for (s32 id = count-1; id >= 0; id--)
        {
          items[id] = list->first;
          list = list->next;
        }
        if (items[count-1]->cat == AC_AstRewriteCommand)
          parseError(&first_token, "the last expression in a sequence cannot be a command");
        else
          out = (Ast*)newAstSequence(arena, &first_token, count, items);
      }
    }
  }
  return out;
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
          patterns[input_case_id] = parseExpressionToAst(arena);
          if (noError())
          {
            pushContextName("fork body");
            if (requireChar(':', "syntax: CASE: BODY"))
            {
              Ast *body = parseSequence(arena);
              bodies[input_case_id] = body;
              if (noError())
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
    if (requireCategory(TC_Arrow, "syntax: (param: type, ...) -> ReturnType"))
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
      Token identical_token = newToken("identical");
      Token hole_token = newToken("_");

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

internal AstRewriteCommand *
parseRewrite(MemoryArena *arena)
{
  unpackGlobals;
  AstRewriteCommand *out = 0;
  Token token = tk->last_token;
  if (Ast *lhs = parseExpressionToAst(arena))
  {
    if (optionalCategory(TC_StrongArrow))
    {
      if (Ast *rhs = parseExpressionToAst(arena))
      {
        out = newAst(arena, AstRewriteCommand, &token);
        initAstRewriteCommand(out, lhs, rhs);
      }
    }
    else
    {
      out = newAst(arena, AstRewriteCommand, &token);
      initAstRewriteCommand(out, lhs);
    }
  }
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

      case Keyword_Rewrite:
      {
        out = (Ast *)parseRewrite(arena);
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
      if (noError(&tk_copy))
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

internal Form *
parseConstructorDef(MemoryArena *arena, Form *out, Form *form, s32 ctor_id)
{
  unpackGlobals;
  pushContext;

  Token ctor_token = nextToken(tk);
  if (equal(&ctor_token, "refl"))
    breakhere;
  if (isIdentifier(&ctor_token))
  {
    if (addGlobalBinding(ctor_token.text, (Expression*)out))
    {
      if (optionalChar(':'))
      {
        if (Expression *parsed_type = parseExpressionFull(arena).expression)
        {
          Expression *type0 = normalize(arena, parsed_type);
          b32 valid_type = false;
          if (Form *type = castExpression(type0, Form))
          {
            if (type == form)
              valid_type = true;
          }
          else if (ArrowType *type = castExpression(type0, ArrowType))
          {
            if (getFormOf(type->return_type) == form)
              valid_type = true;
          }

          if (valid_type)
            initForm(out, &ctor_token, type0, ctor_id);
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
        if (form->type == (Expression*)builtin_Set)
          initForm(out, &ctor_token, (Expression*)form, ctor_id);
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
  unpackGlobals;
  pushContext;

  Token form_name = nextToken(tk);
  if (isIdentifier(&form_name))
  {
    Form *form = newExpression(arena, Form, &form_name);
    // NOTE: the type is in scope of its own constructor.
    if (addGlobalBinding(form_name.text, (Expression*)form))
    {
      Expression *type = (Expression*)builtin_Set;
      if (optionalChar(':'))
      {// type override
        b32 valid_type = false;
        if (ExpressionParsing type_parsing = parseExpressionFull(arena))
        {
          Expression *norm_type = normalize(temp_arena, type_parsing.expression);
          if (ArrowType *arrow = castExpression(norm_type, ArrowType))
          {
            if (arrow->return_type == (Expression*)builtin_Set)
              valid_type = true;
          }
          else if (norm_type == (Expression*)builtin_Set)
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
        Tokenizer tk_copy = *tk;
        s32 expected_ctor_count = getCommaSeparatedListLength(&tk_copy);
        // NOTE: init here for recursive definition
        if (noError(&tk_copy))
        {
          Form *ctors = pushArray(arena, expected_ctor_count, Form);
          initForm(form, &form_name, type, expected_ctor_count, ctors, getNextFormId());
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

// todo currently only top level definition
internal void
parseFunction(MemoryArena *arena, Token *name)
{
  unpackGlobals;
  pushContext;

  assert(isIdentifier(name));
  char *debug_name = "andWithFalse";
  if (equal(toString(debug_name), name->text))
    breakhere;

  if (auto [signature0, signature_ast, _] = parseExpressionFull(arena))
  {
    if (ArrowType *signature = castExpression(signature0, ArrowType))
    {
      Function *fun = newExpression(arena, Function, name);
      if (addGlobalBinding(name->text, (Expression*)fun))
      {
        // note: we have to rebuild the function's local bindings (todo: parse
        // signature+body together?)
        Bindings *fun_bindings = extendBindings(arena, 0);
        for (s32 param_id = 0;
             param_id < signature->param_count;
             param_id++)
        {
          Variable *param = signature->params[param_id];
          b32 add = addBinding(fun_bindings, param->name.text, (Expression*)param);
          assert(add);
        }

        if (requireChar('{', "open function body"))
        {
          if (Ast *body_ast = parseSequence(arena))
          {
            Expression *body = buildExpression(arena, fun_bindings, body_ast);
            if (requireChar('}'))
            {
              initFunction(fun, name, body);
              typecheck(arena, (Expression*)fun, (Expression*)signature);
            }
          }
        }
      }
      else
        tokenError("re-definition");
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
  MemoryArena *temp_arena = global_temp_arena;

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
              Expression *reduced = normalizeStart(temp_arena, parsing.expression);
              printExpression(0, reduced, {.detailed=true});
              printToBuffer(0, ": ");
              printExpression(0, parsing.type, {});
              printNewline();
            }
            requireChar(';');
          } break;

          case Keyword_PrintRaw:
          {
            if (auto parsing = parseExpressionFull(temp_arena))
            {
              printExpression(0, parsing.expression, {.detailed=true});
              printToBuffer(0, ": ");
              printExpression(0, parsing.type, {});
              printNewline();
            }
            requireChar(';');
          } break;

          case Keyword_PrintDebug:
          {
            if (Expression *exp = parseExpression(temp_arena))
            {
              char *output = printExpression(temp_arena, exp, {.detailed=true, .print_type=true});
              printf("%s\n", output);
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
            Expression *value = parseExpression(arena);
            Expression *norm  = normalizeStart(arena, value);
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

inline Expression *
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
          printExpression(0, attachment.expression, {});
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
    checkArena(global_temp_arena);

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
    builtin_Set  = castExpression(lookupGlobalName("Set"), Form);
    builtin_Type->type = (Expression*)builtin_Type; // todo: circular types are gonna bite us

    allocate(arena, hole_expression);
    hole_expression->cat = EC_Hole;

    {// Equality
      b32 success = interpretFile(state, platformGetFileFullPath(arena, "../data/builtins.rea"), true);
      assert(success);
      builtin_identical = castExpression(lookupGlobalName("identical"), Form);
    }

    const char *true_members[] = {"truth"};
    addBuiltinForm(arena, "True", (Expression*)builtin_Set, true_members, 1);
    builtin_True  = lookupGlobalName("True");
    builtin_truth = lookupGlobalName("truth");

    addBuiltinForm(arena, "False", (Expression*)builtin_Set, (const char **)0, 0);
    builtin_False = lookupGlobalName("False");
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
  global_temp_arena_ = newArena(temp_memory_size, temp_memory_base);
  global_temp_arena  = &global_temp_arena_;

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

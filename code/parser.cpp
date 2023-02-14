#include "engine.h"
#include "lexer.cpp"

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
  if (inString(")]}{,;:", token))
  {
    return true;
  }

  // Halt at all directives
  if (token->kind == Token_Directive)
  {
    return true;
  }

  switch (token->kind)
  {
    case Token_DoubleColon:
    case Token_ColonEqual:
    case Token_DoubleDash:
    case Token_StrongArrow:
    case Token_Keyword_in:
    case Token_DoubleDot:
    {
      return true;
    }
    default: {}
  }

  return false;
}

inline b32
seesExpressionEndMarker()
{
  Token token = peekToken();
  return isExpressionEndMarker(&token);
}

inline b32
requireChar(char c, char *reason=0)
{
  auto out = false;
  if (!reason)
    reason = "";
  if (hasMore())
  {
    Token token = nextToken();
    if (token.string.length == 1 && token.string.chars[0] == c)
      out = true;
    else
      reportError(&token, "expected character '%c' (%s)", c, reason);
  }
  return out;
}

inline b32
requireKind(TokenKind tc, char *message=0)
{
  b32 out = false;
  if (hasMore())
  {
    if (nextToken().kind == tc) out = true;
    else tokenError(message);
  }
  return out;
}

inline b32
requireIdentifier(char *message=0)
{
  b32 out = false;
  if (!message)
  {
    message = "expected identifier";
  }
  if (hasMore())
  {
    Token token = nextToken();
    if (isIdentifier(&token)) out = true;
    else tokenError(message);
  }
  return out;
}

inline b32
optionalIdentifier()
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken();
    if (isIdentifier(&token))
    {
      eatToken();
      out = true;
    }
  }
  return out;
}

inline b32
optionalKind(TokenKind tc)
{
  b32 out = false;
  if (hasMore())
    if (peekToken().kind == tc)
    {
      out = true;
      eatToken();
    }
  return out;
}

inline b32
optionalDirective(char *string)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken();
    if (token.kind == Token_Directive)
    {
      if (equal(token.string, string))
      {
        out = true;
        eatToken();
      }
    }
  }
  return out;
}

inline b32
optionalChar(char c)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken();
    if (equal(&token, c))
    {
      out = true;
      nextToken();
    }
  }
  return out;
}

inline b32
requireString(char *str)
{
  b32 out = false;
  if (hasMore())
  {
    eatToken();
    if (equal(lastToken(), str))
    {
      out = true;
    }
    else
    {
      reportError(lastToken(), "expected string %s", str);
    }
  }
  return out;
}

inline b32
optionalString(char *str)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken();
    if (equal(&token, str))
    {
      out = true;
      nextToken();
    }
  }
  return out;
}

inline Ast **
getAstBody(Ast *item0)
{
  // todo Puzzler: How do we make this nicer?
  if (Let *let = castAst(item0, Let))
  {
    return &let->body;
  }
  if (RewriteAst *rewrite = castAst(item0, RewriteAst))
  {
    return &rewrite->body;
  }
  if (GoalTransform *item = castAst(item0, GoalTransform))
  {
    return &item->body;
  }
  if (Invert *item = castAst(item0, Invert))
  {
    return &item->body;
  }
  if (SubstAst *item = castAst(item0, SubstAst))
  {
    return &item->body;
  }

  invalidCodePath;
  return 0;
}

inline Ast *
parseSequence(b32 require_braces=true)
{
  Arena *arena = temp_arena;
  i32 unused_var serial = DEBUG_SERIAL++;
  Ast *out = 0;
  i32 count = 0;
  AstList *list = 0;

  b32 brace_opened = false;
  if (require_braces) brace_opened = requireChar('{');
  else                brace_opened = optionalChar('{');

  for (b32 expect_sequence_to_end = false;
       noError() && !expect_sequence_to_end;
       )
  {
    // Can't get out of this rewind business, because sometimes the sequence is empty :<
    Tokenizer tk_save = *TK;
    Token  token_ = nextToken();
    Token *token  = &token_;
    Ast *ast0 = 0;
    String tactic = token->string;
    if (equal(tactic, "norm"))
    {
      pushContext("norm [EXPRESSION]");
      String name_to_unfold = {};

      if (optionalString("unfold"))
      {
        pushContext("unfold(FUNCTION_NAME)");
        if (requireChar('('))
        {
          if (requireIdentifier("expect function name"))
          {
            name_to_unfold = lastToken()->string;
            requireChar(')');
          }
        }
        popContext();
      }

      if (noError())
      {
        NormalizeMeAst *ast_goal = newAst(arena, NormalizeMeAst, token);
        ast_goal->name_to_unfold = name_to_unfold;
        if (seesExpressionEndMarker())
        {// normalize goal
          GoalTransform *ast = newAst(arena, GoalTransform, token);
          ast->new_goal = ast_goal;
          ast0 = ast;
        }
        else if (Ast *expression = parseExpression())
        {// normalize with let.
          Let *let = newAst(arena, Let, token);
          let->rhs  = expression;
          let->type = ast_goal;
          ast0 = let;
          if (expression->kind == Ast_Identifier)
          {
            // borrow the name if the expression is an identifier 
            let->lhs  = expression->token.string;
          }
          else
          {
            // NOTE This case can happen if it's a "seek"
          }
        }
      }

      popContext();
    }
    else if (equal(tactic, "rewrite"))
    {
      // todo maybe "with" should be "using", since we take "rewrite a with b"
      // to mean "replace a by b"
      pushContext("rewrite [with] EXPRESSION [in EXPRESSION]");
      RewriteAst *rewrite = newAst(arena, RewriteAst, token);
      if (optionalString("<-"))
      {
        rewrite->right_to_left = true;
      }
      b32 has_with = optionalString("with");

      if (Ast *expression = parseExpression())
      {
        if (has_with) rewrite->eq_proof = expression;
        else          rewrite->eq       = expression;

        if (optionalKind(Token_Keyword_in))
        {
          rewrite->in_expression = parseExpression();
        }
        ast0 = rewrite;
      }

      popContext();
    }
    else if (equal(tactic, "=>"))
    {
      pushContext("Goal transform: => NEW_GOAL [{ EQ_PROOF_HINT }]; ...");
      GoalTransform *ast = newAst(arena, GoalTransform, token);
      ast0 = ast;
      if (optionalDirective("print_proof"))
      {
        ast->print_proof = true;
      }
      if (optionalString("norm"))
      {
        ast->new_goal = newAst(arena, NormalizeMeAst, token);
      }
      else
      {
        ast->new_goal = parseExpression();
        if (optionalChar('{'))
        {
          if (optionalChar('}'))
          {
            // no hint provided, this case is just for editing convenience.
          }
          else
          {
            ast->hint = parseExpression();
            requireChar('}');
          }
        }
      }
      popContext();
    }
    else if (equal(tactic, "prove"))
    {
      pushContext("prove PROPOSITION {SEQUENCE} as IDENTIFIER");  // todo don't need the "as" anymore
      if (Ast *proposition = parseExpression())
      {
        if (Ast *proof = parseSequence(true))
        {
          String name = {};
          // String name = toString("anon");  // bookmark do we need this?
          if (optionalString("as") && requireIdentifier("expected name for the proof"))
          {
            name = lastToken()->string;
          }
          if (noError())
          {
            Let *let = newAst(arena, Let, token);
            let->lhs  = name;
            let->rhs  = proof;
            let->type = proposition;
            ast0 = let;
          }
        }
      }
      popContext();
    }
    else if (equal(tactic, "pose"))
    {
      pushContext("pose EXPRESSION");
      if (Ast *expression = parseExpression())
      {
        if (noError())
        {
          Let *let = newAst(arena, Let, token);
          let->rhs  = expression;
          ast0 = let;
        }
      }
      popContext();
    }
    else if (equal(tactic, "return"))
    {
      ast0 = parseExpression();
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "fork"))
    {
      ast0 = parseFork();
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "seek"))
    {
      SeekAst *ast = newAst(arena, SeekAst, token);
      ast0 = ast;
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "reductio"))
    {
      ReductioAst *ast = newAst(arena, ReductioAst, token);
      ast0 = ast;
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "invert"))
    {
      Invert *ast = newAst(arena, Invert, token);
      ast->pointer = parseExpression();
      ast0 = ast;
    }
    else if (equal(tactic, "use"))
    {
      if (requireIdentifier())
      {
        Token op_name = *lastToken();

        CompositeAst *ast = newAst(arena, CompositeAst, token);
        ast->op           = newAst(arena, Identifier, &op_name);
        ast->partial_args = true;

        if (optionalString("with"))
        {
          i32 cap = 16;  // todo #grow
          ast->keywords = pushArray(arena, cap, String);
          ast->args     = pushArray(arena, cap, Ast *);
          for (; noError();)
          {
            if (optionalIdentifier())
            {
              i32 arg_i = ast->arg_count++;
              assert(arg_i < cap);
              ast->keywords[arg_i] = lastToken()->string;
              if (requireChar('='))
              {
                if (Ast *arg = parseExpression())
                {
                  ast->args[arg_i] = arg;
                }

                if (!optionalChar(','))
                  break;
              }
            }
            else
              break;
          }
        }

        ast0 = ast;
        expect_sequence_to_end = true;
      }
    }
    else if (equal(tactic, "subst"))
    {
      SubstAst *ast = newAst(arena, SubstAst, token);
      i32 cap = 16;  // todo #grow
      ast->to_rewrite = pushArray(arena, cap, Ast *);
      for (; noError(); )
      {
        if (Ast *expression = parseExpression())
        {
          i32 i = ast->count++;
          assert(i < cap);
          ast->to_rewrite[i] = expression;
          lastToken();
        }

        if (!optionalChar(','))
          break;
      }
      ast0 = ast;
    }
    else if (isIdentifier(token))
    {
      // NOTE: identifiers can't be tactics, but I don't think that's a concern.
      Token *name = token;
      Token after_name = nextToken();
      switch (after_name.kind)
      {
        case Token_ColonEqual:
        {
          pushContext("let: NAME := VALUE");
          if (Ast *rhs = parseExpression())
          {
            Let *let = newAst(arena, Let, name);
            ast0 = let;
            let->lhs = name->string;
            let->rhs = rhs;
          }
          popContext();
        } break;

        case Token_Colon:
        {
          pushContext("typed let: NAME : TYPE := VALUE");
          if (Ast *type = parseExpression())
          {
            if (requireKind(Token_ColonEqual, ""))
            {
              if (Ast *rhs = parseExpression())
              {
                Let *let = newAst(arena, Let, name);
                let->lhs  = name->string;
                let->rhs  = rhs;
                let->type = type;
                ast0 = let;
              }
            }
          }
          popContext();
        } break;

        default:
        {
          reportError("invalid syntax for sequence item (keep in mind that we're in a sequence, so you need to use the \"return\" keyword to return an expression)");
        } break;
      }
    }
    else if (isExpressionEndMarker(token))
    {// synthetic hole
      ast0  = newAst(arena, Hole, token);
      *TK = tk_save;
      expect_sequence_to_end = true;
    }
    else
    {
      reportError("expected a sequence item");
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->head = ast0;
      new_list->tail  = list;
      list = new_list;
      // f.ex function definitions doesn't need to end with ';'
      optionalChar(';');
    }
  }

  if (brace_opened) requireChar('}');

  if (noError())
  {
    assert(count > 0);
    Ast *previous = 0;
    for (i32 item_i = 0; item_i < count; item_i++)
    {
      Ast *item0 = list->head;
      if (item_i > 0)
      {
        *getAstBody(item0) = previous;
      }
      previous = item0;
      if (item_i != count-1)
        list = list->tail;
    }
    out = list->head;
  }

  return out;
}

inline CtorAst *
parseCtorAst(Arena *arena)
{
  CtorAst *out = newAst(arena, CtorAst, &TK->last_token);
  if (requireChar('['))
  {
    out->ctor_i = parseInt32();
    requireChar(']');
  }
  return out;
}

inline SeekAst *
parseSeek(Arena *arena)
{
  SeekAst *seek = newAst(arena, SeekAst, &TK->last_token);
  if (!seesExpressionEndMarker())
  {
    seek->proposition = parseExpression();
  }
  return seek;
}

inline Ast *
parseOverload(Arena *arena)
{
  OverloadAst *out = newAst(arena, OverloadAst, lastToken());
  if (requireChar('('))
  {
    if (requireIdentifier("require a function name"))
    {
      out->function_name = *lastToken();
      if (requireChar(','))
      {
        if (requireIdentifier())
        {
          out->distinguisher = lastToken()->string;
        }
      }
    }
    requireChar(')');
  }
  if (hasError()) out = 0;
  return out;
}

internal ArrowAst *
parseArrowType(Arena *arena, b32 is_struct)
{
  ArrowAst *out = 0;
  i32      param_count = 0;
  String  *param_names;
  Ast    **param_types;
  u32     *param_flags;
  Token marking_token = peekToken();
  char begin_arg_char = '(';
  char end_arg_char   = ')';
  if (requireChar(begin_arg_char))
  {
    i32 cap = 16;  // todo grow
    // :arrow-copy-done-later
    allocateArray(arena, cap, param_names, true);
    allocateArray(arena, cap, param_flags, true);
    allocateArray(arena, cap, param_types, true);

    i32 typeless_run = 0;
    Token typeless_token;
    for (b32 stop = false;
         !stop && hasMore();
         )
    {
      if (optionalChar(end_arg_char)) stop = true;
      else
      {
        i32 param_i = param_count++;
        assert(param_i < cap);

        if (optionalDirective("unused"))
        {
          setFlag(&param_flags[param_i], ParameterFlag_Unused);
        }
        if (optionalChar('$'))
        {
          setFlag(&param_flags[param_i], ParameterFlag_Inferred);
          if (optionalChar('$'))
          {
            setFlag(&param_flags[param_i], ParameterFlag_Poly);
          }
        }

        Tokenizer tk_save = *TK;
        String param_name = {};
        Token maybe_param_name_token = nextToken();
        if (isIdentifier(&maybe_param_name_token))
        {
          Token after_name = peekToken();
          if (equal(&after_name, ':'))
          {
            eatToken();
            param_name = maybe_param_name_token.string;
            pushContext("parameter type");
            if (Ast *param_type = parseExpression())
            {
              param_types[param_i] = param_type;
              if (typeless_run)
              {
                for (i32 offset = 1; offset <= typeless_run; offset++)
                {
                  param_types[param_i - offset] = param_type;
                }
                typeless_run = 0;
              }
            }
            popContext();
          }
          else if (equal(&after_name, ','))
          {
            param_name = maybe_param_name_token.string;
            typeless_run++;
            typeless_token = maybe_param_name_token;
          }
        }

        if (param_name.chars)
        {
          param_names[param_i] = param_name;
        }
        else
        {
          *TK = tk_save;
          pushContext("anonymous parameter");
          Token anonymous_parameter_token = TK->last_token;
          if (Ast *param_type = parseExpression())
          {
            param_types[param_i] = param_type;
            if (typeless_run)
            {
              tokenError(&anonymous_parameter_token, "cannot follow a typeless parameter with an anonymous parameter");
            }
          }
          popContext();
        }

        if (hasMore())
        {
          Token delimiter = nextToken();
          if (equal(&delimiter, end_arg_char))
            stop = true;
          else if (!equal(&delimiter, ','))
            tokenError("unexpected token");
        }
      }
    }

    if (noError())
    {
      if (typeless_run)
      {
        tokenError(&typeless_token, "please provide types for all parameters");
      }
    }
  }

  if (noError())
  {
    out = newAst(arena, ArrowAst, &marking_token);
    out->param_count = param_count;
    out->param_names = param_names;
    out->param_types = param_types;
    out->param_flags = param_flags;

    if (optionalKind(Token_Arrow))
    {
      if (Ast *return_type = parseExpression())
        out->output_type = return_type;
    }
    else if (!is_struct)  // structs don't need return type
    {
      reportError("non-struct arrow types require an output type");
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

internal Ast *
parseFunctionExpression(Arena *arena)
{
  // cutnpaste from "parseGlobalFunction"
  FunctionAst *out = newAst(arena, FunctionAst, lastToken());

  ArrowAst *signature = 0;
  if (peekChar() == '{')
  {
    // inferred signature.
  }
  else
  {
    signature = parseArrowType(arena, false);
  }

  if (noError())
  {
    if (Ast *body = parseSequence())
    {
      out->body      = body;
      out->signature = signature;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

internal Ast *
parseList(Arena *arena)
{
  ListAst *out = 0;
  // :list-opening-brace-eaten
  Token *first_token = lastToken();
  i32 count = 0;
  i32 cap = 16;  // todo #grow
  Ast **items = pushArray(arena, cap, Ast*);
  char closing = ']';
  Ast *tail = 0;
  for (; noError(); )
  {
    if (optionalChar(closing))
      break;

    items[count++] = parseExpression();

    if (!optionalChar(','))
    {
      if (optionalKind(Token_DoubleDot))
      {
        tail = parseExpression();
      }
      requireChar(closing);
      break;
    }
  }
  if (noError())
  {
    out = newAst(arena, ListAst, first_token);
    out->count = count;
    out->items = items;
    out->tail  = tail;
  }
  return out;
}

internal Ast *
parseOperand()
{
  Ast *operand = 0;
  Token token = nextToken();
  Arena *arena = parse_arena;
  switch (token.kind)
  {
    case '_':
    {
      operand = newAst(arena, Hole, &token);
    } break;

    case '(':
    {
      operand = parseExpression();
      requireChar(')');
    } break;

    case '[':
    {// :list-opening-brace-eaten
      operand = parseList(arena);
    } break;

    case Token_Keyword_fn:
    {
      operand = parseFunctionExpression(arena);
    } break;

    case Token_Keyword_prove:
    {
      Ast *type = 0;
      
      if (peekChar() != '{')
      {
        type = parseExpression();
      }
      if (noError())
      {
        if (Ast *expression = parseSequence(true))
        {
          if (type)
          {
            TypedExpression *typed = newAst(arena, TypedExpression, &type->token);
            typed->type       = type;
            typed->expression = expression;
            operand = typed;
          }
          else
            operand = expression;
        }
      }
    } break;

    case Token_Alphanumeric:
    case Token_Special:
    {
      operand = newAst(arena, Identifier, &token);
    } break;

    case Token_Keyword_union:
    {
      reportError(&token, "anonymous union deprecated");
    } break;

    case Token_Keyword_ctor:
    {
      operand = parseCtorAst(arena);
    } break;

    case Token_Keyword_seek:
    {
      operand = parseSeek(arena);
    } break;

    case Token_Keyword_overload:
    {
      operand = parseOverload(arena);
    } break;

    default:
    {
      tokenError("expected start of expression");
    }
  }

  while (hasMore())
  {
    if (optionalChar('('))
    {// function call syntax, let's keep going
      Ast *op = operand;
      i32 cap = 16;  // todo #grow
      Ast **args = pushArray(arena, cap, Ast*);
      CompositeAst *new_operand = newAst(arena, CompositeAst, &op->token);
      new_operand->op        = op;
      new_operand->arg_count = 0;
      new_operand->args      = args;
      operand = new_operand;
      while (hasMore())
      {
        if (optionalChar(')'))
          break;
        else
        {
          i32 arg_i = new_operand->arg_count++;
          assert(arg_i < cap);
          if ((args[arg_i] = parseExpression()))
          {
            if (!optionalChar(','))
            {
              requireChar(')', "expected ',' or ')'");
              break;
            }
          }
        }
      }
    }
    else if (optionalChar('.'))
    {// member accessor
      AccessorAst *accessor = newAst(arena, AccessorAst, &TK->last_token);
      accessor->record      = operand;
      if (requireIdentifier("expected identifier as field name"))
      {
        accessor->field_name = *lastToken();
        operand              = accessor;
      }
    }
    else break;
  }
  NULL_WHEN_ERROR(operand);
  return operand;
}

inline b32
seesArrowExpression()
{
  b32 out = false;
  Tokenizer tk_save = *TK;
  if (equal(nextToken(), '('))
  {
    if (eatUntilMatchingPair())
    {
      out = (nextToken().kind == Token_Arrow);
    }
  }
  *TK = tk_save;
  return out;
}

inline i32
precedenceOf(String op)
{
  int out = 0;
  const i32 eq_precedence = 50;

  // TODO: implement for real
  if (equal(op, "->"))
  {
    out = eq_precedence - 20;
  }
  else if (equal(op, "/\\"))
  {
    out = eq_precedence - 10;
  }
  else if (equal(op, "=") || equal(op, "!="))
  {
    out = eq_precedence;
  }
  else if (equal(op, "<") || equal(op, ">") || equal(op, "=?") || equal(op, "=="))
  {
    out = eq_precedence + 5;
  }
  else if (equal(op, "+") || equal(op, "-"))
  {
    out = eq_precedence + 10;
  }
  else if (equal(op, "|"))
  {
    out = eq_precedence + 15;
  }
  else if (equal(op, "&") || equal(op, "*"))
  {
    out = eq_precedence + 20;
  }
  else
  {
    out = eq_precedence + 2;
  }

  return out;
}

internal Ast *
parseExpression_(ParseExpressionOptions opt)
{
  Arena *arena = parse_arena;
  Ast *out = 0;
  if (seesArrowExpression())
  {
    // todo Arrow could just be an operand maybe?
    out = parseArrowType(arena, false);
  }
  else if (Ast *operand = parseOperand())
  {
    // (a+b) * c
    //     ^
    for (b32 stop = false; !stop && hasMore();)
    {
      Token op_token = peekToken();
      if (isIdentifier(&op_token))
      {// infix operator syntax
        // (a+b) * c
        //        ^
        Identifier *op = newAst(arena, Identifier, &op_token);
        i32 precedence = precedenceOf(op_token.string);
        if (precedence >= opt.min_precedence)
        {
          // recurse
          nextToken();
          // a + b * c
          //      ^
          ParseExpressionOptions opt1 = opt;
          opt1.min_precedence = precedence;
          if (Ast *recurse = parseExpression_(opt1))
          {
            i32 arg_count = 2;
            Ast **args    = pushArray(arena, arg_count, Ast*);
            args[0] = operand;
            args[1] = recurse;

            CompositeAst *new_operand = newAst(arena, CompositeAst, &op_token);
            new_operand->op        = op;
            new_operand->arg_count = arg_count;
            new_operand->args      = args;
            operand = new_operand;
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
      {
        stop = true;
      }
      else
      {
        tokenError(&op_token, "expected operator token");
      }
    }
    if (noError())
      out = operand;
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare inline Ast *
parseExpression()
{
  return parseExpression_(ParseExpressionOptions{});
}

struct NormList {
  i32          count;
  Identifier **items;
};

// todo No need to normalize a fork if that fork contains other forks inside.
inline void
insertAutoNormalizations(Arena *arena, NormList norm_list, Ast *in0)
{
  switch (in0->kind)
  {
    case Ast_ForkAst:
    {
      ForkAst *in = castAst(in0, ForkAst);
      for (i32 case_id=0; case_id < in->case_count; case_id++)
      {
        Ast *body = in->bodies[case_id];
        insertAutoNormalizations(arena, norm_list, body);
        for (i32 norm_id=0; norm_id < norm_list.count; norm_id++)
        {
          Identifier *item = norm_list.items[norm_id];
          // todo cleanup: we'll need to clean useless let-normalization too!
          Let *new_body = newAst(arena, Let, &item->token);
          new_body->lhs   = item->token.string;
          new_body->rhs   = item;
          new_body->type  = newAst(arena, NormalizeMeAst, &item->token);
          new_body->body  = body;
          setFlag(&new_body->flags, AstFlag_Generated);
          body = new_body;
        }
        GoalTransform *new_body = newAst(arena, GoalTransform, &body->token);
        new_body->new_goal = newAst(arena, NormalizeMeAst, &body->token);
        setFlag(&new_body->flags, AstFlag_Generated);
        new_body->body = body;
        in->bodies[case_id] = new_body;
      }
    } break;

    case Ast_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      assert(in->body);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    case Ast_Let:
    {
      Let *in = castAst(in0, Let);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    default:
    {} break;
  }
}

inline b32
eitherOrChar(char optional, char require)
{
  b32 out = false;
  if (!optionalChar(optional))
  {
    out = requireChar(require);
  }
  return out;
}

internal FunctionAst *
parseGlobalFunction(Arena *arena, Token *name, b32 is_theorem)
{
  FunctionAst *out = newAst(arena, FunctionAst, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpression())
  {
    NormList norm_list = {};
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      while (true)
      {
        // todo #speed calling "optionalKind" repeatedly is slow
        if (optionalDirective("norm"))
        {
          pushContext("auto normalization: #norm(IDENTIFIER...)");
          if (requireChar('('))
          {
            i32 cap = 16;  // todo #grow
            norm_list.items = pushArray(temp_arena, cap, Identifier*);
            for (; noError(); )
            {
              if (optionalChar(')'))
                break;
              else if (requireIdentifier("expect auto-normalized parameter"))
              {
                // todo handle unbound identifier: all names in the norm list
                // should be in the function signature.
                Token *name = lastToken();
                i32 norm_i = norm_list.count++;
                assert(norm_i < cap);
                norm_list.items[norm_i] = newAst(arena, Identifier, name);
                if (!optionalChar(','))
                {
                  requireChar(')');
                  break;
                }
              }
            }
          }
          popContext();
        }
        else if (optionalDirective("hint"))
        {
          setFlag(&out->function_flags, FunctionFlag_is_global_hint);
        }
        else if (optionalDirective("no_apply"))
        {
          // todo: we can automatically infer this!
          setFlag(&out->function_flags, FunctionFlag_no_apply);
        }
        else if (optionalDirective("no_print_as_binop"))
        {
          setFlag(&out->function_flags, FunctionFlag_no_print_as_binop);
        }
        else if (optionalDirective("expand"))
        {
          setFlag(&out->function_flags, FunctionFlag_expand);
        }
        else if (optionalDirective("builtin"))
        {
          setFlag(&out->flags, AstFlag_is_builtin);
        }
        else if (optionalDirective("tag"))
        {
          if (requireChar('('))
          {
            i32 todo_cap = 8;
            allocateArray(arena, todo_cap, out->tags);
            for (; hasMore();)
            {
              if (requireIdentifier())
              {
                out->tags[out->tag_count++] = lastToken()->string;
                assert(out->tag_count <= todo_cap);
              }
              if (eitherOrChar(',', ')')) break;
            }
          }
        }
        else
          break;
      }

      if (Ast *body = parseSequence())
      {
        if (is_theorem)
        {
          insertAutoNormalizations(arena, norm_list, body);
        }
        out->body      = body;
        out->signature = signature;
      }
    }
    else
      reportError(signature0, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare internal Ast *
parseFork()
{
  ForkAst *out = 0;
  Arena *arena = parse_arena;
  Token token = TK->last_token;
  Ast *subject = parseExpression();
  if (requireChar('{', "to open the typedef body"))
  {
    i32 cap = 16;  // todo #grow
    Token *ctors = pushArray(arena, cap, Token);
    Ast **bodies = pushArray(arena, cap, Ast*);

    i32 actual_case_count = 0;
    for (b32 stop = false;
         !stop && hasMore();)
    {
      if (optionalChar('}'))
        stop = true;
      else
      {
        pushContext("fork case: CASE: BODY");
        i32 input_case_i = actual_case_count++;
        assert(input_case_i < cap)
        Token ctor = nextToken();
        if (isIdentifier(&ctor))
        {
          ctors[input_case_i] = ctor;
        }
        else
        {
          tokenError(&ctor, "expected a constructor name");
        }

        optionalChar(':');  // just decoration
        if (Ast *body = parseSequence(false))
        {
          bodies[input_case_i] = body;
          if (!optionalChar(','))
          {
            requireChar('}', "to end fork expression; or use ',' to end the fork case");
            stop = true;
          }
        }
        popContext();
      }
    }

    if (noError())
    {
      out = newAst(arena, ForkAst, &token);
      out->token    = token;
      out->subject    = subject;
      out->case_count = actual_case_count;
      out->bodies     = bodies;
      out->ctors      = ctors;
    }
  }

  return out;
}

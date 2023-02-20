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
    if (!message) message = "token was of a different kind than expected";
    if (nextToken().kind == tc) out = true;
    else tokenError(message);
  }
  return out;
}

inline String
requireIdentifier(char *message=0)
{
  String out = {};
  if (hasMore())
  {
    if (!message) message = "expected identifier";
    Token token = nextToken();
    if (isIdentifier(&token)) out = token.string;
    else                      tokenError(message);
  }
  return out;
}

inline Identifier *
parseIdentifier()
{
  Identifier *out = 0;
  if (requireIdentifier())
  {
    out = newAst(temp_arena, Identifier, lastToken());
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
      eatToken();
    }
  }
  return out;
}

inline void
eatCharRepeatedly(char c)
{
  while (hasMore())
  {
    if (!optionalChar(c)) break;
  }
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
  if (AlgebraNormAst *item = castAst(item0, AlgebraNormAst))
  {
    return &item->body;
  }
  invalidCodePath;
  return 0;
}

inline ArrowAst *
parseNameOnlyArrowType()
{
  Arena *arena = temp_arena;
  ArrowAst *out = newAst(arena, ArrowAst, lastToken());
  i32 cap = 16;  // todo #grow
  allocateArray(arena, cap, out->param_names);
  for (;;)
  {
    i32 param_i = out->param_count++;
    assert(param_i < cap);
    out->param_names[param_i] = requireIdentifier();
    if (!optionalChar(',')) break;
  }
  NULL_WHEN_ERROR(out);
  return out;
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
    eatCharRepeatedly(';');
    Token  token_ = nextToken();
    Token *token  = &token_;
    Ast *ast0 = 0;
    String tactic = token->string;
    if (equal(tactic, "norm") || equal(tactic, "unfold"))
    {
      pushContext("{norm|unfold[(FUNCTION_NAME)]} [as IDENTIFIER] [EXPRESSION]");
      NormOptions norm_options = {};
      String norm_name = {};

      if (equal(tactic, "unfold"))
      {
        if (optionalChar('('))
        {
          if (String name = requireIdentifier("expected function name"))
          {
            norm_options.unfold_name = name;
            requireChar(')');
          }
        }
        else
          norm_options.unfold_topmost_operator = true;
      }

      if (optionalString("as"))
      {
        if (requireIdentifier())
        {
          norm_name = lastToken()->string;
        }
      }

      if (noError())
      {
        NormalizeMeAst *ast_goal = newAst(arena, NormalizeMeAst, token);
        ast_goal->norm_options = norm_options;
        if (seesExpressionEndMarker())
        {// normalize goal
          if (norm_name)
          {
            reportError("you can't name the normalization of the goal");
          }
          else
          {
            GoalTransform *ast = newAst(arena, GoalTransform, token);
            ast->new_goal = ast_goal;
            ast0 = ast;
          }
        }
        else if (Ast *expression = parseExpression())
        {// normalize with let.
          Let *let = newAst(arena, Let, token);
          let->rhs  = expression;
          let->type = ast_goal;
          let->lhs  = norm_name;
          ast0 = let;
        }
      }

      popContext();
    }
    else if (equal(tactic, "?"))
    {
      ast0 = newAst(arena, QuestionMark, token);
      expect_sequence_to_end = true;
    }
    else if (equal(tactic, "rewrite"))
    {
      // todo maybe "with" should be "using", since we take "rewrite a with b"
      // to mean "replace a by b"
      pushContext("rewrite EXPRESSION [in EXPRESSION]");
      RewriteAst *rewrite = newAst(arena, RewriteAst, token);
      if (optionalString("<-"))
      {
        rewrite->right_to_left = true;
      }

      if (Ast *expression = parseExpression())
      {
        rewrite->eq_or_proof = expression;
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
      pushContext("prove [PROPOSITION] {SEQUENCE} as IDENTIFIER");

      Ast *proposition = 0;
      if (peekChar() != '{')
      {
        proposition = parseExpression();
      }

      if (noError())
      {
        if (Ast *proof = parseSequence(true))
        {
          String name = {};
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
    else if (equal(tactic, "fn"))
    {
      if (ArrowAst *signature = parseNameOnlyArrowType())
      {
        // TODO: tbh this is kinda crazy
        FunctionAst *ast = newAst(arena, FunctionAst, token);
        ast->signature = signature;
        ast->body      = parseSequence(false);
        ast0 = ast;
      }
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
      ast0 = parseUse();
      expect_sequence_to_end = true;
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
    else if (equal(tactic, "algebra_norm"))
    {
      AlgebraNormAst *ast = newAst(arena, AlgebraNormAst, token);
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
      ast0 = newAst(arena, Hole, token);
      *TK  = tk_save;
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
      eatCharRepeatedly(';');
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

forward_declare internal Ast *
parseUse()
{
  Token *token = lastToken();
  Ast *ast0 = 0;
  Arena *arena = temp_arena;
  pushContext("use IDENTIFIER|(EXPRESSION) [with PARAMETER=VALUE, ...]");
  Ast *op = 0;
  if (optionalChar('('))
  {
    op = parseExpression();
    requireChar(')');
  }
  else if (requireIdentifier())
  {
    Token op_name = *lastToken();
    op = newAst(arena, Identifier, &op_name);
  }

  if (noError())
  {
    CompositeAst *ast = newAst(arena, CompositeAst, token);
    ast->op           = op;
    ast->partial_args = true;

    b32 quick_syntax = optionalString("with");
    b32 brace_syntax = false;
    if (!quick_syntax) brace_syntax = optionalChar('{');

    if (quick_syntax || brace_syntax)
    {
      i32 cap = 16;  // todo #grow
      ast->keywords = pushArray(arena, cap, String);
      ast->args     = pushArray(arena, cap, Ast *);
      for (; hasMore();)
      {
        if (optionalIdentifier())
        {
          i32 arg_i = ast->arg_count++;
          assert(arg_i < cap);
          ast->keywords[arg_i] = lastToken()->string;
          if (quick_syntax)
          {
            if (requireChar('='))
            {
              ast->args[arg_i] = parseExpression();
              if (!optionalChar(',')) break;
            }
          }
          else
          {
            ast->args[arg_i] = parseSequence(false);
            if (!optionalChar(',')) break;
          }
        }
        else
          break;
      }

      if (hasMore())
      {
        if (optionalDirective("reduce"))
        {
          b32 require_brace = quick_syntax;
          ast->reduce_proof = parseSequence(require_brace);
        }
      }
    }

    if (brace_syntax) requireChar('}');

    ast0 = ast;
  }
  popContext();
  return ast0;
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
parseArrowType(b32 skip_output_type)
{
  Arena *arena = temp_arena;
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

        for (;;)
        {
          if (optionalChar('$'))
          {
            setFlag(&param_flags[param_i], ParameterFlag_Inferred);
          }
          else if (optionalChar('^'))
          {
            setFlag(&param_flags[param_i], ParameterFlag_Poly);
          }
          else break;
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
          if (maybe_param_name_token.kind != ':')
          {
            *TK = tk_save;
          }
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
    else if (!skip_output_type)  // structs don't need return type
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
  else if (peekChar() == '(')
  {
    signature = parseArrowType(false);
  }
  else
  {
    signature = parseNameOnlyArrowType();
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

inline Ast *
newSyntheticAst(Term *term, Token *token)
{
  SyntheticAst *out = newAst(temp_arena, SyntheticAst, token);
  out->term = term;
  return out;
}

internal Ast *
parseExists()
{
  Arena *arena = temp_arena;
  Token token_ = *lastToken(); auto token = &token_;
  pushContext("exists IDENTIFIER: TYPE, BODY");
  CompositeAst *out = 0;

  // TODO: we're only covering the "shorthand" case with a single bound variable.
  ArrowAst *signature = 0;
  if (peekChar() == '(')
  {
    signature = parseArrowType(true);
    optionalChar(',');  // for refactor purpose
  }
  else
  {
    if (requireIdentifier())
    {
      String param_name = lastToken()->string;
      if (requireChar(':'))
      {
        if (Ast *param_type = parseExpression())
        {
          if (requireChar(','))
          {
            signature = newAst(arena, ArrowAst, &param_type->token);
            signature->param_count = 1;
            pushItems(arena, signature->param_names, param_name);
            pushItems(arena, signature->param_types, param_type);
            pushItems(arena, signature->param_flags, ((u32)0));
          }
        }
      }
    }
  }

  if (signature)
  {
    signature->output_type = newSyntheticAst(rea.Type, &signature->token);
    if (Ast *body = parseExpression())
    {
      FunctionAst *fun = newAst(arena, FunctionAst, &body->token);
      fun->signature = signature;
      fun->body      = body;

      out = newAst(arena, CompositeAst, token);
      out->op        = newSyntheticAst(rea.Exists, token);
      out->arg_count = 1;
      pushItems(arena, out->args, (Ast*)fun);
    }
  }

  popContext();
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
      Ast *proposition = 0;
      if (peekChar() != '{')
      {
        proposition = parseExpression();
      }

      if (noError())
      {
        if (Ast *expression = parseSequence(true))
        {
          if (proposition)
          {
            TypedExpression *typed = newAst(arena, TypedExpression, &proposition->token);
            typed->type       = proposition;
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

    case Token_Keyword_use:
    {
      operand = parseUse();
    } break;

    case Token_Keyword_exists:
    {
      operand = parseExists();
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
  int out = 0;  // NOTE: 0 means it's literally not a binop
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
  else if (equal(op, "\\/"))
  {
    out = eq_precedence - 10;
  }
  else if (equal(op, "=") || equal(op, "!="))
  {
    out = eq_precedence;
  }
  else if (equal(op, "<") || equal(op, ">") ||
           equal(op, "<?") || equal(op, ">?") ||
           equal(op, "<=") || equal(op, ">=") ||
           equal(op, "<=?") || equal(op, ">=?") ||
           equal(op, "=?") || equal(op, "=="))
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
  else if (equal(op, "&") || equal(op, "*") || equal(op, "/"))
  {
    out = eq_precedence + 20;
  }
  else if (equal(op, "cons"))
  {
    // NOTE: temporary precedence, until the day we figure a better convention.
    out = eq_precedence + 2;
  }

  return out;
}

internal b32
seesCast()
{
  b32 out = false;
  Tokenizer tk_save = *TK;
  if (peekChar() == '(')
  {
    eatToken();
    if (peekChar() == ':')
    {
      out = true;
    }
  }
  *TK = tk_save;
  return out;
}

internal TypedExpression *
parseCast()
{
  TypedExpression *out = 0;

  Token token = *lastToken();
  requireChar('(');
  requireChar(':');
  assert(noError());

  if (Ast *type = parseExpression())
  {
    if (requireChar(')'))
    {
      if (Ast *expression = parseExpression())
      {
        out = newAst(temp_arena, TypedExpression, &token);
        out->type       = type;
        out->expression = expression;
      }
    }
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
    // NOTE: Doing it like this means that all operators bind stronger than "->".
    out = parseArrowType(false);
  }
  else if (seesCast())
  {
    out = parseCast();
  }
  else if (Ast *operand = parseOperand())
  {
    // (a+b) * c
    //     ^
    for (b32 stop = false; !stop && hasMore();)
    {
      Token op_token_ = peekToken(); auto op_token = &op_token_;
      if (isIdentifier(op_token) || op_token->kind == Token_Arrow)
      {// infix operator syntax
        // (a+b) * c
        //        ^
        Identifier *op = newAst(arena, Identifier, op_token);
        i32 precedence = precedenceOf(op_token->string);
        if (precedence >= opt.min_precedence)
        {
          // recurse
          eatToken();
          // a + b * c
          //      ^
          ParseExpressionOptions opt1 = opt;
          opt1.min_precedence = precedence;

          if (Ast *recurse = parseExpression_(opt1))
          {
            if (op_token->kind == Token_Arrow)
            {
              Ast *param_type = operand;
              ArrowAst *arrow = newAst(arena, ArrowAst, op_token);
              arrow->param_count = 1;
              pushItems(arena, arrow->param_types, param_type);
              pushItems(arena, arrow->param_names, String{});
              pushItems(arena, arrow->param_flags, (u32)0);
              arrow->output_type = recurse;
              operand = arrow;
            }
            else
            {
              // bookmark cleanup: use pushItems
              i32 arg_count = 2;
              Ast **args    = pushArray(arena, arg_count, Ast*);
              args[0] = operand;
              args[1] = recurse;

              CompositeAst *new_operand = newAst(arena, CompositeAst, op_token);
              new_operand->op        = op;
              new_operand->arg_count = arg_count;
              new_operand->args      = args;
              operand = new_operand;
            }
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
      else if (isExpressionEndMarker(op_token))
      {
        stop = true;
      }
      else
      {
        tokenError(op_token, "expected operator token");
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
        Ast *body = in->cases[case_id];
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
        in->cases[case_id] = new_body;
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
        // todo #speed elseif
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
        else if (optionalDirective("no_expand"))  // todo: should this be "no_expand" instead?
        {
          // todo: we can automatically infer this!
          setFlag(&out->function_flags, FunctionFlag_no_expand);
        }
        else if (optionalDirective("expand"))
        {
          setFlag(&out->function_flags, FunctionFlag_expand);
        }
        else if (optionalDirective("builtin"))
        {
          setFlag(&out->flags, AstFlag_IsBuiltin);
          if (optionalChar('('))
          {
            out->builtin_name = requireIdentifier();
            requireChar(')');
          }
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
        else if (optionalDirective("measure"))
        {
          if (requireChar('('))
          {
            if (Ast *measure_function_body = parseExpression())
            {
              if (requireChar(','))
              {
                if (Ast *well_founded_proof = parseExpression())
                {
                  FunctionAst *measure_function = newAst(arena, FunctionAst, &measure_function_body->token);
                  measure_function->signature = pushCopy(arena, signature);
                  measure_function->signature->output_type = 0;  // :no-output-type
                  measure_function->body      = measure_function_body;
                  out->measure_function   = measure_function;
                  out->well_founded_proof = well_founded_proof;
                }
              }
            }
            requireChar(')');
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
      out->cases     = bodies;
      out->ctors      = ctors;
    }
  }

  return out;
}

inline i32
getPolyParamCount(ArrowAst *params)
{
  i32 param_count = 0;
  for (i32 param_i=0; param_i < params->param_count; param_i++)
  {
    if (checkFlag(params->param_flags[param_i], ParameterFlag_Poly))
    {
      param_count++;
    }
    else
      break;
  }
  return param_count;
}

internal UnionAst *
parseUnion(Arena *arena, Token *uni_name)
{
  UnionAst *uni = newAst(arena, UnionAst, uni_name);

  i32 uni_param_count = 0;
  i32 poly_count      = 0;
  i32 non_poly_count  = 0;
  if (peekChar() == ('('))
  {
    if ((uni->signature = parseArrowType(true)))
    {
      if (uni->signature->output_type)
      {
        reportError(uni->signature->output_type, "didn't expect an output type");
      }
      else
      {
        uni->signature->output_type = newSyntheticAst(rea.Type, uni_name);
        uni_param_count = uni->signature->param_count;
        poly_count      = getPolyParamCount(uni->signature);
        non_poly_count  = uni_param_count - poly_count;
      }
    }
  }

  if (optionalDirective("builtin"))
  {
    setFlag(&uni->flags, AstFlag_IsBuiltin);
    if (optionalChar('('))
    {
      uni->builtin_name = requireIdentifier();
      requireChar(')');
    }
  }

  if (requireChar('{'))
  {
    i32 ctor_cap = 16;  // todo #grow
    allocateArray(arena, ctor_cap, uni->ctor_signatures);
    allocateArray(arena, ctor_cap, uni->ctor_names);

    Ast *auto_ctor_output_type = 0;
    if (!non_poly_count)
    {
      if (poly_count)
      {
        CompositeAst *output_type = newAst(arena, CompositeAst, uni_name);
        output_type->arg_count = uni_param_count;
        allocateArray(arena, uni_param_count, output_type->args);
        for (i32 i=0; i < uni_param_count; i++)
        {
          // we got rid of the param token, so now we gotta make one up...
          Token token = newToken(uni->signature->param_names[i]);
          output_type->args[i] = newAst(arena, Identifier, &token);
        }
        output_type->op = newAst(arena, Identifier, uni_name);
        auto_ctor_output_type = output_type;
      }
      else
      {
        auto_ctor_output_type = newAst(arena, Identifier, uni_name);
      }
    }

    for (b32 stop=false; noError() && !stop; )
    {
      if (optionalChar('}')) stop=true;
      else
      {
        i32 ctor_i = uni->ctor_count++;
        Token ctor_name = nextToken();
        uni->ctor_names[ctor_i] = ctor_name;
        if (isIdentifier(&ctor_name))
        {
          ArrowAst *sig = 0;
          if (peekChar() == '(')
          {// composite constructor
            sig = uni->ctor_signatures[ctor_i] = parseArrowType(true);
          }
          else
          {// atomic constructor
            sig = newAst(arena, ArrowAst, &ctor_name);
            uni->ctor_signatures[ctor_i] = sig;
            allocateArray(arena, poly_count, sig->param_names);
            allocateArray(arena, poly_count, sig->param_types);
            allocateArray(arena, poly_count, sig->param_flags);
          }

          if (noError())
          {
            // parameter modification to add poly parameters
            assert((sig->param_count + poly_count) < ctor_cap);
            for (i32 i = sig->param_count-1; i >= 0; i--)
            {
              sig->param_names[i+poly_count] = sig->param_names[i];
              sig->param_types[i+poly_count] = sig->param_types[i];
              sig->param_flags[i+poly_count] = sig->param_flags[i];
            }
            for (i32 i=0; i < poly_count; i++)
            {
              sig->param_names[i] = uni->signature->param_names[i];
              sig->param_types[i] = uni->signature->param_types[i];
              sig->param_flags[i] = uni->signature->param_flags[i] | ParameterFlag_Inferred;
            }
            sig->param_count += poly_count;

            // output type modification
            if (auto_ctor_output_type)
            {
              if (sig->output_type)
              {
                reportError(sig->output_type, "did not expect output type");
              }
              else
              {
                sig->output_type = auto_ctor_output_type;
              }
            }
            else if (!sig->output_type)
            {
              reportError(sig, "output type required since there are non-poly parameters");
            }
          }
        }
        else
        {
          tokenError("expected an identifier as constructor name");
        }

        stop = eitherOrChar(',', '}');
      }
    }
  }
  
  return uni;
}


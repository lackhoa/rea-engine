#include "utils.h"
#include "memory.h"
#include "engine.h"
#include "tokenization.h"

inline char
getMatchingPair(Token *opening)
{
  switch (opening->string.chars[0])
  {
    case '(':
        return ')';
    case '[':
        return ']';
    case '{':
        return '}';
    default:
        return 0;
  }
}

inline b32
equal(Token *token, const char *string)
{
    return equal(token->string, string);
}

inline b32
equal(Token *token, char c)
{
    return ((token->string.length == 1) &&
            (token->string.chars[0] == c));
}

inline b32
isAlphaNumeric(char c)
{
  return ((('a' <= c) && (c <= 'z'))
          || (('A' <= c) && (c <= 'Z'))
          || (('0' <= c) && (c <= '9'))
          || (c == '\'')
          || (c == '_'));
}

inline b32
isSpecial(char c)
{
  switch (c)
  {
    case '`':
    case '/':
    case '?':
    case '<':
    case '>':
    case '!':
    case '~':
    case '@':
    case '#':
    case '$':
    case '^':
    case '&':
    case '|':
    case '*':
    case '-':
    case '+':
    case '=':
        return true;

    default:
        return false;
  }
}

inline void
printCharToBufferRepeat(char *buffer, char c, i32 repeat)
{
    for (i32 index = 0 ;
         index < repeat;
         index++)
    {
        buffer[index] = c;
    }
    buffer[repeat] = 0;
}

global_variable Tokenizer *global_tokenizer;

inline void setErrorFlag(u32 flag, Tokenizer *tk=global_tokenizer)
{
  setFlag(&tk->error->flags, flag);
}

inline b32 checkErrorFlag(u32 flag, Tokenizer *tk=global_tokenizer)
{
  return checkFlag(tk->error->flags, flag);
}

inline void
pushContext(String string, b32 is_important, Tokenizer *tk=global_tokenizer)
{
  ParseContext *context = pushStruct(temp_arena, ParseContext);
  context->first        = string;
  context->is_important = is_important;
  context->next         = tk->context;
  tk->context = context;
}

inline void
pushContext(char *string, b32 is_important=false)
{
  pushContext(toString(string), is_important);
}

inline void
pushContext(const char *string, b32 is_important=false)
{
  pushContext(toString(string), is_important);
}

internal void
popContext(Tokenizer *tk = global_tokenizer)
{
  tk->context = tk->context->next;
}

inline b32
hasMore(Tokenizer *tk = global_tokenizer)
{
  b32 out = ((*tk->at != 0) && (!tk->error));
#if 0
  if (out && (peekToken(tk).cat == 0))
    invalidCodePath;
#endif
  return out;
}

inline void
wipeError(Tokenizer *tk = global_tokenizer)
{
  resetArena(error_buffer);
  tk->error = 0;
}

inline b32
noError(Tokenizer *tk = global_tokenizer)
{
  return !tk->error;
}

inline ParseError *
getError(Tokenizer *tk=global_tokenizer)
{
  return tk->error;
}

inline ParseError *
hasError(Tokenizer *tk=global_tokenizer)
{
  return tk->error;
}

inline char
nextChar(Tokenizer *tk=global_tokenizer)
{
  char out;
  if (*tk->at)
  {
    out = *tk->at++;
    if (out == '\n')
    {
      tk->line++;
      tk->column = 1;
    }
    else
      tk->column++;
  }
  else
    out = 0;
  return out;
}

internal void
eatAllSpaces(Tokenizer *tk)
{
  b32 stop = false;
  while ((*tk->at) && (!stop))
  {
    switch (*tk->at)
    {
      case '\n':
      case '\t':
      case ' ':
      {
        nextChar(tk);
      } break;

      case ';':
      {
        if (*(tk->at+1) == ';')
        {
          nextChar(tk);
          nextChar(tk);
          while ((*tk->at) && (*tk->at != '\n'))
            nextChar(tk);
        }
        else
        {
          stop = true;
        }
      } break;

      default:
          stop = true;
    }
  }
}

internal void
parseErrorVA(i32 line, i32 column, char *format, va_list arg_list, Tokenizer *tk = global_tokenizer)
{
  assert(!tk->error);  // note: prevent parser from doing useless work after failure.

  ParseContext *context = 0;
  for (ParseContext *it = tk->context; it; it=it->next)
  {
    // note: we reverse the context list here, which is convenient for printing.
    // TODO #speed don't do this in here! Since we sometimes recover from error.
    ParseContext *new_context = copyStruct(temp_arena, it);
    new_context->next = context;
    context = new_context;
  }

  tk->error = pushStruct(temp_arena, ParseError, true);
  tk->error->message = printVA(temp_arena, format, arg_list);
  tk->error->line    = line;
  tk->error->column  = column;
  tk->error->context = context;
}

internal void
parseError(Ast *in, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  Token *token = &in->token;
  parseErrorVA(token->line, token->column, format, arg_list);
  __crt_va_end(arg_list);
}

internal void
parseError(Tokenizer *tk, Token *token, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  parseErrorVA(token->line, token->column, format, arg_list, tk);
  __crt_va_end(arg_list);
}

// todo cleanup always use the global tokenizer, so we can get rid of this function
internal void
tokenError(Token *token, char *message, Tokenizer *tk=global_tokenizer)
{
  parseError(tk, token, "%s", message);
}

internal void
tokenError(char *message, Tokenizer *tk=global_tokenizer)
{
  tokenError(&tk->last_token, message, tk);
}

internal void
parseError(char *message, Tokenizer *tk=global_tokenizer)
{
  parseError(tk, &tk->last_token, message);
}

internal void
parseError(Token *token, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  parseErrorVA(token->line, token->column, format, arg_list);
  __crt_va_end(arg_list);
}

forward_declare inline void
eatToken(Tokenizer *tk = global_tokenizer)
{
  Token out = {};
  out.string.chars = tk->at;
  out.line         = tk->line;
  out.column       = tk->column;

  switch (char first_char = nextChar(tk))
  {
    case '#':
    {
      out.string.chars++; // advance past the hash
      out.cat = Token_Directive_START;
      while (isAlphaNumeric(*tk->at))
        nextChar(tk);
    } break;

    case '"':
    {
      out.string.chars++; // advance past the opening double quote
      out.cat = Token_StringLiteral;
      while (*tk->at != '"')
        nextChar(tk);
      // handle the closing double quote
      nextChar(tk);
      out.string.length = (i32)(tk->at - out.string.chars - 1);
    } break;

    case '.':
    {
      if ((*tk->at == '.') && (*(tk->at+1) == '.'))
      {
        nextChar(tk);
        nextChar(tk);
        out.cat = Token_Ellipsis;
      }
      else
        out.cat = (TokenCategory)'.';
    } break;

    case '=':
    {
      switch (*tk->at)
      {
        case '>':
        {
          out.cat = Token_StrongArrow;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = Token_Special;
          while (isSpecial(*tk->at))
            nextChar(tk);
        } break;
      }
    } break;

    case '-':
    {
      switch (*tk->at)
      {
        case '-':
        {
          out.cat = Token_DoubleDash;
          nextChar(tk);
        } break;

        case '>':
        {
          out.cat = Token_Arrow;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = Token_Special;
          while (isSpecial(*tk->at))
            nextChar(tk);
        } break;
      }
    } break;

    case ':':
    {
      switch (*tk->at)
      {
        case ':':
        {
          out.cat = Token_DoubleColon;
          nextChar(tk);
        } break;

        case '=':
        {
          out.cat = Token_ColonEqual;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = (TokenCategory)':';
        } break;
      }
    } break;

    default:
    {
      if (isAlphaNumeric(first_char))
      {
        out.cat = Token_Alphanumeric;
        while (isAlphaNumeric(*tk->at))
          nextChar(tk);
      }
      else if (isSpecial(first_char))
      {
        out.cat = Token_Special;
        while (isSpecial(*tk->at))
          nextChar(tk);
      }
      else
        out.cat = (TokenCategory)first_char;
    } break;
  }

  if (out.cat)
  {
    if (!out.string.length)
      out.string.length = (i32)(tk->at - out.string.chars);
    assert(out.string.length);

    switch (out.cat)
    {
      case Token_Alphanumeric:
      {
        // todo: lookup keywords with hash table
        for (int id = 1; id < arrayCount(keywords); id++)
        {
          if (equal(out.string, keywords[id]))
          {
            out.cat = (TokenCategory)((int)Token_Keyword_START + id);
            break;
          }
        }
      } break;

      case Token_Directive_START:
      {
        b32 found = false;
        for (int id = 1; id < arrayCount(metaDirectives); id++)
        {
          if (equal(out.string, metaDirectives[id]))
          {
            out.cat = (TokenCategory)((int)Token_Directive_START + id);
            found = true;
            break;
          }
        }
        if (!found)
          tokenError(&out, "unknown directive");
      } break;

      default: {};
    }
  }

  tk->last_token = out;
  // note: we eat spaces afterward, so that we can always check *tk->at to see
  // if there's anything left to parse.
  eatAllSpaces(tk);
}

forward_declare inline Token
nextToken(Tokenizer *tk=global_tokenizer)
{
  eatToken(tk);
  return tk->last_token;
}

forward_declare inline Token
peekToken(Tokenizer *tk = global_tokenizer)
{
    auto tk_copy = *tk;
    return nextToken(&tk_copy);
}

inline b32
eatUntil(char c, Tokenizer *tk)
{
  b32 found = false;
  while (*tk->at && !found)
  {
    if (*tk->at == c)
      found = true;
    nextToken(tk);
  }
  return found;
}

inline b32
inString(char *string, Token *token)
{
    if (token->string.length == 1)
    {
        char character = token->string.chars[0];
        for (char *c = string; *c; c++)
        {
            if (*c == character)
                return true;
        }
    }
    return false;
}

// TODO: Better hash function!
internal u32
stringHash(String string)
{
    u32 out = 0;
    for (int i = 0; i < string.length; i++)
    {
        out = 65599*out + string.chars[i];
    }
    return out;
}

inline b32
isIdentifier(Token *token)
{
    return ((token->cat == Token_Alphanumeric)
            || (token->cat == Token_Special));
}

inline b32
eatUntilMatchingPair(Tokenizer *tk)
{
  b32 found = false;
  Token opening = tk->last_token;
  char  closing = getMatchingPair(&opening);
  assert(closing);
  for (; !found && hasMore(tk); )
  {
    Token token = nextToken(tk);
    if (getMatchingPair(&token))
      eatUntilMatchingPair(tk);

    else if (equal(&token, closing))
      found = true;
  }

  if (noError(tk) && !found)
    parseError(tk, &opening, "could not find matching pair for");

  return found;
}

internal i32
getCommaSeparatedListLength(Tokenizer *tk)
{
  Token opening = tk->last_token;
  char closing = getMatchingPair(&opening);
  assert(closing);
  char opening_char = opening.string.chars[0];
  char previous = opening_char;
  i32 out = 0;
  for (b32 stop = false; !stop && hasMore(tk);)
  {
    Token token = nextToken(tk);
    if (getMatchingPair(&token))
    {
      eatUntilMatchingPair(tk);
    }
    else if (equal(&token, closing))
    {
      if ((previous != ',') && (previous != opening_char))
        out++;
      stop = true;
    }
    else if (equal(&token, ','))
    {
      out++;
    }
    previous = tk->last_token.string.chars[0];

  }
  return out;
}

inline i32
parseInt32()
{
  Token token = nextToken();
  i32 out = 0;
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

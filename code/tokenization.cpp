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
printCharToBufferRepeat(char *buffer, char c, s32 repeat)
{
    for (s32 index = 0 ;
         index < repeat;
         index++)
    {
        buffer[index] = c;
    }
    buffer[repeat] = 0;
}

global_variable Tokenizer *global_tokenizer;

inline void setErrorCode(ErrorCode code)
{
  global_tokenizer->error->code = code;
}

inline void addVoidAttachment(char *string, AttachmentType type, void *p)
{
  ParseError *error = global_tokenizer->error;
  assert(error->attachment_count < arrayCount(error->attachments));
  error->attachments[error->attachment_count++] = {string, type, p};
}

inline void attach(char *string, Token *token)
{
  addVoidAttachment(string, AttachmentType_Token, token);
}

inline void attach(char *string, Ast *ast)
{
  addVoidAttachment(string, AttachmentType_Ast, ast);
}

inline void attach(char *string, Value *value)
{
  addVoidAttachment(string, AttachmentType_Value, value);
}

inline void attach(char *string, Matcher *matcher)
{
  addVoidAttachment(string, AttachmentType_TypeMatcher, matcher);
}

// #define pushContext { ParseContext context = {(char*)__func__}; pushContext_(&context); }
inline void
pushContext(char *string, Tokenizer *tk=global_tokenizer)
{
  ParseContext *context = pushStruct(&tk->error_arena, ParseContext);
  context->first = string;
  context->next  = tk->context;
  tk->context    = context;
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
  tk->error_arena.used = 0;
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

// todo: #speed use hash table
inline MetaDirective
matchMetaDirective(Token *token)
{
    auto out = (MetaDirective)0;
    if (token->cat == TC_Alphanumeric)
    {
        for (int id = 1; id < arrayCount(metaDirectives); id++)
        {
            if (equal(token, metaDirectives[id]))
            {
                out = (MetaDirective)(id);
                break;
            }
        }
    }
    return out;
}

forward_declare inline Token
nextToken(Tokenizer *tk = global_tokenizer)
{
  Token out = {};
  out.string.chars = tk->at;
  out.line       = tk->line;
  out.column     = tk->column;

  switch (char first_char = nextChar(tk))
  {
    case '"':
    {
      out.string.chars++; // advance past the opening double quote
      out.cat = TC_StringLiteral;
      while (*tk->at != '"')
        nextChar(tk);
      // handle the closing double quote
      nextChar(tk);
      out.string.length = (s32)(tk->at - out.string.chars - 1);
    } break;

    case '=':
    {
      switch (*tk->at)
      {
        case '>':
        {
          out.cat = TC_StrongArrow;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = TC_Special;
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
          out.cat = TC_DoubleDash;
          nextChar(tk);
        } break;

        case '>':
        {
          out.cat = TC_Arrow;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = TC_Special;
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
          out.cat = TC_DoubleColon;
          nextChar(tk);
        } break;

        case '=':
        {
          out.cat = TC_ColonEqual;
          nextChar(tk);
        } break;

        default:
        {
          out.cat = (TokenCategory)':';
        } break;
      }
    } break;

    case '(':
    case '{':
    {
      out.cat = TC_PairingOpen;
    } break;

    case ')':
    case '}':
    {
      out.cat = TC_PairingClose;
    } break;

    default:
    {
      if (isAlphaNumeric(first_char))
      {
        out.cat = TC_Alphanumeric;
        while (isAlphaNumeric(*tk->at))
          nextChar(tk);
      }
      else if (isSpecial(first_char))
      {
        out.cat = TC_Special;
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
      out.string.length = (s32)(tk->at - out.string.chars);
    assert(out.string.length);

    if (out.cat == TC_Alphanumeric)
    {
      // todo: lookup keywords with hash table
      for (int i = 1;
           i < arrayCount(keywords);
           i++)
      {
        if (equal(out, keywords[i]))
        {
          out.cat = (TokenCategory)((int)TC_KeywordBegin_ + i);
          break;
        }
      }
    }

  }

  tk->last_token = out;
  // note: we eat spaces afterward, so that we can always check *tk->at to see
  // if there's anything left to parse.
  eatAllSpaces(tk);
  return out;
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
    return ((token->cat == TC_Alphanumeric)
            || (token->cat == TC_Special));
}

internal void
parseErrorVA(s32 line, s32 column, char *format, va_list arg_list, Tokenizer *tk = global_tokenizer)
{
  assert(!tk->error);  // note: prevent parser from doing useless work after failure.

  MemoryArena *arena = &tk->error_arena;
  tk->error = pushStruct(arena, ParseError, true);
  tk->error->message = subArena(arena, 1024);

  printVA(&tk->error->message, format, arg_list);

  tk->error->line   = line;
  tk->error->column = column;
  if (tk->context)
    tk->error->context = tk->context->first;
}

internal void
parseError(Token *token, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  parseErrorVA(token->line, token->column, format, arg_list);
  __crt_va_end(arg_list);
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

internal void
tokenError(Token *token, char *message, Tokenizer *tk = global_tokenizer)
{
  parseError(token, message, tk);
  print(&tk->error->message, ": ");
  print(&tk->error->message, token->string);
}

internal void
tokenError(char *message, Tokenizer *tk = global_tokenizer)
{
  tokenError(&tk->last_token, message);
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

internal s32
getCommaSeparatedListLength(Tokenizer *tk)
{
  Token opening = tk->last_token;
  char closing = getMatchingPair(&opening);
  assert(closing);
  char opening_char = opening.string.chars[0];
  char previous = opening_char;
  s32 out = 0;
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

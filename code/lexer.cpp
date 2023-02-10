#include "utils.h"
#include "memory.h"
#include "engine.h"
#include "lexer.h"

inline Token
newToken(String text)
{
  Token out;
  out.string = text;
  out.line   = 0;
  out.column = 0;
  out.kind    = Token_Alphanumeric;
  return out;
}

inline Token
newToken(const char *text)
{
  return newToken(toString(text));
}

inline Tokenizer
newTokenizer(char *input, String directory=toString("<dir_not_provided>"))
{
  Tokenizer out = {};
  out.line         = 1;
  out.column       = 1;
  out.directory    = directory;
  out.at           = input;
  if (input)
    eatAllSpaces(&out);
  return out;
}

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

inline void
pushContext(String string, b32 is_important, Tokenizer *tk=global_tokenizer)
{
  InterpContext *context = pushStruct(temp_arena, InterpContext);
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

InterpError SILENT_ERROR;

inline void
wipeError(Tokenizer *tk = global_tokenizer)
{
  resetArena(error_buffer);
  tk->error       = 0;
}

inline b32
noError(Tokenizer *tk = global_tokenizer)
{
  return !tk->error;
}

inline InterpError *
getError(Tokenizer *tk=global_tokenizer)
{
  return tk->error;
}

inline InterpError *
hasError(Tokenizer *tk=global_tokenizer)
{
  return tk->error;
}

inline void
silentError(Tokenizer *tk=global_tokenizer)
{
  tk->error = &SILENT_ERROR;
}

inline b32
hasSilentError(Tokenizer *tk=global_tokenizer)
{
  return tk->error == &SILENT_ERROR;
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
reportErrorVA(i32 line, i32 column, char *format, va_list arg_list, Tokenizer *tk = global_tokenizer)
{
  assert(!tk->error);  // note: prevent parser from doing useless work after failure.

  InterpContext *context = 0;
  for (InterpContext *it = tk->context; it; it=it->next)
  {
    // note: we reverse the context list here, which is convenient for printing.
    // TODO #speed don't do this in here! Since we sometimes recover from error.
    InterpContext *new_context = copyStruct(temp_arena, it);
    new_context->next = context;
    context = new_context;
  }

  tk->error = pushStruct(temp_arena, InterpError, true);
  tk->error->message = printVA(temp_arena, format, arg_list);
  tk->error->line    = line;
  tk->error->column  = column;
  tk->error->context = context;
}

internal void
reportError(Ast *in, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  Token *token = &in->token;
  reportErrorVA(token->line, token->column, format, arg_list);
  __crt_va_end(arg_list);
}

internal void
reportError(Tokenizer *tk, Token *token, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  reportErrorVA(token->line, token->column, format, arg_list, tk);
  __crt_va_end(arg_list);
}

// todo cleanup always use the global tokenizer, so we can get rid of this function
internal void
tokenError(Token *token, char *message, Tokenizer *tk=global_tokenizer)
{
  reportError(tk, token, "%s", message);
}

internal void
tokenError(char *message, Tokenizer *tk=global_tokenizer)
{
  tokenError(&tk->last_token, message, tk);
}

internal void
reportError(char *message, Tokenizer *tk=global_tokenizer)
{
  reportError(tk, &tk->last_token, message);
}

internal void
reportError(Token *token, char *format, ...)
{
  va_list arg_list;
  __crt_va_start(arg_list, format);
  reportErrorVA(token->line, token->column, format, arg_list);
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
      out.kind = Token_Directive_START;
      while (isAlphaNumeric(*tk->at))
        nextChar(tk);
    } break;

    case '"':
    {
      out.string.chars++; // advance past the opening double quote
      out.kind = Token_StringLiteral;
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
        out.kind = Token_Ellipsis;
      }
      else if (*tk->at == '.')
      {
        nextChar(tk);
        out.kind = Token_DoubleDot;
      }
      else
        out.kind = (TokenKind)'.';
    } break;

    case '=':
    {
      switch (*tk->at)
      {
        case '>':
        {
          out.kind = Token_StrongArrow;
          nextChar(tk);
        } break;

        default:
        {
          out.kind = Token_Special;
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
          out.kind = Token_DoubleDash;
          nextChar(tk);
        } break;

        case '>':
        {
          out.kind = Token_Arrow;
          nextChar(tk);
        } break;

        default:
        {
          out.kind = Token_Special;
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
          out.kind = Token_DoubleColon;
          nextChar(tk);
        } break;

        case '=':
        {
          out.kind = Token_ColonEqual;
          nextChar(tk);
        } break;

        default:
        {
          out.kind = (TokenKind)':';
        } break;
      }
    } break;

    case '_':
    {
      out.kind = Token_Alphanumeric;
      b32 advanced = false;
      while (isAlphaNumeric(*tk->at))
      {
        nextChar(tk);
        advanced = true;
      }
      if (!advanced)
        out.kind = (TokenKind)'_';  // todo: why is the underscore special?
    } break;

    default:
    {
      if (isAlphaNumeric(first_char))
      {
        out.kind = Token_Alphanumeric;
        while (isAlphaNumeric(*tk->at))
          nextChar(tk);
      }
      else if (isSpecial(first_char))
      {
        out.kind = Token_Special;
        while (isSpecial(*tk->at))
          nextChar(tk);
      }
      else
        out.kind = (TokenKind)first_char;
    } break;
  }

  if (out.kind)
  {
    if (!out.string.length)
      out.string.length = (i32)(tk->at - out.string.chars);
    assert(out.string.length);

    switch (out.kind)
    {
      case Token_Alphanumeric:
      {
        // todo: lookup keywords with hash table
        for (int id = 1; id < arrayCount(language_keywords); id++)
        {
          if (equal(out.string, language_keywords[id]))
          {
            out.kind = (TokenKind)((int)Token_Keyword_START + id);
            break;
          }
        }
      } break;

      case Token_Directive_START:
      {
        b32 found = false;
        for (int id = 1; id < arrayCount(meta_directives); id++)
        {
          if (equal(out.string, meta_directives[id]))
          {
            out.kind = (TokenKind)((int)Token_Directive_START + id);
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
  // NOTE: :always-eat-spaces We eat spaces afterward, so that we can always
  // check *tk->at to see if there's anything left to parse.
  eatAllSpaces(tk);
}

// todo just return the token pointer!
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


inline char
peekChar(Tokenizer *tk = global_tokenizer)
{
  return *tk->at;  // :always-eat-spaces
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
    return ((token->kind == Token_Alphanumeric)
            || (token->kind == Token_Special));
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
    reportError(tk, &opening, "could not find matching pair for");

  return found;
}

inline Token *
lastToken()
{
  return &global_tokenizer->last_token;
}

inline i32
toInt32(Token *token)
{
  i32 out = 0;
  String string = token->string;
  i32 length = string.length;
  for (int char_i=0;
       noError() && char_i < length;
       char_i++)
  {
    char c = string.chars[char_i];
    if ('0' <= c && c <= '9')
    {
      out = out*10 + (c - '0');
    }
    else
    {
      tokenError("expected a 32-bit integer");
    }
  }
  return out;
}

inline i32
parseInt32()
{
  eatToken();
  i32 out = toInt32(lastToken());
  return out;
}

#if 0
inline TacticEnum
matchTactic(String string)
{
  TacticEnum out = (TacticEnum)0;
  // todo: lookup with hash table
  for (int i=1; i < arrayCount(language_tactics); i++)
  {
    if (equal(string, language_tactics[i]))
    {
      out = (TacticEnum)((int)i);
      break;
    }
  }
  return out;
}
#endif

#if 0
// NOTE: I've decided it's not worth it to incur the complexity, since parsing
// is done in temp arena anyway, we can just allocate massive space on the temp arena.
internal i32
todoPeekListLengthRemoveme(Tokenizer *tk)
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
#endif

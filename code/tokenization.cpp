#include "utils.h"
#include "memory.h"

#include <stdio.h>

enum TokenCategory
{
    // 0-255 reserved for single-char ASCII types.
    TC_Special         = 256,
    TC_PairingOpen     = 257,
    TC_PairingClose    = 258,
    TC_Alphanumeric    = 259,
    TC_Arrow           = 260,
    TC_StringLiteral   = 261,
};

enum Keyword
{
    Keyword_Null_,

    Keyword_Typedef,
    Keyword_Define,
    Keyword_Switch,
    Keyword_Print,
    Keyword_PrintRaw,
    Keyword_Check,
    Keyword_Theorem,
    Keyword_Return,  // todo: this is a command, not a keyword, we don't expect it at top-level.

    Keywords_Count_,
};
const char *keywords[] = {"", "typedef", "define", "switch", "print",
                          "printRaw", "check", "theorem", "return"};

enum MetaDirective
{
    MetaDirective_Null_,

    MetaDirective_Load,

    MetaDirective_Count_,
};
const char *metaDirectives[] = {"", "load"};

struct Token
{
    String        text;
    TokenCategory cat;
    s32           line_number;
    s32           column;
};

inline b32
equals(String s, const char *cstring)
{
    if (!s.chars)
    {
        return false;
    }
    else
    {
        s32 at = 0;
        for (;
             (at < s.length);
             at++)
        {
            if ((cstring[at] == 0) || (s.chars[at] != cstring[at]))
            {
                return false;
            }
        }
        return (cstring[at] == 0);
    }
}

inline b32
equals(Token *token, const char *string)
{
    return equals(token->text, string);
}

inline b32
equals(Token *token, char c)
{
    return ((token->text.length == 1)
            &&  (token->text.chars[0] == c));
}

internal TokenCategory
getCharacterType(char c)
{
    if ((('a' <= c) && (c <= 'z'))
        || (('A' <= c) && (c <= 'Z'))
        || (('0' <= c) && (c <= '9'))
        || (c == '\'')
        || (c == '_'))
    {
        return TC_Alphanumeric;
    }
    else
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
            {
                return TC_Special;
            } break;

            case '(':
            case '{':
            {
                return TC_PairingOpen;
            } break;

            case ')':
            case '}':
            {
                return TC_PairingClose;
            }
        
            default:
                // NOTE: Self-describing category
                return (TokenCategory)c;
        }
    }
}

inline void
printToBufferVA(MemoryArena *buffer, char *format, va_list arg_list)
{
    char *at = (char *)(buffer->base + buffer->used);
    auto printed = vsprintf_s(at, (buffer->cap - buffer->used), format, arg_list);
    buffer->used += printed;
}

inline char *
myprint(MemoryArena *buffer, char *format, ...)
{
    char *out = 0;;

    va_list arg_list;
    __crt_va_start(arg_list, format);

    if (buffer)
    {
        out = (char *)buffer->base + buffer->used;
        char *at = out;
        auto printed = vsprintf_s(at, (buffer->cap-1 - buffer->used), format, arg_list);
        buffer->used += printed;
        buffer->base[buffer->used] = 0; // nil-termination
    }
    else
        vprintf_s(format, arg_list);

    __crt_va_end(arg_list);

    return out;
}

inline char *
myprint(MemoryArena *buffer, String s)
{
    char *out = 0;
    if (buffer)
    {
        out = (char *)getArenaNext(buffer);
        char *at = out;
        const char *c = s.chars;
        for (s32 index = 0; index < s.length; index++)
            *at++ = *c++;
        *at = 0;
        buffer->used = at - (char *)buffer->base;
        assert(buffer->used <= buffer->cap);
    }
    else
        printf("%.*s", s.length, s.chars);

    return out;
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

struct Expression;
struct ErrorAttachment { char *string; Expression *expression;};

struct ParseErrorData
{
    MemoryArena  message;
    Token        token;
    char        *context;

    s32             attached_count;
    ErrorAttachment attached[8];
};
typedef ParseErrorData* ParseError;

struct ParseContext { char *first; ParseContext *next; };

struct Tokenizer
{
    ParseError    error;
    MemoryArena  *error_arena;
    ParseContext *context;

    char  *at;
    Token  last_token;
    s32    line_number;
    s32    column;

    String     directory;
};

global_variable Tokenizer *global_tokenizer;

inline void
pushAttachment(Tokenizer *tk, char *string, Expression *exp)
{
    assert(tk->error->attached_count < arrayCount(tk->error->attached));
    tk->error->attached[tk->error->attached_count++] = {string, exp};
}

inline void
pushAttachment(char *string, Expression *exp)
{
    pushAttachment(global_tokenizer, string, exp);
}

internal void
pushContext_(ParseContext *context, Tokenizer *tk = global_tokenizer)
{
    ParseContext *old_first = tk->context;
    tk->context = context;
    context->next = old_first;
}

#define pushContext { ParseContext context = {(char*)__func__}; pushContext_(&context); }
#define pushContextName(string) { ParseContext context = {string}; pushContext_(&context); }

internal void
popContext(Tokenizer *tk = global_tokenizer)
{
    tk->context = tk->context->next;
}

inline b32
parsing(Tokenizer *tk = global_tokenizer)
{
    return ((*tk->at != 0) && (!tk->error));
}

inline void
nextChar(Tokenizer *tk)
{
    char previous = *tk->at++;
    if (previous == '\n')
    {
        tk->line_number++;
        tk->column = 1;
    }
    else
        tk->column++;
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

inline b32
eatUntil(char c, Tokenizer *tk)
{
    b32 found = false;
    while ((*tk->at) && (!found))
    {
        if (*tk->at++ == c)
            found = true;
    }
    return found;
}

// todo: #speed make this a hash table
inline Keyword
matchKeyword(Token *token)
{
    auto out = (Keyword)0;
    if (token->cat == TC_Alphanumeric)
    {
        for (int i = 1;
             i < arrayCount(keywords);
             i++)
        {
            if (equals(token, keywords[i]))
            {
                out = (Keyword)(i);
                break;
            }
        }
    }
    return out;
}

// todo: #speed hash table
inline MetaDirective
matchMetaDirective(Token *token)
{
    auto out = (MetaDirective)0;
    if (token->cat == TC_Alphanumeric)
    {
        for (int i = 1;
             i < arrayCount(metaDirectives);
             i++)
        {
            if (equals(token, metaDirectives[i]))
            {
                out = (MetaDirective)(i);
                break;
            }
        }
    }
    return out;
}

inline Token
nextToken(Tokenizer *tk = global_tokenizer)
{
    Token out = {};
    eatAllSpaces(tk);
    out.text.chars  = tk->at;
    out.line_number = tk->line_number;
    out.column      = tk->column;

    TokenCategory first_cat = getCharacterType(*tk->at);
    out.cat = first_cat;

    nextChar(tk);
    switch (first_cat)
    {
        case '"':
        {
            out.text.chars++;
            out.cat = TC_StringLiteral;
            while (getCharacterType(*tk->at) != '"')
                nextChar(tk);
            nextChar(tk);
        } break;

        case TC_Alphanumeric:
        case TC_Special:
        {
            while (getCharacterType(*tk->at) == first_cat)
                nextChar(tk);
        } break;

        default: {}
    }

    out.text.length = (s32)(tk->at - out.text.chars);
    assert(out.text.length);
    if (out.cat == TC_StringLiteral)
    {
        out.text.length -= 1; // minus the last '"'
    }

    if (equals(out.text, "->"))
        out.cat = TC_Arrow;

    tk->last_token = out;
    return out;
}

inline Token
peekNext(Tokenizer *tk = global_tokenizer)
{
    auto tk_copy = *tk;
    return nextToken(&tk_copy);
}

inline b32
inString(char *string, Token *token)
{
    if (token->text.length == 1)
    {
        char character = token->text.chars[0];
        for (char *c = string; *c; c++)
        {
            if (*c == character)
                return true;
        }
    }
    return false;
}

internal void
debugPrintTokens(Tokenizer tk)
{
    while (*tk.at)
    {
        Token token = nextToken(&tk);
        printf("%.*s ", token.text.length, token.text.chars);
    }
    printf("\n");
}

inline b32
equals(String a, String b)
{
    b32 out = true;
    if (a.length != b.length)
        out = false;
    else
    {
        for (int i = 0; i < a.length; i++)
        {
            if (a.chars[i] != b.chars[i])
            {
                out = false;
                break;
            }
        }
    }
    return out;
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

inline String
toString(char *c)
{
    String out;
    out.chars = c;
    out.length = 0;
    while (*c)
    {
        out.length++;
        c++;
    }
    return out;
}

inline b32
equals(char *s1, char *s2)
{
    b32 out = true;
    char *c1 = s1;
    char *c2 = s2;
    b32 stop = false;
    while (!stop)
    {
        if (*c1 != *c2)
        {
            out = false;
            stop = true;
        }
        else
        {
            if (*c1 == 0)
                stop = true;
            else
            {
                c1++;
                c2++;
            }
        }
    }
    return out;
}

inline char
getMatchingPair(char opening)
{
    switch (opening)
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

#include "utils.h"

#include <stdio.h>

struct String
{
    char *chars;
    s32  length;
};

enum TokenCategory
{
    // 0-255 reserved for single-char ASCII types.
    TC_Special         = 256,
    TC_PairingOpen     = 257,
    TC_PairingClose    = 258,
    TC_Alphanumeric    = 259,

    // TODO: Do I really need these? The tokenizer doesn't really produce this
    // information during its tokenization process.
    TC_KeywordsBegin_  = 300,
    TC_KeywordTypedef  = 301,
    TC_KeywordDefine   = 302,
    TC_KeywordSwitch   = 303,
    TC_KeywordPrint    = 304,
    TC_KeywordsEnd_    = 400,
};

const char *keywords[] = {"_ignore_", "typedef", "define", "switch", "print"};

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
        || (('0' <= c) && (c <= '9')))
    {
        return TC_Alphanumeric;
    }
    else
    {
        switch (c)
        {
            case '.':
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

// TODO: buffer overflow check
inline s32
printStringToBuffer(char *buffer, String s)
{
    char *c = s.chars;
    for (s32 index = 0 ;
         index < s.length;
         index++)
    {
        buffer[index] = *c;
        c++;
    }
    buffer[s.length] = 0;

    return s.length;
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

struct Tokenizer
{
    char *at;
    s32   line_number;
    s32   column;
};

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
            } break;

            default:
                stop = true;
        }
    }
}

inline TokenCategory
matchKeyword(Token *token)
{
    TokenCategory out = (TokenCategory)0;
    for (int i = 1;
         i < arrayCount(keywords);
         i++)
    {
        if (equals(token, keywords[i]))
        {
            out = (TokenCategory)(TC_KeywordsBegin_ + i);
            break;
        }
    }
    return out;
}

inline b32
isKeyword(Token *token)
{
    return ((token->cat > TC_KeywordsBegin_)
            && (token->cat < TC_KeywordsEnd_));
}

inline Token
advance(Tokenizer *tk)
{
    Token out = {};
    eatAllSpaces(tk);
    out.text.chars  = tk->at;
    out.line_number = tk->line_number;
    out.column      = tk->column;
    b32 stop = false;

    TokenCategory category = getCharacterType(*tk->at);
    nextChar(tk);
    out.cat = category;
    switch (category)
    {
        case TC_Alphanumeric:
        {
            while (getCharacterType(*tk->at) == category)
                nextChar(tk);
        } break;

        case TC_Special:
        {
            while (getCharacterType(*tk->at) == category)
                nextChar(tk);
        } break;

        default: {}
    }

    out.text.length = tk->at - out.text.chars;
    if (out.cat == TC_Alphanumeric)
    {
        if (TokenCategory new_type = matchKeyword(&out))
            out.cat = new_type;
    }
    return out;
}

inline Token
peekNext(Tokenizer *tk)
{
    auto tk_copy = *tk;
    return advance(&tk_copy);
}

inline void
requireChar(Tokenizer *tk, char c)
{
    Token token = advance(tk);
    if (!((token.text.length == 1) && (token.text.chars[0] == c)))
        todoErrorReport;
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

inline void
requireChar(Tokenizer *tk, char *string)
{
    Token token = advance(tk);
    if (!inString(string, &token))
        todoErrorReport;
}

internal void
debugPrintTokens(Tokenizer tk)
{
    while (*tk.at)
    {
        Token token = advance(&tk);
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

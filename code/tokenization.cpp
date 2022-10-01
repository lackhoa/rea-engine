#include "utils.h"

#include <stdio.h>

struct String
{
    char *chars;
    s32  length;
};

enum TokenCat
{
    // 0-255 reserved for single-char ASCII types.
    TokenCat_Special         = 256,
    TokenCat_PairingOpen     = 257,
    TokenCat_PairingClose    = 258,
    TokenCat_Alphanumeric    = 259,

    // TODO: Do I really need these? The tokenizer doesn't really produce this
    // information during its tokenization process.
    TokenCat_KeywordsBegin_  = 300,
    TokenCat_KeywordTypedef  = 301,
    TokenCat_KeywordDefine   = 302,
    TokenCat_KeywordSwitch   = 303,
    TokenCat_KeywordPrint    = 304,
    TokenCat_KeywordsEnd_    = 400,
};

const char *keywords[] = {"_ignore_", "typedef", "define", "switch", "print"};

struct Token
{
    String text;
    TokenCat cat;
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

inline Token
newToken(char *first_char, TokenCat category)
{
    Token out;
    out.text = {first_char, 0};
    out.cat = category;
    return out;
}

internal TokenCat
getCharacterType(char c)
{
    if ((('a' <= c) && (c <= 'z'))
        || (('A' <= c) && (c <= 'Z'))
        || (('0' <= c) && (c <= '9')))
    {
        return TokenCat_Alphanumeric;
    }
    else
    {
        switch (c)
        {
            case '.':
            case '`':
            case ',':
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
                return TokenCat_Special;
            } break;

            case '(':
            case '{':
            {
                return TokenCat_PairingOpen;
            } break;

            case ')':
            case '}':
            {
                return TokenCat_PairingClose;
            }
        
            default:
                // NOTE: Self-describing category
                return (TokenCat)c;
        }
    }
}

inline void
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
};

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
                tk->at++;
            } break;

            case ';':
            {
                if (*(tk->at+1) == ';')
                {
                    tk->at += 2;
                    while ((*tk->at) && (*tk->at != '\n'))
                        tk->at++;
                }
            } break;

            default:
                stop = true;
        }
    }
}

inline TokenCat
matchKeyword(Token *token)
{
    TokenCat out = (TokenCat)0;
    for (int i = 1;
         i < arrayCount(keywords);
         i++)
    {
        if (equals(token, keywords[i]))
        {
            out = (TokenCat)(TokenCat_KeywordsBegin_ + i);
            break;
        }
    }
    return out;
}

inline b32
isKeyword(Token *token)
{
    return ((token->cat > TokenCat_KeywordsBegin_)
            && (token->cat < TokenCat_KeywordsEnd_));
}

inline Token
advance(Tokenizer *tk)
{
    Token out = {};
    eatAllSpaces(tk);
    out.text.chars = tk->at;
    b32 stop = false;

    TokenCat type = getCharacterType(*tk->at++);
    out.cat = type;
    switch (type)
    {
        case TokenCat_Alphanumeric:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        case TokenCat_Special:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        default: {}
    }

    out.text.length = tk->at - out.text.chars;
    if (out.cat == TokenCat_Alphanumeric)
    {
        if (TokenCat new_type = matchKeyword(&out))
            out.cat = new_type;
    }
    return out;
}

inline void
requireChar(Tokenizer *tk, char c)
{
    Token token = advance(tk);
    if (!((token.text.length == 1) && (token.text.chars[0] == c)))
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

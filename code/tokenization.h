#pragma once

#include "memory.h"
#include "utils.h"

// todo: does enum automatically increment???
enum TokenCategory
{
    // 0-255 reserved for single-char ASCII types.
    TC_Special       = 256,
    TC_PairingOpen   = 257,
    TC_PairingClose  = 258,
    TC_Alphanumeric  = 259,
    TC_DoubleDash    = 260,
    TC_StringLiteral = 261,
    TC_DoubleColon   = 262,
    TC_ColonEqual    = 263,
    TC_Arrow         = 264,
    TC_StrongArrow   = 265,
};

enum Keyword
{
    Keyword_Null_,

    Keyword_Typedef,
    Keyword_Define,
    Keyword_Fork,
    Keyword_Rewrite,

    Keyword_Print,
    Keyword_PrintRaw,
    Keyword_PrintDebug,
    Keyword_Check,

    Keywords_Count_,
};
const char *keywords[] = {"", "typedef", "define", "fork", "rewrite",
                          "print", "print_raw", "print_debug", "check"};

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
  s32           line;
  s32           column;
  TokenCategory cat;
};

inline Token
newToken(String text, s32 line, s32 column, TokenCategory cat)
{
  Token out;
  out.text   = text;
  out.line   = line;
  out.column = column;
  out.cat    = cat;
  return out;
}

struct Expression;
struct ErrorAttachment { char *string; Expression *expression;};

struct ParseErrorData
{
    MemoryArena  message;
    s32          line;
    s32          column;
    char        *context;

    s32             attached_count;
    ErrorAttachment attached[8];
};
typedef ParseErrorData* ParseError;

struct ParseContext { char *first; ParseContext *next; };

// note: the tokenizer also doubles as our error tracker, which may sound weird
// but in reality it doesn't pose any problem, that said it could be better.
struct Tokenizer
{
    ParseError    error;
    MemoryArena  *error_arena;
    ParseContext *context;

    char  *at;
    Token  last_token;
    s32    line;
    s32    column;

    String     directory;
};

void eatAllSpaces(Tokenizer *tk);

// todo: check tokenizer size
inline Tokenizer
newTokenizer(MemoryArena *error_arena, String directory, char *input)
{
  Tokenizer out = {};
  out.line        = 1;
  out.column      = 1;
  out.directory   = directory;
  out.at          = input;
  out.error_arena = error_arena;
  eatAllSpaces(&out);
  return out;
}

inline Tokenizer
newTokenizerFromString(MemoryArena *error_arena, char *string)
{
  return newTokenizer(error_arena, toString("NONE"), string);
}

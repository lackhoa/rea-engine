#pragma once

#include "utils.h"

// todo: does enum automatically increment???
enum TokenCategory
{
  TC_Colon         = ':',
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

  TC_KeywordBegin_,
  TC_KeywordDefine,
  TC_KeywordFork,
  TC_KeywordRewrite,
  TC_KeywordNorm,
  TC_KeywordComputation,

  TC_KeywordPrint,
  TC_KeywordPrintRaw,
  TC_KeywordPrintDebug,
  TC_KeywordCheck,
  TC_KeywordBreakhere,
  TC_KeywordEnd_,
};

const char *keywords[] = {"", "define", "fork", "rewrite", "norm", "computation",
                          "print", "print_raw", "print_debug", "check", "breakhere"};

enum MetaDirective
{
    MetaDirective_Null_,

    MetaDirective_load,
    MetaDirective_should_fail,

    MetaDirective_Count_,
};
const char *metaDirectives[] = {"", "load", "should_fail"};

struct Token
{
  String        text;
  s32           line;
  s32           column;
  TokenCategory cat;
  operator String() { return text; }
};

inline Token
newToken(String text)
{
  Token out;
  out.text   = text;
  out.line   = 0;
  out.column = 0;
  out.cat    = TC_Alphanumeric;
  return out;
}

inline Token
newToken(const char *text)
{
  return newToken(toString(text));
}

enum AttachmentType
{
  AttachmentType_Ast,
  AttachmentType_Value,
  AttachmentType_Token,
  AttachmentType_TypeMatcher,
};
struct ErrorAttachment { char *string; AttachmentType type; void *p; };

enum ErrorCode
{
  ErrorGeneral,
  ErrorWrongType,
};

struct ParseError
{
  MemoryArena  message;
  s32          line;
  s32          column;
  char        *context;
  ErrorCode    code; 

  s32             attachment_count;
  ErrorAttachment attachments[8];
};

struct ParseContext { char *first; ParseContext *next; };

// note: the tokenizer also doubles as our error tracker, which may sound weird
// but so far it doesn't pose any problem.
struct Tokenizer
{
  ParseError   *error;
  MemoryArena   error_arena;
  ParseContext *context;

  char  *at;
  Token  last_token;
  s32    line;
  s32    column;

  String directory;
};

void eatAllSpaces(Tokenizer *tk);

inline Tokenizer
newTokenizer(MemoryArena *arena, String directory, char *input)
{
  Tokenizer out = {};
  out.line        = 1;
  out.column      = 1;
  out.directory   = directory;
  out.at          = input;
  out.error_arena = subArena(arena, kiloBytes(128));
  if (input)
    eatAllSpaces(&out);
  return out;
}

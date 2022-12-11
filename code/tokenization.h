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
  TC_KeywordUnion,
  TC_KeywordStruct,
  TC_KeywordRewrite,
  TC_KeywordNorm,

  TC_KeywordTestEval,
  TC_KeywordPrint,
  TC_KeywordPrintRaw,
  TC_KeywordPrintDebug,
  TC_KeywordCheck,
  TC_KeywordCheckTruth,
  TC_KeywordBreakhere,
  TC_KeywordEnd_,
};

const char *keywords[] = {
  "", "define", "fork", "union", "struct",
  "rewrite", "norm",
  "test_eval", "print", "print_raw", "print_debug", "check", "check_truth", "breakhere"
};

enum MetaDirective {
    MetaDirective_Null_,

    MetaDirective_load,
    MetaDirective_should_fail,

    MetaDirective_Count_,
};
const char *metaDirectives[] = {"", "load", "should_fail"};

struct Token
{
  String        string;
  s32           line;
  s32           column;
  TokenCategory cat;
  operator String() { return string; }
};

inline Token
newToken(String text)
{
  Token out;
  out.string   = text;
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

#if 0
enum AttachmentType
{
  AttachmentType_Ast,
  AttachmentType_Value,
  AttachmentType_Token,
  AttachmentType_TypeMatcher,
};
#endif

struct ErrorAttachment { char *key; char *value; };

enum ErrorCode
{
  ErrorGeneral,
  ErrorWrongType,
  ErrorAmbiguousName,
};

struct ParseError
{
  String     message;
  s32        line;
  s32        column;
  char      *context;
  ErrorCode  code; 

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
newTokenizer(String directory, char *input)
{
  Tokenizer out = {};
  out.line        = 1;
  out.column      = 1;
  out.directory   = directory;
  out.at          = input;
  if (input)
    eatAllSpaces(&out);
  return out;
}

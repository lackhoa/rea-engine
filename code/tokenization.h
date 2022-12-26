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

  TC_Keyword_START,
  TC_Keyword_fn,
  TC_Keyword_fork,
  TC_Keyword_union,
  TC_Keyword_ctor,
  TC_Keyword_seq,
  TC_Keyword_rewrite,
  TC_Keyword_norm,
  TC_Keyword_destruct,

  // todo these should be "commands"
  TC_Keyword_test_eval,
  TC_Keyword_print,
  TC_Keyword_print_raw,
  TC_Keyword_print_ast,
  TC_Keyword_check,
  TC_Keyword_check_truth,
  TC_Keyword_END,

  TC_Directive_START,
  TC_Directive_load,
  TC_Directive_should_fail,
  TC_Directive_debug,
  TC_Directive_norm,
  TC_Directive_END,
};

const char *keywords[] = {
  "", "fn", "fork", "union", "ctor", "seq",
  "rewrite", "norm", "destruct",
  "test_eval", "print", "print_raw", "print_ast", "check", "check_truth"
};

const char *metaDirectives[] = {"", "load", "should_fail", "debug", "norm"};

struct Token
{
  String        string;
  i32           line;
  i32           column;
  TokenCategory cat;
};

inline Token
newToken(String text)
{
  Token out;
  out.string = text;
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

struct ErrorAttachment { char *key; char *value; };

// 1 << 0 is unused
u32 ErrorTypecheck     = 1 << 1;
u32 ErrorUnrecoverable = 1 << 2;
u32 ErrorAmbiguousName = 1 << 3;
u32 ErrorGoalAttached  = 1 << 4;

struct ParseError
{
  String     message;
  i32        line;
  i32        column;
  char      *context;
  u32        flags; 

  i32             attachment_count;
  ErrorAttachment attachments[16];
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
  i32    line;
  i32    column;

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

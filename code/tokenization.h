#pragma once

#include "utils.h"

// todo: does enum automatically increment???
enum TokenCategory
{
  Token_Colon         = ':',
  // 0-255 reserved for single-char ASCII types.
  Token_Special       = 256,
  Token_Ellipsis      = 257,
  // Token_PairingClose  = 258,
  Token_Alphanumeric  = 259,
  Token_DoubleDash    = 260,
  Token_StringLiteral = 261,
  Token_DoubleColon   = 262,
  Token_ColonEqual    = 263,
  Token_Arrow         = 264,
  Token_StrongArrow   = 265,

  Token_Keyword_START,
  Token_Keyword_fn,
  Token_Keyword_fork,
  Token_Keyword_union,
  Token_Keyword_ctor,
  Token_Keyword_seq,

  Token_Keyword_rewrite,
  Token_Keyword_norm,
  Token_Keyword_destruct,
  Token_Keyword_prove,
  Token_Keyword_seek,
  Token_Keyword_auto,

  Token_Keyword_test_eval,
  Token_Keyword_print,
  Token_Keyword_print_raw,
  Token_Keyword_print_ast,
  Token_Keyword_check,
  Token_Keyword_check_truth,
  Token_Keyword_END,

  Token_Directive_START,
  Token_Directive_load,
  Token_Directive_should_fail,
  Token_Directive_debug,
  Token_Directive_norm,
  Token_Directive_hidden,
  Token_Directive_hint,
  Token_Directive_END,
};

const char *keywords[] = {
  "", "fn", "fork", "union", "ctor", "seq",
  "rewrite", "norm", "destruct", "prove", "seek", "auto",
  "test_eval", "print", "print_raw", "print_ast", "check", "check_truth"
};
const char *metaDirectives[] = {"", "load", "should_fail", "debug", "norm", "hidden", "hint"};

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
  out.cat    = Token_Alphanumeric;
  return out;
}

inline Token
newToken(const char *text)
{
  return newToken(toString(text));
}

struct ErrorAttachment { char *key; String value; };

// 1 << 0 is unused
u32 ErrorTypecheck     = 1 << 1;
u32 ErrorUnrecoverable = 1 << 2;
u32 ErrorAmbiguousName = 1 << 3;
u32 ErrorGoalAttached  = 1 << 4;

struct ParseContext { String first; ParseContext *next; };

struct ParseError
{
  String        message;
  i32           line;
  i32           column;
  ParseContext *context;
  u32           flags; 

  i32             attachment_count;
  ErrorAttachment attachments[16];
};

// note: the tokenizer also doubles as our error tracker, which may sound weird
// but so far it doesn't pose any problem.
struct Tokenizer
{
  ParseError   *error;
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
  out.line         = 1;
  out.column       = 1;
  out.directory    = directory;
  out.at           = input;
  if (input)
    eatAllSpaces(&out);
  return out;
}

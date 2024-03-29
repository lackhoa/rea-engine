#pragma once

#include "utils.h"

enum TokenKind
{
  Token_Colon   = ':',
  // 0-255 reserved for single-char ASCII types.

  Token_Special = 256,
  Token_DoubleDot,
  Token_Ellipsis,
  Token_Alphanumeric,
  Token_DoubleDash,
  Token_StringLiteral,
  Token_DoubleColon,
  Token_ColonEqual,
  Token_Arrow,
  Token_StrongArrow,  // NOTE: strong arrow is used for lambda, might as well use it as a tactic.

  Token_Keyword_START,
  Token_Keyword_fn,
  Token_Keyword_union,
  Token_Keyword_ctor,
  Token_Keyword_overload,
  Token_Keyword_prove,
  Token_Keyword_seek,
  Token_Keyword_in,
  Token_Keyword_use,
  Token_Keyword_exists,
  Token_Keyword_let,

  // todo #cleanup These commands can just be dispatched by the top-level parser!
  Token_Keyword_test_eval,
  Token_Keyword_print,
  Token_Keyword_print_raw,
  Token_Keyword_print_ast,
  Token_Keyword_check,
  Token_Keyword_check_truth,
  Token_Keyword_algebra_declare,
  Token_Keyword_define,
  Token_Keyword_END,

  Token_Directive,
};

const char *language_keywords[] = {
  "", "fn", "union", "ctor", "overload", "prove", "seek", "in", "use", "exists", "let",
  "test_eval", "print", "print_raw", "print_ast", "check", "check_truth", "algebra_declare", "define",
};

struct Token
{
  String    string;
  i32       line;
  i32       column;
  TokenKind kind;
  operator String() {return string;};
};

struct ErrorAttachment { char *key; String value; };

struct InterpContext { String first; InterpContext *next; b32 is_important; };

struct InterpError
{
  String         message;
  i32            line;
  i32            column;
  InterpContext *context;
  b32            goal_attached;

  i32             attachment_count;
  ErrorAttachment attachments[16];
};

// TODO: atm the tokenizer also doubles as our error tracker, which is annoying
// to think about because errors also come from the typechecker.
struct Tokenizer
{
  InterpError   *error;
  InterpContext *context;

  char  *at;
  Token  last_token;
  i32    line;
  i32    column;

  String directory;
};

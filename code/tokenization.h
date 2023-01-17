#pragma once

#include "utils.h"

enum TokenCategory
{
  Token_Colon   = ':',
  // 0-255 reserved for single-char ASCII types.

  Token_Special = 256,
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
  Token_Keyword_seq,
  Token_Keyword_overload,
  Token_Keyword_seek,

  // Token_Keyword_rewrite,
  // Token_Keyword_norm,
  // Token_Keyword_prove,
  // Token_Keyword_algebraic_manipulation,

  // todo #cleanup These commands can just be dispatched by the top-level parser!
  Token_Keyword_test_eval,
  Token_Keyword_print,
  Token_Keyword_print_raw,
  Token_Keyword_print_ast,
  Token_Keyword_check,
  Token_Keyword_check_truth,
  Token_Keyword_algebra_declare,
  Token_Keyword_END,

  // todo #cleanup We don't want token categories for these! Just dispatch when you see "#".
  Token_Directive_START,
  Token_Directive_load,
  Token_Directive_should_fail,
  Token_Directive_debug,
  Token_Directive_norm,
  Token_Directive_hidden,
  Token_Directive_hint,
  Token_Directive_no_apply,
  Token_Directive_END,
};

const char *language_keywords[] = {
  "", "fn", "union", "ctor", "seq", "overload", "seek",
  "test_eval", "print", "print_raw", "print_ast", "check", "check_truth", "algebra_declare",
};
const char *meta_directives[] = {"", "load", "should_fail", "debug", "norm", "hidden", "hint", "no_apply"};

enum TacticEnum {
  Tactic_rewrite = 1,
  Tactic_goal_transform,
  Tactic_norm,
  Tactic_return,
  Tactic_fork,
  Tactic_prove,
  Tactic_seek,

  Tactic_COUNT,
};
const char *language_tactics[] = {"", "rewrite", "=>", "norm", "return", "fork", "prove", "seek"};

struct Token
{
  String        string;
  i32           line;
  i32           column;
  TokenCategory cat;
  operator String() {return string;};
};

struct ErrorAttachment { char *key; String value; };

// 1 << 0 is unused
u32 ErrorTypecheck     = 1 << 1;
u32 ErrorUnrecoverable = 1 << 2;
u32 ErrorAmbiguousName = 1 << 3;
u32 ErrorGoalAttached  = 1 << 4;

struct ParseContext { String first; ParseContext *next; b32 is_important; };

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

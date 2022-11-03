#pragma once

#include "utils.h"
#include "engine.h"

global_variable Form *builtin_refl;
global_variable Form *builtin_identical;
global_variable Form *builtin_True;
global_variable Form *builtin_truth;
global_variable Form *builtin_False;
global_variable Form *builtin_Set;
global_variable Form *builtin_Type;

global_variable Ast dummy_hole     = {.cat = AC_DummyHole};
global_variable Ast dummy_sequence = {.cat = AC_DummySequence};
global_variable Ast dummy_rewrite  = {.cat = AC_DummyRewrite};

global_variable u64 global_next_form_id;
inline u64
getNextFormId()
{
  return global_next_form_id++;
}

#pragma once

#include "utils.h"

struct Expression;
struct Form;
struct ArrowType;

global_variable Form       *builtin_identical;
global_variable Expression *builtin_True;
global_variable Expression *builtin_truth;
global_variable Expression *builtin_False;
global_variable Form       *builtin_Set;
global_variable Form       *builtin_Type;
global_variable Expression *hole_expression;

global_variable u64 global_next_form_id;
inline u64
getNextFormId()
{
  return global_next_form_id++;
}

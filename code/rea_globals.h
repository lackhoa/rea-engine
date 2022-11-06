#pragma once

#include "utils.h"
#include "engine.h"

struct Builtins
{
  Form *refl;
  Form *identical;
  Form *True;
  Form *truth;
  Form *False;
  Form *Set;
  Form *Type;
};

global_variable Builtins builtins;

global_variable Ast dummy_hole = {.cat = AC_DummyHole};
global_variable Ast dummy_body_under_construction = {};

global_variable u64 global_next_form_id;
inline u64
getNextFormId()
{
  return global_next_form_id++;
}

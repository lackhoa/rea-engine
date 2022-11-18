#pragma once

#include "utils.h"
#include "engine.h"

global_variable Builtins builtins;

global_variable Ast    dummy_hole_ = {.cat = AC_DummyHole};
global_variable Ast   *dummy_hole  = &dummy_hole_;
global_variable Value *dummy_holev = (Value*)&dummy_hole_;

global_variable Ast dummy_function_under_construction;

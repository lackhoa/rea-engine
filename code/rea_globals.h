#pragma once

#include "utils.h"
#include "engine.h"

global_variable Builtins builtins;

global_variable Ast    holea_ = {.cat = AC_Hole};
global_variable Ast   *holea = &holea_;
global_variable Value  holev_ = {.cat = VC_Hole};
global_variable Value *holev = (Value *)&holev_;

global_variable Ast dummy_function_under_construction;

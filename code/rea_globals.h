#pragma once

#include "utils.h"
#include "engine.h"

global_variable Builtins builtins;

global_variable Ast dummy_hole = {.cat = AC_DummyHole};
global_variable Ast dummy_function_under_construction;

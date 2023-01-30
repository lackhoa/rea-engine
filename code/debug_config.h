#if !defined(DEBUG_H)

#include "utils.h"

global_variable i32 DEBUG_LOG_apply     = 0;
global_variable i32 DEBUG_LOG_normalize = 0;
global_variable i32 DEBUG_LOG_evaluate  = 0;
global_variable i32 DEBUG_LOG_compare   = 1;
global_variable i32 DEBUG_LOG_unify     = 0;
global_variable i32 DEBUG_LOG_solve     = 0;

global_variable i32 DEBUG_print_all_arguments = 1;

#define DEBUG_H
#endif

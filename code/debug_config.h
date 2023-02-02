#if !defined(DEBUG_H)

#include "utils.h"

global_variable b32 DEBUG_LOG_apply     = 0;
global_variable b32 DEBUG_LOG_normalize = 0;
global_variable b32 DEBUG_LOG_evaluate  = 0;
global_variable b32 DEBUG_LOG_compare   = 0;
global_variable b32 DEBUG_LOG_unify     = 0;
global_variable b32 DEBUG_LOG_solve     = 0;

global_variable b32 print_all_args  = 0;
global_variable b32 print_var_delta = 0;
global_variable b32 print_var_index = 0;

#define DEBUG_H
#endif

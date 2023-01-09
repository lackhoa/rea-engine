#if 0
          // todo #cleanup This powers the "destruct" syntax.
          i32 ctor_arg_count      = signature->param_count;
          i32 compare_param_count = ctor_arg_count*2 + 1;
          String  *param_names = pushArray(arena, compare_param_count, String);
          Term   **param_types = pushArray(arena, compare_param_count, Term*);
          for (i32 group=0; group <= 1; group++)
          {
            for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
            {
              String name = print(arena, "_");
              concat(&name, print(arena, signature->param_names[arg_id]));
              concat(&name, print(arena, "%d", group));
              i32 offset   = (group == 0) ? 0 : ctor_arg_count;
              i32 param_id = offset + arg_id;
              param_names[param_id] = name;
              param_types[param_id] = signature->param_types[arg_id];
            }
          }
          Term **lhs_args = pushArray(arena, ctor_arg_count, Term*);
          Term **rhs_args = pushArray(arena, ctor_arg_count, Term*);
          for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
          {
            i32 lhs_param_id = arg_id;
            i32 rhs_param_id = ctor_arg_count+arg_id;
            lhs_args[arg_id] = newVariable(arena, param_names[lhs_param_id], 0, lhs_param_id);
            rhs_args[arg_id] = newVariable(arena, param_names[rhs_param_id], 0, rhs_param_id);
          }
          Term *lhs = newComposite(arena, env, &ctor->t, ctor_arg_count, lhs_args);
          Term *rhs = newComposite(arena, env, &ctor->t, ctor_arg_count, rhs_args);
          param_names[compare_param_count-1] = toString("P");
          param_types[compare_param_count-1] = newEquality(arena, &uni->t, lhs, rhs);

          DestructList *destruct_list = pushStruct(global_state.arena, DestructList);
          destruct_list->next = global_state.builtin_destructs;
          global_state.builtin_destructs = destruct_list;
          destruct_list->uni     = uni;
          destruct_list->ctor_id = ctor_id;
          allocateArray(arena, ctor_arg_count, destruct_list->items);
          for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
          {
            Arrow *destruct_signature = newTerm(arena, Arrow, 0);
            destruct_signature->param_count = compare_param_count;
            destruct_signature->param_names = param_names;
            destruct_signature->param_types = param_types;
            allocateArray(arena, compare_param_count, destruct_signature->param_flags, true);
            destruct_signature->output_type = newEquality(arena, signature->param_types[arg_id], lhs_args[arg_id], rhs_args[arg_id]);

            Builtin *destruct = newTerm(arena, Builtin, &destruct_signature->t);
            destruct_list->items[arg_id] = &destruct->t;
          }
#endif

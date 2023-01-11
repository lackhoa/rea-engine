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

    case Ast_DestructAst:
    {
#if 0
      DestructAst *in = castAst(in0, DestructAst);
      if (BuildTerm build_eqp = buildTerm(arena, env, in->eqp, holev))
      {
        Term *eq = getType(arena, env, build_eqp.term);
        if (TermPair sides = getEqualitySides(eq, false))
        {
          Constructor *ctor = 0;
          Composite *lhs = 0;
          Composite *rhs = 0;
          if ((lhs = castTerm(sides.lhs, Composite)))
          {
            if (Constructor *lhs_ctor = castTerm(lhs->op, Constructor))
            {
              if ((rhs = castTerm(sides.rhs, Composite)))
              {
                if (Constructor *rhs_ctor = castTerm(rhs->op, Constructor))
                {
                  if (equal(&rhs_ctor->t, &lhs_ctor->t))
                    ctor = lhs_ctor;
                  else
                    parseError(in0, "lhs constructor is not equal to rhs constructor");
                }
                else
                  parseError(in0, "rhs must be a record");
              }
            }
            else
              parseError(in0, "lhs must be a record");
          }
          else
            parseError(in0, "lhs must be a record");

          if (hasError())
            attach("type", eq);
          else
          {
            i32 param_count = castTerm(ctor->type, Arrow)->param_count;
            if (in->arg_id < param_count)
            {
              for (DestructList *destructs = global_state.builtin_destructs;
                   destructs;
                   destructs = destructs->next)
              {
                // todo #speed
                if ((destructs->uni == ctor->uni) && (destructs->ctor_id == ctor->id))
                {
                  Composite *out = newTerm(arena, Composite, 0);
                  out->op        = destructs->items[in->arg_id];
                  out->arg_count = lhs->arg_count*2+1;
                  out->args      = pushArray(arena, out->arg_count, Term*);
                  // todo cleanup: use parameter type inference
                  for (i32 id=0; id < out->arg_count; id++)
                  {
                    if (id == out->arg_count-1)
                      out->args[id] = build_eqp.term;
                    else if (id < lhs->arg_count)
                      out->args[id] = lhs->args[id];
                    else
                      out->args[id] = rhs->args[id - lhs->arg_count];
                  }
                  out0.term = &out->t;
                  break;
                }
              }
            }
            else
              parseError(in0, "constructor only has %d parameters", param_count);
          }
        }
        else
          parseError(in0, "expected an equality proof as argument");
      }
#else
      parseError(in0, "destruct syntax has been deprecated, waiting for something better to emerge");
#endif
    } break;

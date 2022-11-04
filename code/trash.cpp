#if 0
      if (!subject_matched)
      {
        Fork *out = copyStruct(env.arena, in);
        out0 = out;
        out->subject = norm_subject;
        allocateArray(env.arena, out->case_count, out->cases);
        Environment *outer_env = &env;
        for (s32 case_id = 0; case_id < out->case_count; case_id++)
        {
          Environment env = *outer_env;
          Form *ctor = in->form->ctors + case_id;
          switch (ctor->type->cat)
          {
            case AC_Form:
            {
              extendStack(&env, 0, 0);
            } break;

            case AC_ArrowType:
            {
              introduceVariables(&env,
                                 castAst(ctor->type, ArrowType)->param_count,
                                 in->cases[case_id].params);
            } break;

            invalidDefaultCase;
          }
          out->cases[case_id]      = in->cases[case_id];
          out->cases[case_id].body = normalize(env, in->cases[case_id].body);
        }
      }
#endif

#if 0
        else if (isCompositeForm(lhs)
                 && isCompositeForm(rhs))
        {// Leibniz' principle
          Composite *lapp = castAst(lhs, Composite);
          Composite *rapp = castAst(rhs, Composite);
          assert(identicalB32(lapp->op, rapp->op)); // if they aren't equal then it'd already be false.

          CompositeV *out = newValue(env.arena, CompositeV, &in->h.token, );
          out0 = &out->h;

          if (lapp->arg_count > 1)
          {
            todoIncomplete;  // we need "and" expression
          }
          else
          {
            allocateArray(env.arena, 3, out->args);
            out->args[0] = in->args[0];
            out->args[1] = lapp->args[0];
            out->args[2] = rapp->args[0];
          }
        }
#endif






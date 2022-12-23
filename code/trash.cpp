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

#if 0
// this has to work on both values and terms
internal Term *
toAbstractTerm(MemoryArena *arena, Term *in0, i32 zero_depth)
{
  Term *out0 = 0;

  i32 serial = global_debug_serial++;
  b32 debug = false;
  if (global_debug_mode && debug)
  {debugIndent(); DUMP("toAbstractTerm(", serial, "): ", in0, " with zero_depth: ", zero_depth, "\n");}

  if (in0->anchor)
  {
    out0 = toAbstractTerm(arena, in0->anchor, zero_depth);
  }
  else
  {
    switch (in0->cat)
    {
      case Term_Constant:
      {out0 = in0;} break;

      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->is_absolute)
        {
          Variable *out = copyStruct(arena, in);
          out->is_absolute = false;
          out->stack_frame = zero_depth - in->stack_frame;
          assert(out->stack_frame >= 0);
          out0 = &out->t;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        out->op        = toAbstractTerm(arena, in->op, zero_depth);
        allocateArray(arena, out->arg_count, out->args);
        for (i32 id=0; id < out->arg_count; id++)
          out->args[id] = toAbstractTerm(arena, in->args[id], zero_depth);
        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        out->stack = 0;
        out0 = &out->t;
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = newTerm(arena, Computation, 0);
        out->lhs  = toAbstractTerm(arena, in->lhs, zero_depth);
        out->rhs  = toAbstractTerm(arena, in->rhs, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyStruct(arena, in);
        out->record = toAbstractTerm(arena, in->record, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in   = castTerm(in0, Rewrite);
        Rewrite *out  = copyStruct(arena, in);
        out->eq_proof = toAbstractTerm(arena, in->eq_proof, zero_depth);
        out->body     = toAbstractTerm(arena, in->body, zero_depth);
        out0 = &out->t;
      } break;

      case Term_Fork:
      {todoIncomplete;} break;

      // global values (and functions) should have anchors.
      case Term_Constructor:
      case Term_Builtin:
      case Term_Union:
      case Term_Function:
      case Term_Hole:
        invalidCodePath;
    }
  }

  assert(out0);
  if (global_debug_mode && debug)
  {debugDedent(); dump("=>("); dump(serial); dump(") "); dump(out0); dump();}
  return out0;
} 


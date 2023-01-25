// todo #cleanup a lot of the copies are unnecessary, we must think about where
// we can put stack values. and whether to have stack values at all.
//
// todo #cleanup I think this is now only for the global overloads typecheck for
// composites?  If so then just copy the composite, no need to deepcopy
internal Ast *
deepCopy(MemoryArena *arena, Ast *in0)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case Ast_Hole:
    case Ast_Identifier:
    {out0 = in0;} break;

    case Ast_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);
      CompositeAst *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, out->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
      {
        out->args[id] = deepCopy(arena, in->args[id]);
      }
      out0 = &out->a;
    } break;

    case Ast_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      ArrowAst *out = copyStruct(arena, in);
      out->output_type = deepCopy(arena, in->output_type);
      allocateArray(arena, out->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
      {
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      }
      out0 = &out->a;
    } break;

    case Ast_Let:
    {
      Let *in = castAst(in0, Let);
      Let *out = copyStruct(arena, in);
      out->rhs = deepCopy(arena, in->rhs);
      out0 = &out->a;
    } break;

    case Ast_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      RewriteAst *out = copyStruct(arena, in);
      out->eq_proof_hint = deepCopy(arena, in->eq_proof_hint);
      out0 = &out->a;
    } break;

    case Ast_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      AccessorAst *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->a;
    } break;

    invalidDefaultCase;
  }
  return out0;
}


#if 0
forward_declare inline Term *
computeType(MemoryArena *arena, Typer *typer, Term *in0)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  Term *out0 = 0;
  if (in0->type)
    out0 = in0->type;
  else
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        Scope *scope = typer->scope;
        for (i32 id=0; id < in->delta; id++)
          scope=scope->outer;
        
        assert(scope->depth == typer->scope->depth - in->delta);
        out0 = scope->first->param_types[in->id];
        out0 = rebase(arena, out0, in->delta);

        assert(out0);
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        if (Constructor *ctor = castTerm(in->op, Constructor))
        {
          assert(ctor->uni);
          out0 = &ctor->uni->t;  // todo this makes me nervous!
        }
        else
        {
          Term *op_type0 = getType(in->op);
          Arrow *op_type = castTerm(op_type0, Arrow);
          out0 = evaluate(arena, in->args, op_type->output_type);
        }
      } break;

      case Term_Arrow:
      {
        out0 = builtin_Type;
      } break;

      case Term_Function:
      {
        invalidCodePath;
      } break;

      case Term_Computation:
      {
        invalidCodePath;
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Term **args = 0;
        if (Composite *record = castTerm(in->record, Composite))
        {
          if (Constructor *ctor = castTerm(record->op, Constructor))
            args = record->args;
        }
        if (!args)
        {
          Constructor ctor = getConstructor(typer, in->record);
          args = synthesizeMembers(arena, in->record, ctor.id);
        }

        out0 = args[in->field_id]->type;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        auto [lhs, rhs] = getEqualitySides(getType(in->eq_proof));
        Term *rewrite_to = in->right_to_left ? rhs : lhs;
        out0 = rewriteTerm(arena, rewrite_to, in->path, getType(in->body));
      } break;

      case Term_Constructor:
      {
        Constructor *ctor = castTerm(in0, Constructor);
        out0 = &getConstructorType(ctor)->t;
      } break;

      default:
      {
        DUMP("The term is: ", in0);
        todoIncomplete;
      }
    }

    in0->type = out0;
  }
  assert(out0);
  return out0;
}
#endif

#if 0
internal Term *
newRecord(Union *uni, i32 ctor_index, ...)
{
  i32 param_count = uni->structs[ctor_index]->param_count;
  Term **args = pushArray(arena, param_count, Term*);

  va_list arg_list;
  __crt_va_start(arg_list, op);
  for (i32 i=0; i < param_count; i++)
  {
    args[i] = __crt_va_arg(arg_list, Term*);
  }
  __crt_va_end(arg_list);

  Constructor *ctor = uni->ctors[ctor_index];
  return newComposite(arena, &ctor->t, param_count);
}
#endif


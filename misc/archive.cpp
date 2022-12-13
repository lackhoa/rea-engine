#if 0
internal Ast *
toAst(MemoryArena *arena, i32 env_depth, Term* term)
{
  Ast *out0 = 0;
  Token token = newToken("<synthetic>");
  switch (term->cat)
  {
    case Term_StackPointer:
    {
      StackPointer *ptr = castTerm(term, StackPointer);
      Variable     *var = newAst(arena, Variable, &ptr->name);
      out0 = &var->a;
      if (ptr->is_absolute)
        var->stack_delta = env_depth - ptr->stack_frame;
      else
        var->stack_delta = ptr->stack_frame;
      var->id          = ptr->id;  // :stack-ref-id-has-significance
    } break;

    case Term_Composite:
    {
      Composite *compositev = castTerm(term, Composite);
      CompositeAst  *composite  = newAst(arena, CompositeAst, &token);
      composite->op        = toAst(arena, env_depth, compositev->op);
      composite->arg_count = compositev->arg_count;
      allocateArray(arena, composite->arg_count, composite->args);
      for (int id=0; id < composite->arg_count; id++)
      {
        composite->args[id] = toAst(arena, env_depth, compositev->args[id]);
      }
      out0 = &composite->a;
    } break;

    case Term_Accessor:
    {
      Accessor *accessorv = castTerm(term, Accessor);
      AccessorAst  *accessor  = newAst(arena, AccessorAst, &token);
      accessor->record      = toAst(arena, env_depth, accessorv->record);
      accessor->field_id    = accessorv->field_id;
      accessor->field_name  = newToken(accessorv->field_name);
      out0 = &accessor->a;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(term, Arrow);
      ArrowAst  *out = newAst(arena, ArrowAst, &token);
      out->param_count = in->param_count;
      out->param_names = in->param_names;
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
        out->param_types[id] = toAst(arena, env_depth+1, in->param_types[id]);
      out->output_type = toAst(arena, env_depth+1, in->output_type);
      out0 = &out->a;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Function:
    case Term_Constructor:
    {
      Constant *synthetic = newSyntheticConstant(arena, term);
      out0 = &synthetic->a;
    } break;

    case Term_Rewrite:
    {
      dump(); dump("-------------------"); dump(term);
      todoIncomplete;  // really we don't need it tho?
    } break;

    case Term_Hole:
    case Term_Computation:
    case Term_Fork:
    {todoIncomplete;}
  }

  assert(out0);

  return out0;
}
#endif

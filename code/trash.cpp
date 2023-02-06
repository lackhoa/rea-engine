struct EvaluationContext {
  Arena  *arena;
  Term **args;
  i32    offset;
  u32    flags;
};

#if 0
internal Term *
evaluate_(EvaluationContext *ctx, Term *in0)
{
  Term *out0 = 0;
  assert(ctx->offset >= 0);
  Arena *arena = ctx->arena;

  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_LOG_evaluate)
  {
    if (DEBUG_MODE)
    {DEBUG_INDENT(); DUMP("evaluate(", serial, "): ", in0, "\n");}
  }

  if (isGlobalValue(in0))
  {
    out0 = in0;
  }
  else
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->delta == ctx->offset)
        {
          out0 = rebase(arena, ctx->args[in->index], ctx->offset);
        }
        else if (in->delta > ctx->offset)
        {
          out0 = rebase(arena, in0, -1);
        }
        else
        {
          out0 = in0;
        }
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        Term **args = pushArray(arena, in->arg_count, Term *);

        Term *op = in->op;
        if (op->cat != Term_Constructor)
        {
          op = evaluate_(ctx, in->op);
        }

        for (i32 id=0; id < in->arg_count; id++)
        {
          args[id] = evaluate_(ctx, in->args[id]);
          assert(args[id]);
        }

        Term *type = evaluate_(ctx, getType(in0));  // :eval-type
        if (checkFlag(ctx->flags, EvaluationFlag_AlwaysApply))
        {
          out0 = apply(arena, op, in->arg_count, args, {});
        }

        if (!out0)
        {
          Composite *out = copyTerm(arena, in);
          out->op   = op;
          out->args = args;
          out->type = type;
          out0 = &out->t;
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);

        allocateArray(arena, out->param_count, out->param_types);
        ctx->offset++;
        for (i32 id=0; id < out->param_count; id++)
        {
          out->param_types[id] = evaluate_(ctx, in->param_types[id]);
        }
        if (in->output_type)
          out->output_type = evaluate_(ctx, in->output_type);
        ctx->offset--;

        out0 = &out->t;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyTerm(arena, in);
        out->type = evaluate_(ctx, getType(in0));  // :eval-type

        u32 old_flags = ctx->flags;
        unsetFlag(&ctx->flags, EvaluationFlag_AlwaysApply);
        ctx->offset++;
        out->body = evaluate_(ctx, in->body);
        ctx->offset--;
        ctx->flags = old_flags;

        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Term *record0 = evaluate_(ctx, in->record);
        if (auto [record, ctor] = castRecord(record0))
        {
          // note: we could honor "ctx->normalize" but idk who would actually want that.
          out0 = record->args[in->field_index];
        }
        else
        {
          Accessor *out = copyTerm(arena, in);
          out->record = record0;
          out->type = evaluate_(ctx, getType(in0));  // :eval-type
          out0 = &out->t;
        }
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = copyTerm(arena, in);
        out->type = evaluate_(ctx, getType(in0));  // :eval-type
        out0 = out;  // NOTE: copying since we might :eval-type below
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        if (Term *eq_proof = evaluate_(ctx, in->eq_proof))
        {
          if (Term *body = evaluate_(ctx, in->body))
          {
            Rewrite *out = copyTerm(arena, in);
            out->type = evaluate_(ctx, getType(in0));  // :eval-type
            out->eq_proof = eq_proof;
            out->body     = body;
            out0 = &out->t;
          }
        }
      } break;

      case Term_Fork:
      {
        Fork *in = castTerm(in0, Fork);
        Term *subject0 = evaluate_(ctx, in->subject);
        if (checkFlag(ctx->flags, EvaluationFlag_AlwaysApply))
        {
          if (Composite *subject = castTerm(subject0, Composite))
          {
            if (Constructor *ctor = castTerm(subject->op, Constructor))
            {
              out0 = evaluate_(ctx, in->bodies[ctor->index]);
            }
          }
        }
        else
        {
          Fork *out = copyTerm(arena, in);
          out->type = evaluate_(ctx, getType(in0));  // :eval-type
          out->subject = subject0;
          allocateArray(arena, in->case_count, out->bodies);
          for (i32 id=0; id < in->case_count; id++)
          {
            out->bodies[id] = evaluate_(ctx, in->bodies[id]);
          }
          out0 = &out->t;
        }
      } break;

#if 0
      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyTerm(arena, in);
        allocateArray(arena, in->ctor_count, out->structs);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *struc = evaluate_(ctx, &in->structs[id]->t);
          out->structs[id] = castTerm(struc, Arrow);
        }
        out0 = &out->t;
      } break;
#endif

      case Term_Primitive:
      case Term_Hole:
      {out0=in0;} break;

      default:
        invalidCodePath;
    }
  }

  if(DEBUG_LOG_evaluate)
  {
    if (DEBUG_MODE) {DEBUG_DEDENT(); DUMP("=>(", serial, ") ", out0, "\n");}
  }

  assert(checkFlag(ctx->flags, EvaluationFlag_AlwaysApply) || out0);
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

#if 0
        signature->param_count += poly_count;
        allocateArray(arena, signature->param_count, signature->param_names);
        allocateArray(arena, signature->param_count, signature->param_types);
        allocateArray(arena, signature->param_count, signature->param_flags);
        for (i32 param_i=0; param_i < poly_count; param_i++)
        {
          signature->param_names[param_i] = uni_params->param_names[param_i];
          signature->param_types[param_i] = uni_params->param_types[param_i];
          signature->param_flags[param_i] = uni_params->param_flags[param_i] | ParameterFlag_Inferred;  // todo actually you can't infer the union parameter in case there's no arg (f.ex nil Nat), but the compiler will complain in that case so it's fine.
        }
        ProcessPolyConstructorTypeContext ctx = {.arena=arena, .poly_param_count=poly_count};
        for (i32 param_i=0; param_i < struc->param_count; param_i++)
        {
          signature->param_names[poly_count+param_i] = struc->param_names[param_i];
          signature->param_types[poly_count+param_i] = processPolyConstructorType(&ctx, struc->param_types[param_i]);
          signature->param_flags[poly_count+param_i] = struc->param_flags[param_i];
        }

        if (non_poly_count)
        {
          signature->output_type = processPolyConstructorType(&ctx, struc->output_type);
        }
        else
        {
          signature->output_type = &common_ctor_output_type->t;
        }

        if (noError())
        {
          PolyConstructor *pctor = newTerm(arena, PolyConstructor, &signature->t);
          pctor->uni   = uni;
          pctor->index = ctor_i;
          addGlobalBinding(&in->ctor_names[ctor_i], &pctor->t);
          uni->global_ctors[ctor_i] = &pctor->t;
        }
#endif

#if 0
        if (noError() && non_poly_count)
        {
          // building the inverts
          i32 param_count = uni_param_count+2;

          TermBuilder builder_ = {.arena=arena, typer=typer};
          auto builder = &builder;
          beginFunction(builder);
          {
            beginSignature(builder, param_count);
            for (i32 i=0; i < uni_param_count; i++)
            {
              addParameter(builder, uni_params->param_names[i], uni_params->param_types[i]);
            }
            i32 p_index = addParameter(builder, toString("p"), &common_ctor_output_type->t);  // todo Avoid name collision
            addParameter(builder, {},
                         newCompositeB(builder, rea_ctor_is,
                                       newVariable(builder, 0, param_count-2),
                                       newPrimitiveI32(builder, ctor_i)));

            beginConjunction(builder);
            addConjunct(builder, newEquality(builder, newAccessor(builder, newVariable(builder, 0, p_index))));
            Term *output = endConjunction(builder);

            setOutput(builder, output);
            endSignature(builder);
          }
          Term *fun = endFunction(builder);

          Union *output_type = newTerm(arena, Union, rea_Type);
          output_type->ctor_count = 1;
          output_type->structs    = pushArray(arena, 1, Arrow *);
          output_type->structs[0] = output_struc;

          Arrow *signature = newArrow(arena, param_count, param_names, param_types, 0, &output_type->t);
        }
#endif

#if 0
inline Term **
synthesizeMembers(Arena *arena, Term *parent, i32 ctor_index)
{
  auto [uni, args] = castUnion(getType(parent));
  Arrow *struc = getConstructorSignature(uni, ctor_index);
  i32 param_count = struc->param_count;
  Term **members = pushArray(temp_arena, param_count, Term *);
  i32 poly_count = 0;
  if (Arrow *uni_params = castTerm(getType(&uni->t), Arrow))
  {
    poly_count = getPolyParamCount(uni_params);
  }
  for (i32 field_i=0; field_i < poly_count; field_i++)
  {
    members[field_i] = args[field_i];
  }
  for (i32 field_i=poly_count; field_i < param_count; field_i++)
  {
    String field_name = struc->param_names[field_i];
    Term *type = evaluate({.args=members}, struc->param_types[field_i]);
    Accessor *accessor    = newTerm(arena, Accessor, type);
    accessor->record      = parent;
    accessor->field_index = field_i;
    accessor->debug_field_name  = field_name;
    members[field_i] = &accessor->t;
  }
  return members;
}

inline Term *
synthesizeTree(Arena *arena, Term *parent, DataTree *tree)
{
  Composite *record = 0;
  auto [uni, poly_args] = castUnion(getType(parent));
  Arrow *struc = getConstructorSignature(uni, tree->ctor_i);
  Constructor *ctor = uni->constructors[tree->ctor_i];
  i32 param_count = struc->param_count;
  record = newTerm(arena, Composite, parent->type);
  record->op        = &ctor->t;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term *);
  Term **members = synthesizeMembers(arena, parent, tree->ctor_i);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    DataTree *member_tree = tree->members[field_id];
    if (member_tree)
      record->args[field_id] = synthesizeTree(arena, members[field_id], member_tree);
    else
      record->args[field_id] = members[field_id];
  }
  return &record->t;
}
#endif

#if 0
internal void
printDataMap(Arena *buffer, Typer *typer)
{
  for (DataMap *map = typer->map; map; map=map->tail)
  {
    Term *root = newVariable(temp_arena, typer, getScopeDepth(typer) - map->depth, map->index);
    print(buffer, castTerm(root, Variable)->name);
    print(buffer, ": ");
    Term *tree = synthesizeTree(temp_arena, root, &map->tree);
    PrintOptions print_options = {.print_type_depth=2};
    print(buffer, tree, print_options);
    if (map->tail)
      print(buffer, "\n");
  }
}
#endif

#if 0
// todo: factoring this out might be a big mistake
inline Term *
normalizeVariable(Arena *arena, DataMap *data_map, i32 depth, Variable *in)
{
  Term *out = &in->t;
  i32 var_depth = depth - in->delta;
  DataTree *tree = 0;
  for (DataMap *map = data_map; map; map=map->tail)
  {
    if (map->depth == var_depth && map->index == in->index)
    {
      tree = &map->tree;
      break;
    }
  }
  if (tree)
  {
    out = synthesizeTree(arena, &in->t, tree);
  }
  return out;
}
#endif


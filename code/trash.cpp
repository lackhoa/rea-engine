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

#if 0
internal AddDataTree
getOrAddDataTree(Arena *arena, Typer *typer, Term *in0, i32 ctor_i)
{
  DataTree *tree = 0;
  b32 added = false;
  i32 scope_depth = getScopeDepth(typer);

  Variable *in_root = 0;
  i32    path_length = 0;
  Term *reverse_unions[32];
  u8    reverse_path[32];
  Term *iter0 = in0;
  Term *root_union = 0;
  for (b32 stop = false ;!stop;)
  {
    Term *uni = getType(iter0);
    switch (iter0->cat)
    {
      case Term_Variable:
      {
        in_root = castTerm(iter0, Variable);
        root_union = uni;
        stop = true;
      } break;

      case Term_Accessor:
      {
        Accessor *iter = castTerm(iter0, Accessor);
        i32 path_id = path_length++;
        assert(path_length < arrayCount(reverse_path));
        reverse_unions[path_id] = uni;
        reverse_path[path_id]   = iter->field_index;
        iter0 = iter->record;
      } break;

      default:
      {
        stop = true;
      } break;
    }
  }

  i32 in_root_depth = scope_depth - in_root->delta;
  for (DataMap *map = typer->map; map; map=map->tail)
  {
    if (map->depth == in_root_depth && map->index == in_root->index)
    {
      tree = &map->tree;
      break;
    }
  }
  if (!tree)
  {
    if (path_length == 0)
    {
      if (ctor_i != -1)
      {
        DataMap *map = pushStruct(arena, DataMap, true);
        map->depth   = in_root_depth;
        map->index   = in_root->index;
        initDataTree(arena, &map->tree, root_union, ctor_i);
        tree = &map->tree;
        map->tail    = typer->map;
        typer->map     = map;

        DataMapAddHistory *history = pushStruct(temp_arena, DataMapAddHistory, true);
        history->previous_map = map->tail;
        history->previous     = typer->add_history;
        typer->add_history = history;
        added = true;
      }
    }
    else 
    {
      assert(castUnionOrPolyUnion(root_union)->ctor_count == 1);
      DataMap *map = pushStruct(arena, DataMap, true);
      map->depth   = in_root_depth;
      map->index   = in_root->index;
      initDataTree(arena, &map->tree, root_union, 0);
      tree = &map->tree;
      map->tail = typer->map;
      typer->map = map;
    }
  }

  for (i32 path_index=0; path_index < path_length; path_index++)
  {
    i32   reverse_index = path_length-1-path_index;
    i32   field_index   = reverse_path[reverse_index];
    Term *uni           = reverse_unions[reverse_index];
    DataTree *parent = tree;
    tree = tree->members[field_index];
    if (!tree)
    {
      if (path_index == path_length-1)
      {
        if (ctor_i != -1)
        {
          DataTree *new_tree = pushStruct(arena, DataTree, true);
          initDataTree(arena, new_tree, uni, ctor_i);
          parent->members[field_index] = new_tree;
          tree = new_tree;

          DataMapAddHistory *history = pushStruct(temp_arena, DataMapAddHistory, true);
          history->parent      = parent;
          history->field_index = field_index;
          history->previous = typer->add_history;
          typer->add_history = history;
          added = true;
        }
      }
      else
      {
        assert(castUnionOrPolyUnion(uni)->ctor_count == 1);
        DataTree *new_tree = pushStruct(arena, DataTree, true);
        initDataTree(arena, new_tree, uni, 0);
        parent->members[field_index] = new_tree;
        tree = new_tree;
      }
    }
  }
  
  return AddDataTree{.tree=tree, .added=added};
}

internal DataTree *
getDataTree(Typer *env, Term *in0)
{
  return getOrAddDataTree(0, env, in0, -1).tree;
}
#endif

struct DataTree {
  i32        ctor_i;
  i32        member_count;
  DataTree **members;
  Union     *debug_uni;
};

struct DataMapAddHistory {
  // option A: root 
  DataMap      *previous_map;
  // option B: branch
  DataTree     *parent;
  i32           field_index;

  DataMapAddHistory *previous;
};

struct DataMap {
  i32       depth;
  i32       index;
  DataTree  tree;
  DataMap  *tail;
};

#if 0
// todo make this an inline mutation
internal Term *
rebase_(Arena *arena, Term *in0, i32 delta, i32 offset)
{
  Term *out0 = 0;
  if (!isGround(in0) && (delta != 0))
  {
    switch (in0->kind)
    {
      case Term_Variable:
      {
        Variable *in  = castTerm(in0, Variable);
        if (in->delta >= offset)
        {
          Variable *out = copyTerm(arena, in);
          out->delta += delta; assert(out->delta >= 0);
          out0 = out;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyTerm(arena, in);
        if (in->op->kind == Term_Constructor)
        {
          // we copied the constructor index, and that's enough.
        }
        else
        {
          out->op = rebase_(arena, out->op, delta, offset);
        }
        allocateArray(arena, out->arg_count, out->args);
        for (i32 id = 0; id < out->arg_count; id++)
        {
          out->args[id] = rebase_(arena, in->args[id], delta, offset);
        }
        out0 = out;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyTerm(arena, in);
        allocateArray(arena, in->param_count, out->param_types);
        for (i32 id=0; id < in->param_count; id++)
          out->param_types[id] = rebase_(arena, in->param_types[id], delta, offset+1);
        if (in->output_type)
        {
          out->output_type = rebase_(arena, in->output_type, delta, offset+1);
        }
        out0 = out;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyTerm(arena, in);
        out->record = rebase_(arena, in->record, delta, offset);
        out0 = out;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in  = castTerm(in0, Rewrite);
        Rewrite *out = copyTerm(arena, in);
        out->eq_proof = rebase_(arena, in->eq_proof, delta, offset);
        out->body     = rebase_(arena, in->body, delta, offset);
        out0 = out;
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = copyTerm(arena, in);
        out0 = out;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyTerm(arena, in);
        out->body = rebase_(arena, in->body, delta, offset+1);
        out0 = out;
      } break;

#if 0
      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyTerm(arena, in);
        allocateArray(arena, in->ctor_count, out->structs);
        for (i32 i=0; i < in->ctor_count; i++)
        {
          Term *rebased = rebase_(arena, &in->structs[i]->t, delta, offset);
          out->structs[i] = castTerm(rebased, Arrow);
        }
        out0 = out;
      } break;
#endif

      case Term_Constructor:
      {
        invalidCodePath;
      } break;

      default:
        todoIncomplete;
    }
    if (out0 != in0)
    {
      out0->type = rebase_(arena, getType(in0), delta, offset);
    }
  }
  else
    out0 = in0;

  assert(out0);
  return out0;
}

forward_declare internal Term *
rebase(Arena *arena, Term *in0, i32 delta)
{
  return rebase_(arena, in0, delta, 0);
}
#endif

#if 0
inline Term *
newConjunctionN(Arena *arena, i32 count, Term **conjuncts)
{
  Term *out0 = 0;
  assert(count != 0);  // return True? :>
  if (count == 1)
  {
    out0 = conjuncts[0];
  }
  else
  {
    Arrow *struc = newTerm(arena, Arrow, rea_Type);
    struc->param_count = count;
    struc->param_names = pushArray(arena, count, String);
    struc->param_types = pushArray(arena, count, Term *);

    for (i32 i=0; i < count; i++)
    {
      assert(i < arrayCount(number_to_string));
      struc->param_names[i] = number_to_string[i];
      struc->param_types[i] = rebase(arena, conjuncts[i], 1);
    }

    Union *out = newTerm(arena, Union, rea_Type);
    out->ctor_count = 1;
    out->structs    = pushArray(arena, 1, Arrow*);
    out->structs[0] = struc;
    out0 = out;
  }
  return out0;
}
#endif

#if 0
    if (Composite *l = castTerm(l0, Composite))
    {
      if (Composite *r = castTerm(r0, Composite))
      {
        if (Constructor *lctor = castTerm(l->op, Constructor))
        {
          if (Constructor *rctor = castTerm(r->op, Constructor))
          {
            can_destruct = (lctor->index == rctor->index);
          }
        }

        if (Union *luni = castTerm(l->op, Union))
        {
          if (Union *runi = castTerm(r->op, Union))
          {
            can_destruct = (luni == runi);
          }
        }

        if (can_destruct)
        {
          assert(l->arg_count == r->arg_count);
          i32 arg_count = l->arg_count;
          if (arg_count == 0)
          {
            // since we can't return "True", nothing to do here
          }
          else if (arg_count == 1)
          {
            i32 arg_i = 0;
            Term *conjunct = newEquality(arena, l->args[arg_i], r->args[arg_i]);
            Composite *composite = castTerm(conjunct, Composite);
            if (Term *more = apply(arena, composite->op, composite->arg_count, composite->args, name_to_unfold))
            {
              conjunct = more;
            }

            out0 = conjunct;
          }
          else
          {
            todoIncomplete;
#if 0
            Term **conjuncts = pushArray(temp_arena, arg_count, Term *);
            for (i32 arg_i=0; arg_i < arg_count; arg_i++)
            {
              Term *conjunct = newEquality(arena, l->args[arg_i], r->args[arg_i]);
              Composite *composite = castTerm(conjunct, Composite);
              if (Term *more = apply(arena, composite->op, composite->arg_count, composite->args, name_to_unfold))
              {
                conjunct = more;
              }

              // todo #leak the conjuncts are gonna be rebased anyway, haizz
              conjuncts[arg_i] = conjunct;
            }
            out0 = newConjunctionN(arena, arg_count, conjuncts);
#endif
          }
        }
      }
    }
#endif

inline Fork *
newForkOld(Term *subject, i32 case_count, Term **cases, Term *goal)
{
  i32 unused_var serial = DEBUG_SERIAL;
  Arena *arena = temp_arena;
  Union *uni = getUnionOrPolyUnion(subject->type);
  assert(case_count == uni->ctor_count);
  for (i32 i=0; i < case_count; i++)
  {
    instantiate(subject, i);
    assertEqualNorm(cases[i]->type, goal);
    uninstantiate(subject);
  }

  Fork *out = newTerm(arena, Fork, goal);
  out->subject    = subject;
  out->case_count = case_count;
  out->cases      = cases;
  return out;
}

// TODO: I think we can eliminate this comparison by simply storing a temporary
// pointer in the fork case.
inline b32
equalPointer(Term *l0, Term *r0)
{
  b32 out = false;
  Pointer *l = castTerm(l0, Pointer);
  Pointer *r = castTerm(r0, Pointer);
  if (l && r)
  {
    if (l->pointer_kind == Pointer_Stack &&
        r->pointer_kind == Pointer_Stack)
    {
      out = (l->stack.depth == r->stack.depth &&
             l->stack.index == r->stack.index);
    }
    else if (l->pointer_kind == Pointer_Heap &&
             r->pointer_kind == Pointer_Heap &&
             l->heap.index == r->heap.index)
    {
      // TODO: not happy with this "looping up" thing. Since "compareTerms"
      // might have already compared the parents, then descend down.
      out = equalPointer(l->heap.record, r->heap.record);
    }
  }
  return out;
}


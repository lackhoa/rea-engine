#if 0
// todo this seems like a massive waste of time, maybe we can try using the data
// tree directly.
inline Composite *
makeFakeRecord(MemoryArena *arena, Term *parent, DataTree *tree)
{
  Composite *record = 0;
  Constructor *ctor = newTerm(arena, Constructor, 0);
  ctor->uni = tree->uni;
  ctor->id  = tree->ctor_id;
  Arrow *ctor_sig = getType(ctor);
  i32 param_count = ctor_sig->param_count;
  record = newTerm(arena, Composite, 0);
  record->op        = &ctor->t;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term*);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = ctor_sig->param_names[field_id].string;
    Accessor *accessor = newTerm(arena, Accessor, 0);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    DataTree *member_tree = tree->members[field_id];
    if (member_tree)
      record->args[field_id] = &makeFakeRecord(arena, &accessor->t, member_tree)->t;
    else
      record->args[field_id] = &accessor->t;
  }
  return record;
}
#endif

#if 0
inline void
removeLatestDataTree(Typer *env)
{
  DataMapAddHistory *history = env->add_history;
  if (history->map)
  {
    assert(history->map == env->map);
    env->map = env->map->next;
  }
  else
    history->parent->members[history->field_index] = 0;

  env->add_history = history->next;
}
#endif

#if 0
internal GetOrAddDataTree
getOrAddDataTree(MemoryArena *arena, Typer *env, Term *subject, i32 ctor_id)
{
  // :subject_is_well_typed
  DataTree *tree = 0;

  if (in_root)
  {
    i32 in_root_depth = scope_depth - in_root->delta;
    for (DataMap *map = env->map; map; map=map->next)
    {
      if (map->depth == in_root_depth && map->index == in_root->index)
      {
        tree = &map->tree;
        break;
      }
    }

    if (!tree)
    {
      Union *root_uni = castTerm(getType(temp_arena, env, &in_root->t), Union);
      if (arena && root_uni)
      {
        added = true;
        DataMap *new_map = pushStruct(arena, DataMap, true);
        new_map->depth   = in_root_depth;
        new_map->index   = in_root->index;
        new_map->next    = env->map;
        env->map     = new_map;
        initDataTree(arena, &new_map->tree, root_uni, ctor_id);
        tree = &new_map->tree;
        if (path_length == 0)
        {
          DataMapAddHistory *history = pushStruct(arena, DataMapAddHistory, true);
          history->map  = new_map;
          history->next = env->add_history;
          env->add_history = history;
        }
      }
    }

    for (i32 reverse_index = path_length-1;
         (reverse_index >= 0) && tree;
         reverse_index--)
    {
      i32    field_index = reverse_path[reverse_index];
      Union *uni         = reverse_unions[reverse_index];
      DataTree *parent = tree;
      tree = tree->members[field_index];
      if (!tree && arena)
      {
        assert(reverse_index == 0 || uni->ctor_count == 1);
        i32 new_ctor_id = (reverse_index == 0) ? ctor_id : 0;
        DataTree *new_tree = pushStruct(arena, DataTree, true);
        initDataTree(arena, new_tree, uni, new_ctor_id);
        parent->members[field_index] = new_tree;
        tree = new_tree;
        if (reverse_index == 0)
        {
          added = true;
          DataMapAddHistory *history = pushStruct(arena, DataMapAddHistory, true);
          history->parent      = parent;
          history->field_index = field_index;
          history->next        = env->add_history;
          env->add_history = history;
        }
      }
    }
  }
  
  return GetOrAddDataTree{.tree=tree, .added=added};
}
#endif

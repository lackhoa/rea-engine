#if 0
// array version
internal Term *
algebraSort(Typer *typer, i32 count, Term **in)
{
  Term **out = copyArray(temp_arena, count, in);
  i32 *indexes = pushArray(temp_arena, count, i32);
  for (i32 i=0; i < count; i++) { indexes[i] = i; }
  quickSort(out, indexes, count);
  i32 *inverse = pushArray(temp_arena, count, i32);
  for (i32 i=0; i < count; i++) { inverse[indexes[i]] = i; }
  i32 *subtracted = pushArray(temp_arena, count, i32);
  for (i32 i=0; i < count; i++)
  {
    subtracted[i] = inverse[i];
    for (i32 left_index=0; left_index < i; left_index++)
    {
      if (inverse[left_index] < inverse[i])
      {
        subtracted[i]--;
      }
    }
  }
  Term *proof = provePermute(typer, in, out, subtracted, count);
  return proof;
}
#endif

internal Term *
provePermute_(Typer *typer, Term *al, Term **c_bac, i32 *indexes, i32 count)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  Arena *arena = temp_arena;
  Term *out = 0;
  assert(count > 0);
  local_persist Term *helper = lookupBuiltin("provePermuteHelper");

  Term *T = getType(c_bac[0]);
  Term *bac = toReaList(c_bac, count);

  // DUMP("provePermute_: (", al, ") and (", bac, ") \n");

  if (count == 1)
  {
    Term *bac = toReaList(c_bac, count);
    Term *eq = reaEqualByComputation(arena, typer, al, bac);
    out = newCompositeN(arena, rea.permuteSame, T, al, bac, eq);
  }
  else
  {
    i32 a_index = indexes[0];
    Term *l = getArg(al, 1);

    Term **c_bc = pushArray(temp_arena, count-1, Term *);
    for (i32 i=0; i < a_index; i++)
    {
      c_bc[i] = c_bac[i];
    }
    for (i32 i=a_index+1; i < count; i++)
    {
      assert(i-1 < count-1);
      c_bc[i-1] = c_bac[i];
    }
    Term *bc = toReaList(c_bc, count-1);

    Term *a = getArg(al, 0);
    Term *b = (a_index > 0)       ? toReaList(c_bc, a_index)                   : 0;
    Term *c = (a_index+1 < count) ? toReaList(c_bc+a_index, count-(a_index+1)) : 0;

    Term *recurse = provePermute_(typer, l, c_bc, indexes+1, count-1);

    Term *al_destruct = reaIdentity(arena, al);
    if (b && c)
    {// permute
      Term *bac_destruct = reaEqualByComputation(arena, typer, bac, reaConcat(arena, b, reaCons(arena, a, c)));
      Term *b_plus_c = reaConcat(arena, b, c);
      Term *e = reaEqualByComputation(arena, typer, bc, b_plus_c);
      recurse = newCompositeN(arena, helper, T, l,bc,b_plus_c, recurse,e);
      out = newCompositeN(arena, rea.permute, T,al,bac,
                          a,l,b,c, al_destruct,bac_destruct, recurse);
    }
    else if (c)
    {// permuteFirst
      Term *bac_destruct = reaEqualByComputation(arena, typer, bac, reaCons(arena, a, c));
      out = newCompositeN(arena, rea.permuteFirst, T,al,bac,
                          a,l,c, al_destruct,bac_destruct, recurse);
    }
    else
    {// permuteLast
      Term *bac_destruct = reaEqualByComputation(arena, typer, bac, reaConcat(arena, b, reaSingle(arena, a)));
      out = newCompositeN(arena, rea.permuteLast, T,al,bac,
                          a,l,b, al_destruct,bac_destruct, recurse);
    }
  }
  return out;
}

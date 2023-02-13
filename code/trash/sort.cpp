// list version
internal Term *
algebraSort(Term *in0)
{
  Record *in = castRecord(in0);
  Term *out = 0;
  Term *T = reaListType(in);
  if (reaIsSingle(in))
  {
    out = reaComposite(rea.permuteSingle, T, reaHead(in));
  }
  else
  {
    Term *head = reaHead(in);
    Term *tail = reaTail(in);
    Term *tail_sort = algebraSort(castRecord(tail));
    Term *right = getPermuteRhs(tail_sort);
    Term *skip = reaComposite(rea.permuteSkip, T, tail, right, tail_sort);

    const i32 cap = 32;  // todo #grow
    Term *left[cap];
    i32 left_count = 0;

    for (;;)
    {
      if (algebraLessThan(reaHead(right), head))
      {
        assert(left_count < cap);
        left[left_count++] = reaHead(right);
        if (reaIsSingle(right))
        {
          right = 0;
          break;
        }
        else
        {
          right = reaTail(right);
        }
      }
      else
        break;
    }
    
    if (left_count)
    {
      if (right)
      {
        todoIncomplete;
      }
      else
      {
        Term *p = reaComposite(rea.permuteConsSwap, T, head, toReaList(left, left_count));
        out = reaComposite(rea.permuteChain, T);
      }
    }
    else
    {
      // skip
      out = reaComposite(rea.permuteSkip, T, head, tail, right, tail_sort);
    }
  }
  return out;
}


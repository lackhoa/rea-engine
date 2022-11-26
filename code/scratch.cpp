struct ValuePair {Value *lhs; Value *rhs;};

inline ValuePair getLhsRhs(Value *eq0)
{
  CompositeV *eq = castValue(eq0, CompositeV);
  assert(eq->op == &builtins.equal->v);
  return ValuePair{eq->args[1], eq->args[2]};
}

#if 0
          if (global_debug_mode)
          {
            dump("outer_rewrite equality: "); dump(outer_rewrite->eq_proof->type); dump();
            dump("outer_rewrite path: "); dump(outer_rewrite->path); dump();
            dump("outer_rewrite body type: "); dump(rewritev->type); dump();
          }
          if (global_debug_mode)
          {
            dump("outer_rewrite resulting type: "); dump(type); dump();
          }
#endif

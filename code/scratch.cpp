struct ValuePair {Value *lhs; Value *rhs;};

inline ValuePair getLhsRhs(Value *eq0)
{
  CompositeV *eq = castValue(eq0, CompositeV);
  assert(eq->op == &builtins.equal->v);
  return ValuePair{eq->args[1], eq->args[2]};
}

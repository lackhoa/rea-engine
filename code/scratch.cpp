#if 0
internal void
parseExpression(EngineState *state, InstructionVector *instructions, Bindings *bindings, AstIterator *it, char end_delimiter = 0)
{
    MemoryArena *permanent = &state->permanent_arena;
    b32 not_empty = (it->list.c
                     && !isChar(it->list.c->car.token, end_delimiter));
    if (not_empty)
    {
        Ast *first = advance(it);
        b32 is_combination = (it->list.c
                              && !isChar(it->list.c->car.token, end_delimiter));
        if (is_combination)
        {
            // NOTE: the first thing is either a unary op, a function call, an
            // identifier, or a composite expression.
            if (first->is_branch)
            {
                todoIncomplete;
            }
            else
            {
                // NOTE: This is a composite: operator + operands.
                OpId op_id = lookupOperator(state, first);
                if (op_id)
                {
                    // MARK: Function call.
                    // TODO: could also be unary operator, but I suspect they go through the same path?
                    result.op = op_id;
                    AstList args = parseList(it);
                    if (args.c)
                    {
                        ExpressionList *dst = &result.args;
                        AstIterator arg_it = getIterator(args);
                        while (arg_it.list.c)
                        {
                            dst->c = pushStruct(permanent, ExpressionListContent);
                            dst->c->car = parseExpression(state, bindings, &arg_it);
                            dst = &dst->c->cdr;
                        }
                    }
                }
                else
                    todoErrorReport;
            }
        }
        else
        {
            if (first->is_branch)
            {
                AstIterator it = getIterator(first->children);
                // NOTE: Extra parens don't matter (we're not lisp).
                result = parseExpression(state, bindings, &it);
            }
            else
            {
                result.type = ExpressionTypeAtom;
                s32 id = lookupAtom(bindings, first);
                if (!id)
                    todoErrorReport;
                result.atom_id = id;
            }
        }
    }
    return result;
}
#endif

struct Binding
{};

int foo()
{
    
}

int main()
{
}

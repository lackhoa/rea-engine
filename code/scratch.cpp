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

string Convert(const CXString& s)
{
  string result = clang_getCString(s);
  clang_disposeString(s);
  return result;
}

void print_function_prototype(CXCursor cursor)
{
    // TODO : Print data! 
    auto type = clang_getCursorType(cursor);

    auto function_name = Convert(clang_getCursorSpelling(cursor));
    auto return_type   = Convert(clang_getTypeSpelling(clang_getResultType(type)));

    int num_args = clang_Cursor_getNumArguments(cursor);
    for (int i = 0; i < num_args; ++i)
    {
        auto arg_cursor = clang_Cursor_getArgument(cursor, i);
        auto arg_name = Convert(clang_getCursorSpelling(arg_cursor));
        if (arg_name.empty())
        {
            arg_name = "no name!";
        }

        auto arg_data_type = Convert(clang_getTypeSpelling(clang_getArgType(type, i)));
    }
}
CXChildVisitResult functionVisitor(CXCursor cursor, CXCursor /* parent */, CXClientData /* clientData */)
{
    if (clang_Location_isFromMainFile(clang_getCursorLocation(cursor)) == 0)
        return CXChildVisit_Continue;

    CXCursorKind kind = clang_getCursorKind(cursor);
    if ((kind == CXCursorKind::CXCursor_FunctionDecl || kind == CXCursorKind::CXCursor_CXXMethod || kind == CXCursorKind::CXCursor_FunctionTemplate || \
         kind == CXCursorKind::CXCursor_Constructor))
    {
        print_function_prototype(cursor);
    }

    return CXChildVisit_Continue;
}

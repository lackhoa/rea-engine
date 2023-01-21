void eatToken(Tokenizer * tk);
Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
Term * getType(Term * in0);
void dump(Trinary trinary);
void unwindScope(Typer * env);
void unwindBindingsAndScope(Typer * env);
void dump(Term * in0);
void dump(Ast * in0);
void DEBUG_INDENT();
void DEBUG_DEDENT();
void print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
void print(MemoryArena * buffer, Ast * in0);
void print(MemoryArena * buffer, Term * in0, PrintOptions opt);
void print(MemoryArena * buffer, Term * in0);
void print(MemoryArena * buffer, void * in0, b32 is_absolute, PrintOptions opt);
Scope * newScope(Scope * outer, Arrow * signature);
b32 equal(Term * lhs, Term * rhs);
Term * rebase(MemoryArena * arena, Term * in0, i32 delta);
Term * evaluate(MemoryArena * arena, Term ** args, Term * in0);
Term * evaluate(EvaluationContext ctx, Term * in0);
CompareTerms compareTerms(MemoryArena * arena, Term * lhs0, Term * rhs0);
Trinary equalTrinary(Term * lhs0, Term * rhs0);
Term * normalize(MemoryArena * arena, Typer * env, Term * in0);
void introduceSignature(Typer * typer, Arrow * signature, b32 add_bindings);
Term * solveGoal(Solver * solver, Term * goal);
BuildTerm buildTerm(MemoryArena * arena, Typer * typer, Ast * in0, Term * goal);
Term * buildFork(MemoryArena * arena, Typer * env, ForkAst * in, Term * goal);
Term * newRewrite(MemoryArena * arena, Term * eq_proof, Term * body, TreePath * path, b32 right_to_left);
Ast * parseFork(MemoryArena * arena);
Term * buildUnion(MemoryArena * arena, Typer * typer, UnionAst * in, Token * global_name);
Ast * parseExpression(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);

Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
Term * newComputation(MemoryArena * arena, Term * lhs, Term * rhs);
Term * getType(MemoryArena * arena, Typer * env, Term * in0);
Term * getType(Typer * env, Term * in0);
Term * getTypeNoEnv(Term * in0);
void dump(Trinary trinary);
void unwindStack(Typer * env);
void unwindBindingsAndStack(Typer * env);
void dump(Term * in0);
void dump(Ast * in0);
void debugIndent();
void debugDedent();
char * print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Ast * in0);
char * print(MemoryArena * buffer, Term * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Term * in0);
char * print(MemoryArena * buffer, void * in0, b32 is_absolute, PrintOptions opt);
void extendStack(Typer * env, i32 cap, Value ** items);
void addToStack(Typer * env, Value * value);
b32 equal(Term * lhs, Term * rhs);
Term * rebase(MemoryArena * arena, Term * in0, i32 delta, i32 offset);
Term * rebase(MemoryArena * arena, Term * in0, i32 delta);
Value * evaluate(MemoryArena * arena, Stack * stack, Term * in0, i32 offset);
Value * evaluateWithArgs(MemoryArena * arena, i32 arg_count, Term ** args, Term * in0);
CompareTerms compareTerms(MemoryArena * arena, Term * lhs0, Term * rhs0);
Trinary equalTrinary(Term * lhs0, Term * rhs0);
Term * normalize(MemoryArena * arena, Typer * env, Value * in0);
void introduceSignature(Typer * env, Arrow * signature, b32 add_bindings);
BuildTerm buildTerm(MemoryArena * arena, Typer * env, Ast * in0, Value * goal);
Term * buildFork(MemoryArena * arena, Typer * env, ForkAst * in, Term * goal);
Value * newRewrite(MemoryArena * arena, Value * eq_proof, Value * body, TreePath * path, b32 right_to_left);
FunctionDecl * parseFunction(MemoryArena * arena, Token * name, b32 is_theorem);
ForkAst * parseFork(MemoryArena * arena, b32 is_theorem);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);
BuildTerm parseExpressionFromString(MemoryArena * arena, char * string);

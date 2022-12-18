Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
Term * newComputation(MemoryArena * arena, Term * lhs, Term * rhs);
Term * getType(MemoryArena * arena, Environment * env, Term * in0);
Term * getType(Environment * env, Term * in0);
Term * getTypeNoEnv(Term * in0);
void dump(Trinary trinary);
void unwindStack(Environment * env);
void unwindBindingsAndStack(Environment * env);
void dump(Term * in0);
void dump(Ast * in0);
void checkStack(Stack * stack);
void debugIndent();
void debugDedent();
char * print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Ast * in0);
char * print(MemoryArena * buffer, Term * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Term * in0);
char * print(MemoryArena * buffer, void * in0, b32 is_absolute, PrintOptions opt);
void extendStack(Environment * env, i32 cap, Value ** items);
void addToStack(Environment * env, Value * value);
b32 equal(Environment * env, Term * lhs, Term * rhs);
Term * rebase(MemoryArena * arena, Term * in0, i32 delta, i32 offset);
Term * rebase(MemoryArena * arena, Term * in0, i32 delta);
Value * substitute(MemoryArena * arena, Term ** args, Term * in0, i32 offset);
Value * substitute(MemoryArena * arena, Term ** args, Term * in0);
CompareTerms compareTerms(MemoryArena * arena, Environment * env, Term * lhs0, Term * rhs0);
Trinary equalTrinary(Environment * env, Term * lhs0, Term * rhs0);
Value * normalize(MemoryArena * arena, Environment * env, Value * in0);
void introduceSignature(Environment * env, Arrow * signature, b32 add_bindings);
BuildExpression buildExpression(MemoryArena * arena, Environment * env, Ast * in0, Value * goal);
Term * buildFork(MemoryArena * arena, Environment * env, ForkAst * in, Term * goal);
void doubleCheckType(Value * in0);
Value * newRewrite(MemoryArena * arena, Value * eq_proof, Value * body, TreePath * path, b32 right_to_left);
FunctionDecl * parseFunction(MemoryArena * arena, Token * name, b32 is_theorem);
ForkAst * parseFork(MemoryArena * arena, b32 is_theorem);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);
BuildExpression parseExpressionFromString(MemoryArena * arena, char * string);

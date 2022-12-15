Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
void dump(Trinary trinary);
void dump(Term * in0);
void dump(Ast * in0);
void debugIndent();
void debugDedent();
char * print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Ast * in0);
char * print(MemoryArena * buffer, Term * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Term * in0);
char * print(MemoryArena * buffer, void * in0, b32 is_absolute, PrintOptions opt);
Value * evaluate(MemoryArena * arena, Environment * env, Term * in0, i32 offset);
Term * evaluate(MemoryArena * arena, Environment * env, Term * in0);
CompareTerms compareTerms(MemoryArena * arena, Term * lhs0, Term * rhs0);
Trinary equalTrinary(Term * lhs0, Term * rhs0);
Term * normalize(MemoryArena * arena, Environment * env, Term * in0);
Term * toPartiallyAbstractTerm(MemoryArena * arena, Environment * env, Term * in0);
Term * toAbstractTerm(MemoryArena * arena, Environment * env, Term * in0);
Term * evaluateAndNormalize(MemoryArena * arena, Environment * env, Term * in0, i32 offset);
void introduceOnStack(MemoryArena * arena, Environment * env, Token * name, Term * typev);
Term * buildFork(MemoryArena * arena, Environment * env, ForkAst * in, Term * goal);
void doubleCheckType(Value * in0);
BuildExpression buildExpression(MemoryArena * arena, Environment * env, Ast * in0, Term * goal);
FunctionDecl * parseFunction(MemoryArena * arena, Token * name, b32 is_theorem);
ForkAst * parseFork(MemoryArena * arena, b32 is_theorem);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);
BuildExpression parseExpressionFromString(MemoryArena * arena, char * string);

Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
char * print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Ast * in0);
char * print(MemoryArena * buffer, Term * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Term * in0);
char * print(MemoryArena * buffer, void * in0, b32 is_value, PrintOptions opt);
CompareValues compareValues(MemoryArena * arena, Term * lhs0, Term * rhs0);
Trinary equalTrinary(Term * lhs0, Term * rhs0);
Term * evaluateFork(MemoryArena * arena, Environment * env, Fork * fork);
Term * evaluateSequence(MemoryArena * arena, Environment * env, Sequence * sequence);
Term * normalize(MemoryArena * arena, Environment * env, Term * in0);
Term * evaluate(MemoryArena * arena, Environment * env, Ast * in0);
Term * evaluateAndNormalize(MemoryArena * arena, Environment * env, Ast * in0);
void introduceOnStack(MemoryArena * arena, Environment * env, Token * name, Term * typev);
void introduceOnStack(MemoryArena * arena, Environment * env, Token * name, Ast * type);
b32 buildSequence(MemoryArena * arena, Environment * env, Sequence * sequence, Term * goal);
void buildFork(MemoryArena * arena, Environment * env, Fork * fork, Term * expected_type);
BuildOutput buildExpression(MemoryArena * arena, Environment * env, Ast * in0, Term * goal);
FunctionDecl * parseFunction(MemoryArena * arena, Token * name, b32 is_theorem);
Fork * parseFork(MemoryArena * arena, b32 is_theorem);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);
BuildOutput parseExpressionFromString(MemoryArena * arena, char * string);

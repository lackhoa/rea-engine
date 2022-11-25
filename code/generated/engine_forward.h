Token nextToken(Tokenizer * tk);
Token peekToken(Tokenizer * tk);
char * print(MemoryArena * buffer, Ast * in0, PrintOptions opt);
char * print(MemoryArena * buffer, Value * in0, PrintOptions opt);
char * print(MemoryArena * buffer, void * in0, b32 is_value, PrintOptions opt);
Trinary equalTrinary(Value * lhs0, Value * rhs0);
Value * evaluateFork(MemoryArena * arena, Environment * env, Fork * fork, b32 should_normalize);
Value * evaluateSequence(MemoryArena * arena, Environment * env, Sequence * sequence, b32 should_normalize);
Value * normalize(MemoryArena * arena, Environment * env, Value * in0);
Value * evaluate(MemoryArena * arena, Environment * env, Ast * in0, b32 should_normalize);
Value * evaluate(MemoryArena * arena, Environment * env, Ast * in0);
void introduceOnStack(Environment * env, Token * name, Ast * type);
void buildSequence(MemoryArena * arena, Environment * env, Sequence * sequence, Value * goal);
void buildFork(MemoryArena * arena, Environment * env, Fork * fork, Value * expected_type);
Expression buildExpression(MemoryArena * arena, Environment * env, Ast * in0, Value * expected_type);
FunctionDecl * parseFunction(MemoryArena * arena, Token * name, b32 is_theorem);
Fork * parseFork(MemoryArena * arena, b32 is_theorem);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);

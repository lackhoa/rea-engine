char * printAst(MemoryArena * buffer, void * in_void, PrintOptions opt);
Value * normalize(Environment env, Value * in0);
Value * evaluate(Environment env, Ast * in0);
void introduceOnStack(Environment * env, Token * name, Ast * type);
Expression buildExpression(Environment * env, Ast * in0, Value * expected_type);
Function * parseFunction(MemoryArena * arena, Token * name);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);

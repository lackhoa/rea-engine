char * printAst(MemoryArena * buffer, void * in_void, PrintOptions opt);
Value * normalize(Environment env, Value * in0);
Value * evaluate(Environment env, Ast * in0);
b32 introduce(Environment * env, s32 count, Token * names, Ast ** types, IntroduceOptions opt);
Expression buildExpression(Environment * env, Ast * in0, Value * expected_type);
Function * parseFunction(MemoryArena * arena, Token * name);
Ast * parseExpressionToAst(MemoryArena * arena);
b32 interpretFile(EngineState * state, FilePath input_path, b32 is_root_file);

#define embed_FunctionDecl(name) union { FunctionDecl name; struct { Ast a; Sequence * body; ArrowA * signature;  }; };
#define embed_Value(name) union { Value name; struct { ValueCategory cat; Value * type;  }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token;  }; };

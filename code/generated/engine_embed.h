#define embed_Ast(name) union { Ast name; struct { AstKind kind; Token token; u32 flags;  }; };

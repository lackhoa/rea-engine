#define embed_Ast(name) union { Ast name; struct { AstKind cat; Token token; u32 flags;  }; };

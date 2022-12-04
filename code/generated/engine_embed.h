#define embed_Term(name) union { Term name; struct { TermCategory cat; Term * type;  }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token;  }; };

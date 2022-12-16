#define embed_Term(name) union { Term name; struct { TermCategory cat; Value * type; Anchor * anchor;  }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token;  }; };

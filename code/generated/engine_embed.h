#define embed_Term(name) union { Term name; struct { TermCategory cat; Term * type; Token * global_name; i32 serial; }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token; u32 flags;  }; };

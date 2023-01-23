#define embed_Term(name) union { Term name; struct { TermCategory cat; i32 serial; Term * type; Token * global_name;  }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token; u32 flags;  }; };

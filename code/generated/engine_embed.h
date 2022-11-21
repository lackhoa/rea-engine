#define embed_Arrow(name) union { Arrow name; struct { union {Ast a; struct {AstCategory cat; Token token; }; }; Ast * out_type; s32 param_count; Token * param_names; Ast ** param_types;  }; };
#define embed_FunctionDecl(name) union { FunctionDecl name; struct { Ast a; Sequence * body; Arrow * signature;  }; };
#define embed_Value(name) union { Value name; struct { ValueCategory cat; Value * type;  }; };
#define embed_Ast(name) union { Ast name; struct { AstCategory cat; Token token;  }; };

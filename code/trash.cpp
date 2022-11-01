#if 0
      if (!subject_matched)
      {
        Fork *out = copyStruct(env.arena, in);
        out0 = out;
        out->subject = norm_subject;
        allocateArray(env.arena, out->case_count, out->cases);
        Environment *outer_env = &env;
        for (s32 case_id = 0; case_id < out->case_count; case_id++)
        {
          Environment env = *outer_env;
          Form *ctor = in->form->ctors + case_id;
          switch (ctor->type->cat)
          {
            case AC_Form:
            {
              extendStack(&env, 0, 0);
            } break;

            case AC_ArrowType:
            {
              introduceVariables(&env,
                                 castAst(ctor->type, ArrowType)->param_count,
                                 in->cases[case_id].params);
            } break;

            invalidDefaultCase;
          }
          out->cases[case_id]      = in->cases[case_id];
          out->cases[case_id].body = normalize(env, in->cases[case_id].body);
        }
      }
#endif

enum ValueCategory
{
  VC_ParameterV,
  VC_StackValue,
  VC_ApplicationV,
  VC_FormV,
  VC_FunctionV,
  VC_ArrowTypeV,
};

struct Value
{
  ValueCategory cat;
};

struct StackValue
{
  Value h;

  String name;
  s32    stack_depth;
};

struct ParameterV
{
  Value h;

  String name;
  Value *type;
};

struct ApplicationV
{
  Value h;

  Value  *op;
  s32     arg_count;
  Value **args;
};

struct FormV
{
  Value h;

  Token  name;
  Value *type;

  s32 ctor_id;

  s32   ctor_count;
  Form *ctors;
};

struct FunctionV
{
  Value h;
  Token name;
  Ast *body;
};

struct ArrowTypeV
{
  Value        h;

  s32          param_count;
  Variable   **params;
  Ast  *return_type;
};


#include "utils.h"
#include "engine.h"
#include "tokenization.h"
#include "rea_globals.h"

struct PrintOptions{b32 detailed; b32 print_type;};

internal char*
printValue(MemoryArena *buffer, Value *in0, PrintOptions opt);

internal char*
printAst(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{
  char *out = buffer ? (char*)getArenaNext(buffer) : 0;
  if (in0 == &dummy_hole)
  {
    printToBuffer(buffer, "_");
  }
  else if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
      case AC_Constant:
      {
        Constant *in = castAst(in0, Constant);
        printToBuffer(buffer, in->a.token);
      } break;

      case AC_Variable:
      {
        Variable *in = castAst(in0, Variable);
#if 0
        printToBuffer(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
#else
        printToBuffer(buffer, in->a.token);
#endif
      } break;

      case AC_Sequence:
      {
        Sequence *in = castAst(in0, Sequence);
        for (s32 id = 0; id < in->count; id++)
        {
          printAst(buffer, in->items[id], new_opt);
          if (id < in->count-1)
            printToBuffer(buffer, "; ");
        }
      } break;

      case AC_Rewrite:
      {
        Rewrite *in = castAst(in0, Rewrite);
        printToBuffer(buffer, "rewrite ");
        printAst(buffer, in->proof, new_opt);
      } break;

      case AC_Composite:
      {
        Composite *in = castAst(in0, Composite);

        printAst(buffer, in->op, new_opt);

        printToBuffer(buffer, "(");
        for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
        {
          printAst(buffer, in->args[arg_id], new_opt);
          if (arg_id < in->arg_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ")");

      } break;

      case AC_Fork:
      {
        Fork *in = castAst(in0, Fork);
        printToBuffer(buffer, "fork ");
        printAst(buffer, in->subject, new_opt);
        printToBuffer(buffer, " {");
        Form *form = in->form;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          ForkParameters *casev = in->params + ctor_id;
          Form *ctor = form->ctors + ctor_id;
          switch (ctor->v.type->cat)
          {// print pattern
            case AC_Form:
            {
              printValue(buffer, &ctor->v, new_opt);
            } break;

            case AC_ArrowV:
            case AC_Arrow:
            {
              printValue(buffer, &ctor->v, new_opt);
              printToBuffer(buffer, " ");
              ArrowV *signature = castValue(ctor->v.type, ArrowV);
              for (s32 param_id = 0; param_id < signature->a->param_count; param_id++)
              {
                printToBuffer(buffer, casev->names[param_id]);
                printToBuffer(buffer, " ");
              }
            } break;

            invalidDefaultCase;
          }

          printToBuffer(buffer, ": ");
          printAst(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != form->ctor_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, "}");
      } break;

      case AC_Arrow:
      {
        Arrow *in = castAst(in0, Arrow);
        printToBuffer(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          printToBuffer(buffer, in->param_names[param_id]);
          printToBuffer(buffer, ": ");
          printAst(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ") -> ");

        printAst(buffer, in->out_type, new_opt);
      } break;

      default:
      {
        printToBuffer(buffer, "<unimplemented category: %u>", in0->cat);
      } break;
    }
  }
  else
    printToBuffer(buffer, "<null>");
  return out;
}

internal char*
printValue(MemoryArena *buffer, Value *in0, PrintOptions opt)
{
  char *out = buffer ? (char*)getArenaNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    new_opt.detailed = false;

    switch (in0->cat)
    {
      case AC_StackRef:
      {
        StackRef *in = castAst(in0, StackRef);
#if 1
        printToBuffer(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
#else
        printToBuffer(buffer, in->name);
#endif
      } break;

      case AC_CompositeV:
      {
        CompositeV *in = castAst(in0, CompositeV);

        printValue(buffer, in->op, new_opt);

        printToBuffer(buffer, "(");
        for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
        {
          printValue(buffer, in->args[arg_id], new_opt);
          if (arg_id < in->arg_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ")");

      } break;

      case AC_Form:
      {
        Form *in = castAst(in0, Form);
        if (opt.detailed && in != builtins.Type)
        {
          printToBuffer(buffer, in->token);

          if (opt.print_type)
          {
            printToBuffer(buffer, ": ");
            printValue(buffer, in->v.type, new_opt);
          }

          if (in->ctor_count)
          {
            printToBuffer(buffer, " {");
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Form *ctor = in->ctors + ctor_id;
              printToBuffer(buffer, ctor->token);
              printToBuffer(buffer, ": ");
              printValue(buffer, ctor->v.type, new_opt);
            }
            printToBuffer(buffer, " }");
          }
        }
        else
          printToBuffer(buffer, in->token);
      } break;

      case AC_FunctionV:
      {
        FunctionV *in = castAst(in0, FunctionV);
        printToBuffer(buffer, in->token);
        if (opt.detailed)
        {
          printToBuffer(buffer, " { ");
          printAst(buffer, in->a->body, new_opt);
          printToBuffer(buffer, " }");
        }
      } break;

      case AC_ArrowV:
      {
        ArrowV *in = castAst(in0, ArrowV);
        printAst(buffer, &in->a->a, opt);
      } break;

      default:
      {
        printToBuffer(buffer, "<unimplemented category: %u>", in0->cat);
      } break;
    }
  }
  else
    printToBuffer(buffer, "<null>");
  return out;
}

inline void
myprint()
{
  printToBuffer(0, "\n");
}

inline void
myprint(Ast *in0)
{
  printAst(0, in0, {});
}

inline void
myprint(Value *in0)
{
  printValue(0, in0, {});
}

inline void
myprint(int d)
{
  printf("%d", d);
}

inline void
myprint(char *c)
{
  printf("%s", c);
}

#include "utils.h"
#include "engine.h"
#include "tokenization.h"
#include "rea_builtins.h"

struct PrintOptions{b32 detailed; b32 print_type;};

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
      case AC_StackRef:
      {
        StackRef *in = castAst(in0, StackRef);
#if 0
        printToBuffer(buffer, "%.*s<%d>", in->name.length, in->name.chars, in->stack_depth);
#else
        printToBuffer(buffer, in->name);
#endif
      } break;
      case AC_Constant:
      {
        Constant *in = castAst(in0, Constant);
        printToBuffer(buffer, in->h.token);
      } break;

      case AC_Variable:
      {
        Variable *in = castAst(in0, Variable);
#if 0
        printToBuffer(buffer, "%.*s[%d]", in->name.length, in->name.chars, in->stack_delta);
#else
        printToBuffer(buffer, in->h.token);
#endif

        if (opt.detailed || opt.print_type)
        {
          printToBuffer(buffer, ": ");
          printAst(buffer, in->type, new_opt);
        }
      } break;

      case AC_Composite:
      case AC_CompositeV:
      {
        Composite *in = polyAst(in0, Composite, CompositeV);

        if (in->op == &dummy_sequence)
        {
          for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
          {
            printAst(buffer, in->args[arg_id], new_opt);
            if (arg_id < in->arg_count-1)
              printToBuffer(buffer, "; ");
          }
        }
        else if (in->op == &dummy_rewrite)
        {
          printToBuffer(buffer, "rewrite ");
          if (in->arg_count == 1)
          {
            printAst(buffer, in->args[0], new_opt);
          }
          else if (in->arg_count == 2)
          {
            printAst(buffer, in->args[0], new_opt);
            printToBuffer(buffer, " => ");
            printAst(buffer, in->args[1], new_opt);
          }
        }
        else
        {
          printAst(buffer, in->op, new_opt);

          printToBuffer(buffer, "(");
          for (s32 arg_id = 0; arg_id < in->arg_count; arg_id++)
          {
            printAst(buffer, in->args[arg_id], new_opt);
            if (arg_id < in->arg_count-1)
              printToBuffer(buffer, ", ");
          }
          printToBuffer(buffer, ")");
        }
      } break;

      case AC_Fork:
      {
        Fork *fork = castAst(in0, Fork);
        printToBuffer(buffer, "fork ");
        printAst(buffer, fork->subject, new_opt);
        printToBuffer(buffer, " {");
        Form *form = fork->form;
        for (s32 ctor_id = 0;
             ctor_id < form->ctor_count;
             ctor_id++)
        {
          ForkCase *casev = fork->cases + ctor_id;
          Form *ctor = form->ctors + ctor_id;
          switch (ctor->v.type->cat)
          {// print pattern
            case AC_Form:
            {
              printAst(buffer, &ctor->v.a, new_opt);
            } break;

            case AC_ArrowV:
            case AC_Arrow:
            {
              printAst(buffer, &ctor->v.a, new_opt);
              printToBuffer(buffer, " ");
              Arrow *signature = polyAst(ctor->v.type, Arrow, ArrowV);
              for (s32 param_id = 0; param_id < signature->param_count; param_id++)
              {
                printToBuffer(buffer, casev->params[param_id]->h.token);
                printToBuffer(buffer, " ");
              }
            } break;

            invalidDefaultCase;
          }

          printToBuffer(buffer, ": ");
          printAst(buffer, casev->body, new_opt);
          if (ctor_id != form->ctor_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, "}");
      } break;

      case AC_Form:
      {
        Form *in = castAst(in0, Form);
        if (opt.detailed && in != builtin_Type)
        {
          printToBuffer(buffer, in0->token);

          if (opt.print_type)
          {
            printToBuffer(buffer, ": ");
            printAst(buffer, in->v.type, new_opt);
          }

          if (in->ctor_count)
          {
            printToBuffer(buffer, " {");
            for (s32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              Form *ctor = in->ctors + ctor_id;
              printToBuffer(buffer, ctor->v.a.token);
              printToBuffer(buffer, ": ");
              printAst(buffer, ctor->v.type, new_opt);
            }
            printToBuffer(buffer, " }");
          }
        }
        else
          printToBuffer(buffer, in0->token);
      } break;

      case AC_FunctionV:
      case AC_Function:
      {
        Function *in = polyAst(in0, Function, FunctionV);
        printToBuffer(buffer, in0->token);
        if (opt.detailed)
        {
          printToBuffer(buffer, " { ");
          printAst(buffer, in->body, new_opt);
          printToBuffer(buffer, " }");
        }
      } break;

      case AC_ArrowV:
      case AC_Arrow:
      {
        Arrow *arrow = polyAst(in0, Arrow, ArrowV);
        printToBuffer(buffer, "(");
        for (int param_id = 0;
             param_id < arrow->param_count;
             param_id++)
        {
          Parameter *param = arrow->params[param_id];
          printToBuffer(buffer, param->h.token);
          printToBuffer(buffer, ": ");
          printAst(buffer, param->type, new_opt);
          if (param_id < arrow->param_count-1)
            printToBuffer(buffer, ", ");
        }
        printToBuffer(buffer, ") -> ");

        printAst(buffer, arrow->return_type, new_opt);
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
myprint(int d)
{
  printf("%d", d);
}

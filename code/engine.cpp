#include "utils.h"
#include "memory.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"

// NOTE: Eventually this will talk to the editor, but let's work in console mode for now.
// Important: all parsing must be aborted when the tokenizer encounters error.

// NOTE: Think of this like the function stack, we'll clean it every once in a while.
global_variable MemoryArena  global_temp_arena_;
global_variable MemoryArena *global_temp_arena = &global_temp_arena_;

#define unpackGlobals                           \
    Tokenizer   *tk         = global_tokenizer; \
    MemoryArena *temp_arena = global_temp_arena; \
    (void) tk;                                  \
    (void) temp_arena;                          \

enum ExpressionCategory
{
    EC_Unknown,
    EC_Variable,                // reference to some unknown on "the stack"
    EC_Application,             // operator application
    EC_Switch,                  // switch statement
    EC_Struct,                  // struct information
    EC_Procedure,               // holds actual computation (ie body that can be executed)
    EC_ArrowType,               // type of procedure and built-in objects
    EC_ConstructorRef,          // reference to a constructor of a type

    EC_Builtin_identical,
    EC_Builtin_Set,
    EC_Builtin_Prop,
    EC_Builtin_Proc,
    EC_Builtin_Type,
};

#define castExpression(Type, exp) (exp->cat == EC_##Type) ? &exp->Type : 0;

struct Expression;

struct Variable
{
    String name;
    s32    stack_delta;
    u32    id;
};

struct Application
{
    Expression *op;
    s32        arg_count;
    Expression **args;
};

struct Switch
{
    Expression *subject;
    Expression **case_bodies;
};

struct Constructor;
struct Struct
{
    String       name;
    s32          ctor_count;
    Constructor *ctors;
    s32          parameter_count;
    Expression  *parameters;
};

// like procedures, but we don't allow arbitrary expressions in here (maybe we
// need to).
struct Constructor
{
    String  name;
};

// NOTE: we need the id to arrange the switch body. otw it's just a pointer.
struct ConstructorRef
{
    u32 id;
};

// NOTE: most of the information is in the (arrow) type;
struct Procedure
{
    String       name;
    Expression  *body;
};

struct ArrowType
{
    s32          arg_count;
    Expression **args;
    Expression  *return_type;
};

struct Expression
{
    ExpressionCategory  cat;
    Expression         *type;  // IMPORTANT: always in normal form
    union
    {
        Variable       Variable;
        Application    Application;
        Switch         Switch;
        Struct         Struct;
        Procedure      Procedure;
        ArrowType      ArrowType;
        ConstructorRef ConstructorRef;
    };
};

global_variable Expression builtin_identical;
global_variable Expression *builtin_True;
global_variable Expression *builtin_truth;
global_variable Expression *builtin_False;
global_variable Expression builtin_Set;
global_variable Expression builtin_Prop;
global_variable Expression builtin_Proc;
global_variable Expression builtin_Type;

internal void
printConstructor(MemoryArena *buffer, Constructor *ctor)
{
    myprint(buffer, ctor->name);
}

inline s32
switchCtorCount(Switch *myswitch)
{
    return myswitch->subject->type->Struct.ctor_count;
}

internal void
printExpression(MemoryArena *buffer, Expression *exp, b32 detailed = false)
{
    switch (exp->cat)
    {
        case EC_Variable:
        {
            auto var = castExpression(Variable, exp);
            myprint(buffer, "%.*s", var->name.length, var->name.chars);
            if (detailed)
            {
                myprint(buffer, " : ");
                printExpression(buffer, exp->type);
            }
        } break;

        case EC_Application:
        {
            auto app = &exp->Application;

            printExpression(buffer, app->op);

            myprint(buffer, "(");
            for (s32 arg_id = 0; arg_id < app->arg_count; arg_id++)
            {
                printExpression(buffer, app->args[arg_id]);
                if (arg_id < app->arg_count-1)
                    myprint(buffer, ", ");
            }
            myprint(buffer, ")");
        } break;

        case EC_Switch:
        {
            auto myswitch = &exp->Switch;
            myprint(buffer, "switch ");
            printExpression(buffer, myswitch->subject);
            myprint(buffer, " {");
            auto subject_struct = castExpression(Struct, myswitch->subject->type);
            for (s32 ctor_id = 0;
                 ctor_id < subject_struct->ctor_count;
                 ctor_id++)
            {
                printConstructor(buffer, subject_struct->ctors + ctor_id);
                myprint(buffer, " -> ");
                printExpression(buffer, myswitch->case_bodies[ctor_id]);
                if (ctor_id != subject_struct->ctor_count-1)
                    myprint(buffer, ", ");
            }
            myprint(buffer, "}");
        } break;

        case EC_Struct:
        {
            auto mystruct = &exp->Struct;
            myprint(buffer, mystruct->name);
        } break;

        case EC_Procedure:
        {
            auto proc = castExpression(Procedure, exp);
            auto signature = castExpression(ArrowType, exp->type);
            myprint(buffer, proc->name);
            if (detailed)
            {
                myprint(buffer, "(");
                for (int arg_id = 0;
                     arg_id < signature->arg_count;
                     arg_id++)
                {
                    auto arg = signature->args[arg_id];
                    printExpression(buffer, arg);
                    myprint(buffer, ": ");
                    printExpression(buffer, arg->type);
                    if (arg_id < signature->arg_count-1)
                        myprint(buffer, ", ");
                }
                myprint(buffer, ") => ");

                printExpression(buffer, proc->body);
                myprint(buffer, " : ");

                printExpression(buffer, signature->return_type);
            }
        } break;

        case EC_ConstructorRef:
        {
            auto type = castExpression(Struct, exp->type);
            Constructor *ctor = type->ctors + exp->ConstructorRef.id;
            myprint(buffer, ctor->name);
        } break;

        case EC_ArrowType:
        {
            auto arrow = castExpression(ArrowType, exp);
            myprint(buffer, "(");
            for (int arg_id = 0;
                 arg_id < arrow->arg_count;
                 arg_id++)
            {
                printExpression(buffer, arrow->args[arg_id], true);
                if (arg_id < arrow->arg_count-1)
                        myprint(buffer, ", ");
            }
            myprint(buffer, ") -> ");

            printExpression(buffer, arrow->return_type);
        } break;

        case EC_Builtin_identical:
        {
            myprint(buffer, "identical");
        } break;

        case EC_Builtin_Set:
        {
            myprint(buffer, "Set");
        } break;

        case EC_Builtin_Proc:
        {
            myprint(buffer, "Proc");
        } break;

        case EC_Builtin_Prop:
        {
            myprint(buffer, "Prop");
        } break;

        case EC_Builtin_Type:
        {
            myprint(buffer, "Type");
        } break;

        default:
        {
            myprint(buffer, "<unimplemented category: %u>", exp->cat);
        } break;
    }
}

inline Expression *
newExpression(MemoryArena *arena, ExpressionCategory cat, Expression *type)
{
    auto out = pushStruct(arena, Expression);
    out->cat  = cat;
    out->type = type;
    return out;
}

struct Macro {};

enum AstCategory { AstCat_Expression, AstCat_Macro, };

struct Ast
{
    AstCategory  cat;
    void        *p;  // pointer to either a macro or an expression
};

inline Ast
expressionAst(Expression *exp)
{
    return Ast{AstCat_Expression, exp};
}

#define castAst(Type, ast) (ast.cat == AstCat_##Type) ? (Type *)ast.p : 0;

struct Binding
{
    String   key;
    Ast      value;
    Binding *next;
};

struct Bindings
{
    MemoryArena *arena;
    Binding      first[128];
    Bindings    *next;
};

global_variable Bindings *global_bindings;

struct Stack
{
    MemoryArena  *arena;
    s32           count;
    Expression  **first;
    Stack        *next;
};

internal Stack
extendStack(Stack *outer, u32 arg_count, Expression **args)
{    
    Stack out = {};

    out.arena = outer->arena;
    out.count = arg_count;
    out.first = args;
    out.next  = outer;

    return out;
}

inline Bindings *
extendBindings(MemoryArena *arena, Bindings *outer)
{
    Bindings *out = pushStruct(arena, Bindings);
    for (int i = 0; i < arrayCount(out->first); i++)
    {// invalidate these slots
        Binding *slot = &out->first[i];
        slot->key.length = 0;
    }
    out->next        = outer;
    out->arena       = arena;
    return out;
}

struct LookupName { Binding* slot; b32 found; };

internal LookupName
lookupNameCurrentFrame(Bindings *bindings, String key, b32 add_if_missing = false)
{
    Binding *slot = 0;
    b32 found = false;
    u32 hash = stringHash(key);
    slot = bindings->first + (hash % arrayCount(bindings->first));
    b32 first_slot_valid = slot->key.length;
    if (first_slot_valid)
    {
        b32 stop = false;
        while (!stop)
        {
            if (equals(slot->key, key))
            {
                stop = true;
                found = true;
            }
            else if (slot->next)
                slot = slot->next;
            else
            {
                stop = true;
                if (add_if_missing)
                {
                    allocate(bindings->arena, slot->next);
                    slot = slot->next;
                    slot->key  = key;
                    slot->next = 0;
                }
            }
        }
    }
    else if (add_if_missing)
    {
        slot->key = key;
        slot->value = {};
    }

    LookupName out = { slot, found };
    return out;
}

inline void
addBuiltinName(char *key, Expression *value)
{
    auto lookup = lookupNameCurrentFrame(global_bindings, toString(key), true);
    lookup.slot->value = {AstCat_Expression, value};
}

inline void
addBuiltinMacro(char *key)
{
    auto lookup = lookupNameCurrentFrame(global_bindings, toString(key), true);
    lookup.slot->value = {AstCat_Macro, (void*)0};
}

struct LookupNameRecursive { Ast value; b32 found; };

inline LookupNameRecursive
lookupNameRecursive(Bindings *bindings, Token *token)
{
    Ast value = {};
    b32 found = false;

    for (b32 stop = false;
         !stop;
         )
    {
        LookupName lookup = lookupNameCurrentFrame(bindings, token->text, false);
        if (lookup.found)
        {
            found = true;
            stop = true;
            value = lookup.slot->value;
        }
        else
        {
            if (bindings->next)
                bindings = bindings->next;
            else
                stop = true;
        }
    }

    LookupNameRecursive out = { value, found };
    return out;
}

internal Constructor
parseConstructorDef(MemoryArena *arena, Expression *mystruct, s32 ctor_id)
{
    unpackGlobals;
    Constructor out = {};
    Token ctor_token = advance(tk);
    switch (ctor_token.cat)
    {
        case TC_Special:
        case TC_Alphanumeric:
        {
            LookupName ctor_lookup = lookupNameCurrentFrame(global_bindings, ctor_token.text, true);
            if (ctor_lookup.found)
            {
                todoErrorReport;
            }
            else
            {
                out.name = ctor_token.text;

                auto exp = newExpression(arena, EC_ConstructorRef, mystruct);
                auto ctor_ref = &exp->ConstructorRef;
                ctor_ref->id  = ctor_id;

                ctor_lookup.slot->value = expressionAst(exp);
            }
        } break;

        default:
        {
            todoErrorReport;
        }
    }
    return out;
}

internal void
parseErrorVA(Token *token, char *format, va_list arg_list, Tokenizer *tk = global_tokenizer)
{
#if 0
    assert(!tk->error);  // note: prevent parser from doing huge amount of
                         // useless work after failure (#speed).
#endif
    auto arena = tk->error_arena;
    tk->error = pushStructZero(arena, ParseErrorData);
    tk->error->message = subArena(tk->error_arena, 256);

    printToBufferVA(&tk->error->message, format, arg_list);

    tk->error->token = *token;
    tk->error->context = tk->context->first;
}

internal void
parseError(Token *token, char *format, ...)
{
    va_list arg_list;
    __crt_va_start(arg_list, format);
    parseErrorVA(token, format, arg_list);
    __crt_va_end(arg_list);
}

internal void
tokenError(Token *token, char *message, Tokenizer *tk = global_tokenizer)
{
    parseError(token, message, tk);
    myprint(&tk->error->message, ": ");
    myprint(&tk->error->message, token->text);
}

internal void
tokenError(char *message, Tokenizer *tk = global_tokenizer)
{
    tokenError(&tk->last_token, message);
}

inline b32
requireChar(Tokenizer *tk, char c)
{
    auto out = false;
    if (parsing(tk))
    {
        Token token = advance(tk);
        if (token.text.length == 1 && token.text.chars[0] == c)
            out = true;
        else
            parseError(&token, "expected character %c", c);
    }
    return out;
}

inline b32
requireChar(char c)
{
    return requireChar(global_tokenizer, c);
}

inline b32
optionalChar(Tokenizer *tk, char c)
{
    b32 out = false;
    Token token = peekNext(tk);
    if (equals(&token, c))
    {
        out = true;
        advance(tk);
    }
    return out;
}

inline b32
optionalChar(char c)
{
    return optionalChar(global_tokenizer, c);
}

internal b32
addGlobalNameBinding(String key, Expression *value)
{
    b32 succeed = false;
    LookupName lookup = lookupNameCurrentFrame(global_bindings, key, true);
    if (!lookup.found)
    {
        succeed = true;
        lookup.slot->value = expressionAst(value);
    }
    return succeed;
}

internal void
addBuiltinStruct(MemoryArena *arena, char *name, const char **ctor_names, s32 ctor_count)
{
    auto *struct_exp = newExpression(arena, EC_Struct, &builtin_Set);
    auto struct_name = toString(name);
    assert(addGlobalNameBinding(struct_name, struct_exp));

    Struct *mystruct = &struct_exp->Struct;
    mystruct->name = struct_name;
    mystruct->ctor_count = ctor_count;
    allocateArray(arena, mystruct->ctor_count, mystruct->ctors);

    for (auto ctor_id = 0; ctor_id < ctor_count; ctor_id++)
    {
        auto ctor = mystruct->ctors + ctor_id;
        ctor->name = toString(ctor_names[ctor_id]);
        auto ctor_exp = newExpression(arena, EC_ConstructorRef, struct_exp);
        ctor_exp->ConstructorRef.id = ctor_id;
        assert(addGlobalNameBinding(ctor->name, ctor_exp));
    }
}

internal void
parseTypedef(MemoryArena *arena)
{
    unpackGlobals;
    Token type_name = advance(tk);
    if (type_name.cat == TC_Alphanumeric)
    {
        // NOTE: the type is in scope of its own constructor.
        LookupName lookup = lookupNameCurrentFrame(global_bindings, type_name.text, true);
        if (lookup.found)
            tokenError("redefinition of type");
        else
        {
            auto *struct_exp = newExpression(arena, EC_Struct, &builtin_Set);
            lookup.slot->value = expressionAst(struct_exp);

            Struct *mystruct = &struct_exp->Struct;
            mystruct->name = type_name.text;

            requireChar(tk, '{');

            s32 expected_case_count = 0;
            {// peek ahead to get the case count. this code can be crappy since
             // the real error checking is done later.
                Tokenizer tk1 = *tk;
                s32 nesting_depth = 0;
                for (b32 stop = false; !stop;)
                {
                    Token token = advance(&tk1);
                    if (token.cat == TC_PairingOpen)
                        nesting_depth++;
                    else if (token.cat == TC_PairingClose)
                    {
                        if (nesting_depth > 0)
                            nesting_depth--;
                        else
                            stop = true;
                    }
                    else if ((nesting_depth == 0) && (equals(&token, '|')))
                    {
                        expected_case_count++;
                    }
                }
            }

            allocateArray(arena, expected_case_count, mystruct->ctors);

            s32 actual_case_count = 0;
            for (s32 stop = 0, constructor_id = 0; !stop; constructor_id++)
            {
                Token bar_or_stop = advance(tk);
                if (equals(&bar_or_stop, '}'))
                    stop = true;
                else if (equals(&bar_or_stop, '|'))
                {
                    mystruct->ctors[constructor_id] = parseConstructorDef(arena, struct_exp, constructor_id);
                    actual_case_count++;
                }
                else
                    parseError(&bar_or_stop, "Expected '|' or '}'");
            }
            assert(actual_case_count == expected_case_count);
            mystruct->ctor_count = actual_case_count;

            assert(lookupNameCurrentFrame(global_bindings, type_name.text).found);
        }
    }
}

struct OptionalU32 { b32 success; u32 value; };

inline b32
equals(Variable atom1, Variable atom2)
{
    return ((atom1.id == atom2.id)
            && (atom1.stack_delta == atom2.stack_delta));
}

internal Expression *
resolve(Stack *stack, Variable variable)
{
    for (s32 i = 0; i < variable.stack_delta; i++)
        stack = stack->next;
    assert(variable.id < stack->count);
    Expression *out = stack->first[variable.id];
    return out;
}

// NOTE: input expression must be normalized first
internal OptionalU32
matchSwitchCase(Expression *matched)
{
    OptionalU32 out = {};

    if (matched)
    {
        if (matched->cat == EC_Variable)
        {}  // surrender
        else if (matched->cat == EC_ConstructorRef)
        {
            auto ctor   = matched->ConstructorRef;
            out.success = true;
            out.value   = ctor.id;
        }
        else if (matched->cat == EC_Application)
        {
            auto app = castExpression(Application, matched);
            auto ctor = castExpression(ConstructorRef, app->op);
            if (ctor)
            {
                out.success = true;
                out.value = ctor->id;
            }
        }
    }
    
    return out;
}

enum Trinary
{
    Trinary_Unknown, Trinary_False, Trinary_True,
};

// NOTE: we need a trinary return value because it will detect if the comparison
// is false.
internal Trinary
compareExpressions(Expression *lhs, Expression *rhs)
{
    Trinary out = Trinary_Unknown;

    if (lhs == rhs)
        out = Trinary_True;
    else if (lhs->cat == rhs->cat)
    {
        switch (lhs->cat)
        {
            case EC_Variable:
            {
                if ((lhs->Variable.stack_delta == rhs->Variable.stack_delta)
                    && (lhs->Variable.id == rhs->Variable.id))
                {
                    out = Trinary_True;
                }
            } break;

            case EC_ConstructorRef:
            {
                if (lhs->ConstructorRef.id == rhs->ConstructorRef.id)
                    out = Trinary_True;
                else
                    out = Trinary_False;
            } break;

            case EC_ArrowType:
            {
                auto arg_count = lhs->ArrowType.arg_count;
                if (rhs->ArrowType.arg_count == arg_count)
                {
                    b32 mismatch_found = false;
                    b32 unknown_found = false;
                    for (auto arg_id = 0;
                         (arg_id < arg_count) && (!mismatch_found) && (!unknown_found);
                         arg_id++)
                    {
                        auto lhs_arg = lhs->ArrowType.args[arg_id];
                        auto rhs_arg = rhs->ArrowType.args[arg_id];
                        auto compare = compareExpressions(lhs_arg->type, rhs_arg->type);
                        if (compare == Trinary_Unknown)
                        {
                            unknown_found = true;
                        }
                        if (compare == Trinary_False)
                        {
                            mismatch_found = true;
                        }
                    }
                    if (mismatch_found)
                        out = Trinary_False;
                    else if (unknown_found)
                        out = Trinary_Unknown;   
                    else
                        out = Trinary_True;
                }
            } break;

            case EC_Switch:
            {
                b32 unknown_found = false;
                b32 false_found   = false;
                auto lhs_switch = castExpression(Switch, lhs);
                auto rhs_switch = castExpression(Switch, rhs);
                auto ctor_count = switchCtorCount(lhs_switch);
                for (int ctor_id = 0, stop = false;
                     ctor_id < ctor_count && !stop;
                     ctor_id++)
                {
                    auto compare = compareExpressions(lhs_switch->case_bodies[ctor_id],
                                                      rhs_switch->case_bodies[ctor_id]);
                    if (compare == Trinary_Unknown)
                    {
                        unknown_found = true;
                    }
                    else if (compare == Trinary_False)
                    {
                        stop = true;
                        false_found = true;
                    }
                }
                if (false_found)
                    out = Trinary_False;
                else if (unknown_found)
                    out = Trinary_Unknown;
                else
                    out = Trinary_True;
            } break;

            default:
                todoIncomplete;
        }
    }

    return out;
}

internal b32
expressionsIdenticalB32(Expression *lhs, Expression *rhs)
{
    return (compareExpressions(lhs, rhs) == Trinary_True);
}

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
    // IMPORTANT: I really don't want "." to be a special thing, I want to use it in expresions
    if (token->cat == TC_Arrow)
        return true;
    else if (inString("{},);:", token))
        return true;
    else
        return false;
}

inline s32
precedenceOf(Ast op)
{
    int out = 0;
    switch (op.cat)
    {
        case AstCat_Expression:
        {
            // TODO: implement for real
            auto exp = (Expression *)op.p;
            if (exp->cat == EC_Procedure)
            {
                if (equals(exp->Procedure.name, "&"))
                    out = 20;
                else if (equals(exp->Procedure.name, "|"))
                    out = 10;
                else
                    out = 100;
            }
            else if (exp->cat == EC_ConstructorRef)
                out = 100;
            else
                invalidCodePath;
        } break;

        case AstCat_Macro:
        {
            // also implement for real
            out = 0;
        } break;
    }

    return out;
}

internal Expression *
parseOperand(MemoryArena *arena, Bindings *bindings);

internal Expression *
getArgType(Expression *op, s32 arg_id)
{
    auto signature = castExpression(ArrowType, op->type);
    assert(arg_id < signature->arg_count);
    return signature->args[arg_id]->type;
}

inline Expression *
makeBinopExpression(MemoryArena *arena, Expression *op, Expression *lhs, Expression *rhs)
{
    auto signature = castExpression(ArrowType, op->type);
    Expression *out = newExpression(arena, EC_Application, signature->return_type);

    out->Application.op        = op;
    out->Application.arg_count = 2;
    allocateArray(arena, 2, out->Application.args);
    out->Application.args[0] = lhs;
    out->Application.args[1] = rhs;
    return out;
}

internal Expression *
normalize(MemoryArena *arena, Stack *stack, Expression *in)
{
    Expression *out = 0;
    unpackGlobals;

    switch (in->cat)
    {
        case EC_Variable:
        {
            out = resolve(stack, in->Variable);
            if (!out)
                out = in;
        } break;

        case EC_Application:
        {
            auto in_app = &in->Application;
            Expression **reduced_args = pushArray(temp_arena, in_app->arg_count, Expression*);
            for (auto arg_id = 0;
                 arg_id < in_app->arg_count;
                 arg_id++)
            {
                Expression *in_arg   = in_app->args[arg_id];
                reduced_args[arg_id] = normalize(arena, stack, in_arg);
            }

            Expression *reduced_op = normalize(arena, stack, in_app->op);
            if (reduced_op->cat == EC_Procedure)
            {
                Stack new_env = extendStack(stack, in_app->arg_count, reduced_args);
                out = normalize(arena, &new_env, reduced_op->Procedure.body);
            }
            else
            {
                if (reduced_op->cat == EC_Builtin_identical)
                {// special case for equality
                    auto compare = compareExpressions(reduced_args[1], reduced_args[2]);
                    if (compare == Trinary_True)
                        out = builtin_True;
                    else if (compare == Trinary_False)
                        out = builtin_False;
                }

                if (!out)
                {
                    // TODO: don't allocate if the out & in are identical.
                    out = newExpression(arena, EC_Application, in->type);
                    out->cat = EC_Application;
                    auto app = castExpression(Application, out);

                    app->op        = reduced_op;
                    app->arg_count = in_app->arg_count;
                    allocateArray(arena, app->arg_count, app->args);
                    for (int arg_id = 0; arg_id < app->arg_count; arg_id++)
                    {
                        app->args[arg_id] = reduced_args[arg_id];
                    }
                }
            }
        } break;

        case EC_Switch:
        {
            auto myswitch = &in->Switch;
            Expression *reduced_subject = normalize(arena, stack, myswitch->subject);

            auto subject_type = reduced_subject->type;
            auto switch_struct = castExpression(Struct, subject_type);
            auto ctor_count = switch_struct->ctor_count;
            auto ctor_id = matchSwitchCase(reduced_subject);

            if (ctor_id.success)
                out = normalize(arena, stack, myswitch->case_bodies[ctor_id.value]);
            else
            {
                auto reduced_bodies = pushArray(arena, switch_struct->ctor_count, Expression*);
                for (int ctor_id = 0; ctor_id < ctor_count; ctor_id++)
                {
                    reduced_bodies[ctor_id] = normalize(arena, stack, myswitch->case_bodies[ctor_id]);
                }

                if (ctor_count > 0)
                {
                    b32 all_equal = true;
                    for (int ctor_id = 1, stop = false;
                         (ctor_id < ctor_count) & !stop;
                         ctor_id++)
                    {
                        if (!expressionsIdenticalB32(reduced_bodies[0], reduced_bodies[ctor_id]))
                        {
                            all_equal = false;
                            stop = true;
                        }
                    }
                    if (all_equal)
                        out = reduced_bodies[0];
                }

                if (!out)
                {
                    // todo: #memory don't copy too soon
                    out = newExpression(arena, EC_Switch, subject_type);
                    out->Switch.subject     = reduced_subject;
                    out->Switch.case_bodies = reduced_bodies;
                }
            }
        } break;

        default:
        {
            out = in;
        } break;
    }

    return out;
}

internal Expression *
newApplication(MemoryArena *arena, Token *blame_token, Expression *op, Expression **args, s32 arg_count)
{
    unpackGlobals;
    Expression *out = 0;
    auto signature = castExpression(ArrowType, op->type);
    if (signature)
    {
        if (signature->arg_count == arg_count)
        {
            out = newExpression(arena, EC_Application, 0);
            auto app = &out->Application;
            app->op = op;
            app->arg_count = signature->arg_count;
            allocateArray(arena, app->arg_count, app->args);

            Stack stack = {};
            stack.arena = arena;
            allocateArray(temp_arena, app->arg_count, stack.first);

            for (int arg_id = 0, stop = 0;
                 (arg_id < signature->arg_count) && !stop;
                 arg_id++)
            {
                auto arg = args[arg_id];
                stack.first[stack.count++] = arg;
                auto expected_arg_type = normalize(temp_arena, &stack, getArgType(op, arg_id));
                if (expressionsIdenticalB32(arg->type, expected_arg_type))
                {
                    app->args[arg_id] = arg;
                    out->type = normalize(arena, &stack, signature->return_type);
                }
                else
                {
                    out = 0;
                    parseError(blame_token, "argument %d has wrong type", arg_id);
                    pushAttachment(tk, "got", arg->type);
                    pushAttachment(tk, "expected", expected_arg_type);
                    stop = true;
                }
            }
        }
        else
            parseError(blame_token, "incorrect arg count: %d (procedure expected %d)", arg_count, signature->arg_count);
    }
    else
        tokenError(blame_token, "operator must have an arrow type");
    
    return out;
}

internal Expression *
parseExpression(MemoryArena *arena, Bindings *bindings, s32 min_precedence = -9999)
{
    unpackGlobals;
    pushContext;

    Expression *out = parseOperand(arena, bindings);
    if (parsing(tk))
    {
        // (a+b) * c
        //     ^
        for (b32 stop = false; !stop && parsing(tk);)
        {
            Token op_token = peekNext(tk);
            if (isIdentifier(&op_token))
            {// infix operator syntax
                // (a+b) * c
                //        ^
                auto op_lookup = lookupNameRecursive(bindings, &op_token);
                if (op_lookup.found)
                {
                    Ast op = op_lookup.value;
                    auto precedence = precedenceOf(op);
                    if (precedence >= min_precedence)
                    {
                        // recurse
                        advance(tk);
                        // a + b * c
                        //      ^
                        Expression *recurse = parseExpression(arena, bindings,  precedence);
                        if (parsing(tk))
                        {
                            switch (op.cat)
                            {
                                case AstCat_Expression:
                                {
                                    Expression *args[2];
                                    auto op_exp = castAst(Expression, op);
                                    args[0] = out;
                                    args[1] = recurse;
                                    out = newApplication(arena, &op_token, op_exp, args, 2);
                                }
                                break;

                                case AstCat_Macro:
                                {
                                    Expression *args[3];
                                    args[0] = out->type;
                                    args[1] = out;
                                    args[2] = recurse;
                                    out = newApplication(arena, &op_token, &builtin_identical, args, 3);
                                }
                                break;
                            }
                        }
                    }
                    else
                    {
                        // we are pulled to the left
                        // a * b + c
                        //      ^
                        stop = true;
                    }
                }
                else
                    tokenError(&op_token, "unbound operator");
            }
            else if (isExpressionEndMarker(&op_token))
                stop = true;
            else
                tokenError(&op_token, "expected operator token, got");
        }
    }

    if (parsing(tk))
    {
        assert(out);
    }
    else
        out = 0;

    popContext(tk);
    return out;
}

internal Expression *
parseSwitch(MemoryArena *arena, Bindings *bindings)
{
    pushContext;
    unpackGlobals;
    auto token1 = peekNext(tk);

    auto out = newExpression(arena, EC_Switch, 0);
    auto myswitch = castExpression(Switch, out);

    Token subject_token = peekNext(tk);
    myswitch->subject = parseExpression(arena, bindings);
    if (requireChar(tk, '{'))
    {
        Expression *subject_type = myswitch->subject->type;
        if (subject_type->cat == EC_Struct)
        {
            auto subject_struct = &subject_type->Struct;
            auto expected_ctor_count = subject_struct->ctor_count;
            allocateArray(arena, expected_ctor_count, myswitch->case_bodies);

            s32 actual_case_id = 0;
            Expression *switch_type = 0;
            for (b32 stop = false;
                 !stop && parsing();)
            {
                if (optionalChar('}'))
                    stop = true;
                else
                {
                    Expression *switch_case = parseExpression(arena, bindings);
                    if (advance().cat == TC_Arrow)
                    {
                        auto matched_case_id = matchSwitchCase(switch_case);

                        if (!matched_case_id.success)
                            tokenError("expression is not a constructor for type");
                        else
                        {
                            auto body_token = peekNext(tk);
                            auto body = parseExpression(arena, bindings);
                            if (parsing())
                            {
                                if (!switch_type)
                                    switch_type = body->type;
                                else if (!expressionsIdenticalB32(body->type, switch_type))
                                {
                                    parseError(&body_token, "mismatched return type in input case %d", actual_case_id);
                                    pushAttachment(tk, "got", body->type);
                                    pushAttachment(tk, "expected", switch_type);
                                    stop = true;
                                }

                                myswitch->case_bodies[matched_case_id.value] = body;
                                actual_case_id++;
                            }

                            if (!optionalChar(tk, ','))
                            {
                                requireChar('}');
                                stop = true;
                            }
                        }
                    }
                    else
                        tokenError("require an arrow");
                }
            }

            if (!parsing())
            {}
            else if (actual_case_id != expected_ctor_count)
            {
                parseError(&token1, "wrong number of cases, expected: %d, got: %d",
                           expected_ctor_count, actual_case_id);
            }
            else if (actual_case_id == 0)
            {
                // TODO: support empty switch later.
                tokenError(&token1, "cannot assign type to empty switch expression");
                out->type = 0;
            }
            else
                out->type = switch_type;
        }
        else
            tokenError(&subject_token, "cannot switch over a non-struct");
    }
    popContext();
    return out;
}

internal Expression *
parseOperand(MemoryArena *arena, Bindings *bindings)
{
    unpackGlobals;
    pushContext;

    Expression *out = 0;
    Token token1 = advance(tk);
    if (Keyword keyword = matchKeyword(&token1))
    {
        switch (keyword)
        {
            case Keyword_Switch:
            {
                out = parseSwitch(arena, bindings);
            } break;

            default:
                tokenError("keyword not part of expression");
        }
    }
    else if (isIdentifier(&token1))
    {
        auto lookup1 = lookupNameRecursive(bindings, &token1);
        if (lookup1.found)
        {
            if (lookup1.value.cat == AstCat_Expression)
                out = (Expression *)lookup1.value.p;
            else if (lookup1.value.cat == AstCat_Macro)
                todoIncomplete;
        }
        else
            tokenError("unbound identifier in expression");
    }
    else if (equals(&token1, '('))
    {
        out = parseExpression(arena, bindings);
        if (parsing(tk))
            requireChar(tk, ')');
    }
    else
    {
        tokenError("expected start of expression");
    }

    if (parsing(tk))
    {
        Token funcall = peekNext(tk);
        if (equals(&funcall, '('))
        {// function call syntax, let's keep going
            advance(tk);
            auto op = out;
            if (op->type->cat == EC_ArrowType)
            {
                auto signature = &op->type->ArrowType;
                auto args = pushArray(arena, signature->arg_count, Expression*);
                s32 actual_arg_count = 0;
                for(s32 stop = false, arg_id = 0;
                    !stop;
                    arg_id++)
                {
                    if (*tk->at == ')')
                    {
                        stop = true;
                        actual_arg_count = arg_id;
                    }
                    else
                    {
                        auto arg = parseExpression(arena, bindings);
                        // todo: typecheck the arg
                        if (parsing(tk))
                        {
                            args[arg_id] = arg;

                            for (b32 non_comma = false; !non_comma;)
                            {// eat all commas for now
                                if (*tk->at == ',')
                                    advance(tk);
                                else
                                    non_comma = true;
                            }
                        }
                        else
                            stop = true;
                    }
                }
                if (parsing(tk) && requireChar(tk, ')'))
                {
                    out = newApplication(arena, &funcall, op, args, actual_arg_count);
                }
            }
            else
                tokenError("cannot call non-procedure");
        }
    }

    popContext(tk);
    return out;
}

internal Expression *
parseProof(MemoryArena *arena, Bindings *bindings, Stack *stack, Expression *goal)
{
    Expression *out = 0;

    unpackGlobals;
    pushContext;

    goal = normalize(temp_arena, stack, goal);

    Token token = advance(tk);
    switch (auto keyword = matchKeyword(&token))
    {
        case Keyword_Switch:
        {
            auto switch_subject = parseExpression(arena, bindings);
            auto subject_var = castExpression(Variable, switch_subject);
            if (subject_var)
            {
                if (requireChar(tk, ';'))
                {
                    out = newExpression(arena, EC_Switch, 0);
                    auto myswitch = &out->Switch;
                    myswitch->subject = switch_subject;
                    auto subject_type = myswitch->subject->type;
                    auto subject_struct = castExpression(Struct, subject_type);
                    if (subject_struct)
                    {
                        auto ctor_count = subject_struct->ctor_count;
                        allocateArray(arena, ctor_count, myswitch->case_bodies);
                        for (s32 ctor_id = 0;
                             (ctor_id < ctor_count) && parsing(tk);
                             ctor_id++)
                        {
                            if (optionalChar('-'))
                            {
                                // todo: bind variable to the stack 
                                // todo: what if we switched over composite expression as subject? the stack wouldn't help at all
                                Expression *ctor_exp = newExpression(temp_arena, EC_ConstructorRef, subject_type);
                                ctor_exp->ConstructorRef.id = subject_var->id;
                                stack->first[subject_var->id] = ctor_exp;
                                Expression *subgoal = normalize(temp_arena, stack, goal);
                                Expression *subproof = parseProof(temp_arena, bindings, stack, subgoal);
                                myswitch->case_bodies[ctor_id] = subproof;
                            }
                            else if (ctor_id == 0)
                                parseError(&tk->last_token, "%d goals remaining", ctor_count);
                            else
                                tokenError("please begin to prove next switch case with '-'");
                        }
                    }
                    else
                        tokenError("cannot switch on non-structs");
                }
            }
            else
                tokenError("cannot switch over non-var (for now)");
        } break;

        case Keyword_Return:
        {
            Token return_token = peekNext(tk);
            Expression *returned = parseExpression(arena, bindings);
            if (parsing(tk))
            {
                if (!returned->type)
                    tokenError(&return_token, "failed to infer type");
                else if (!expressionsIdenticalB32(returned->type, goal))
                {
                    parseError(&return_token, "returned expression doesn't have the correct type");
                    pushAttachment(tk, "returned type", returned->type);
                }
                else
                    out = returned;
            }
            optionalChar(tk, ';');
        } break;

        default:
            tokenError(&tk->last_token, "please input a proof command in place of token");
    }

    if (!parsing(tk))
    {
        pushAttachment(global_tokenizer, "proof in progress", goal);
    }

    popContext(tk);
    return out;
}

internal void
parseDefine(MemoryArena* arena, b32 is_theorem = false)
{
    unpackGlobals;
    pushContext;

    Token define_name = advance(tk);
    if ((define_name.cat == TC_Alphanumeric)
        || (define_name.cat == TC_Special))
    {
        auto define_slot = lookupNameCurrentFrame(global_bindings, define_name.text, true);
        if (define_slot.found)
            tokenError("re-definition");
        else if (requireChar(tk, '('))
        {
            auto  define_type       = newExpression(arena, EC_ArrowType, &builtin_Proc);
            auto *define_exp        = newExpression(arena, EC_Procedure, define_type);
            define_slot.slot->value = expressionAst(define_exp);
            auto proc  = &define_exp->Procedure;
            proc->name = define_name.text;

            auto signature = &define_type->ArrowType;

            s32 expected_arg_count = 0;
            {// peek ahead to get the arg count
                // todo: this code is so garbage
                Tokenizer tk1_ = *tk;
                Tokenizer *tk1 = &tk1_;
                s32 nesting_depth = 0;
                char previous = '(';
                for (b32 stop = false; !stop;)
                {
                    Token token = advance(tk1);
                    b32 current_is_comma = false;
                    if (equals(&token, '('))
                        nesting_depth++;
                    else if (equals(&token, ')'))
                    {
                        if (nesting_depth > 0)
                            nesting_depth--;
                        else
                        {
                            if ((previous != ',') && (previous != '('))
                                expected_arg_count++;
                            stop = true;
                        }
                    }
                    else if ((nesting_depth == 0)
                             && (equals(&token, ',')))
                    {
                        expected_arg_count++;
                        current_is_comma = true;
                    }
                    previous = *tk1->at;
                }
            }
            signature->arg_count = expected_arg_count;
            allocateArray(arena, expected_arg_count, signature->args);

            Bindings *local_bindings = extendBindings(arena, global_bindings);
            s32 actual_arg_count = 0;
            for (s32 arg_id = 0, stop = 0;
                 !stop && parsing(tk);
                 arg_id++)
            {// parsing arguments
                Token arg_name_or_end = advance(tk);
                if (equals(&arg_name_or_end, ')'))
                    stop = true;

                else if (arg_name_or_end.cat == TC_Alphanumeric)
                {
                    auto arg_name_lookup = lookupNameCurrentFrame(local_bindings, arg_name_or_end.text, true);
                    if (arg_name_lookup.found)
                        tokenError("duplicate arg name");
                    else if (requireChar(tk, ':'))
                    {
                        auto arg_exp = newExpression(arena, EC_Variable, 0);
                        arg_name_lookup.slot->value = expressionAst(arg_exp);

                        arg_exp->Variable.name        = arg_name_or_end.text;
                        arg_exp->Variable.id          = arg_id;
                        arg_exp->Variable.stack_delta = 0;
                        
                        Expression *arg_type    = parseExpression(arena, local_bindings);
                        arg_exp->type           = arg_type;
                        signature->args[arg_id] = arg_exp;
                        actual_arg_count++;

                        Token delimiter = advance(tk);
                        if (equals(&delimiter, ')'))
                            stop = true;
                        else if (!equals(&delimiter, ','))
                            tokenError("unexpected token after arg type");

                    }
                }
                else
                    tokenError("expected arg name");
            }
            if (parsing(tk))
            {
                assert(actual_arg_count == expected_arg_count);
            }

            // return type
            if (requireChar(tk, ':'))
            {
                signature->return_type = parseExpression(arena, local_bindings);
                if (requireChar(tk, '{'))
                {
                    Token body_token = peekNext(tk);
                    Expression *body = 0;
                    if (is_theorem)
                    {
                        Stack stack = {};
                        stack.arena = temp_arena;
                        stack.count = actual_arg_count;
                        allocateArrayZero(temp_arena, actual_arg_count, stack.first);
                        body = parseProof(arena, local_bindings, &stack, signature->return_type);
                    }
                    else
                    {
                        body = parseExpression(arena, local_bindings);
                    }
                    if (parsing(tk) && requireChar(tk, '}'))
                    {
                        proc->body = body;

                        if (!is_theorem)
                        {
                            auto body_type = proc->body->type;
                            if (body_type != signature->return_type)
                                tokenError(&body_token, "body has wrong type");
                        }
                    }
                }
            }
        }
    }
    else
        tokenError("expected a name to be defined");

    popContext(tk);
}

inline Tokenizer *
newTokenizer(MemoryArena *arena, String directory, char *input)
{
    Tokenizer *out = pushStruct(arena, Tokenizer);
    out->directory   = directory;
    out->at          = input;
    out->line_number = 1;
    out->column      = 1;
    out->error_arena = arena;
    
    return out;
}

struct FileList
{
    char     *first_path;
    char     *first_content;
    FileList *next;
};

struct EngineState
{
    FileList *file_list;
};

internal b32
interpretFile(EngineState *state, MemoryArena *arena, FilePath input_path, b32 is_root_file = false);

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state, MemoryArena *arena)
{
    pushContext;
    auto temp_arena = global_temp_arena;

    while (parsing())
    {
        auto top_level_temp = beginTemporaryMemory(temp_arena);
        Token token = advance(); 
        if (equals(&token, '\0'))
        {}
        else if (equals(&token, '#'))
        {// compile directive
            token = advance();
            switch (MetaDirective directive = matchMetaDirective(&token))
            {
                case MetaDirective_Load:
                {
                    pushSubContext("#load");
                    auto file = advance();
                    if (file.cat != TC_StringLiteral)
                        tokenError("expect \"FILENAME\"");
                    else
                    {
                        auto path_buffer = arena;
                        char *load_path = myprint(path_buffer, global_tokenizer->directory);
                        myprint(path_buffer, file.text);
                        path_buffer->used++;

                        // note: this could be made more efficient but we don't care.
                        auto full_path = platformGetFileFullPath(arena, load_path);

                        b32 already_loaded = false;
                        for (auto file_list = state->file_list;
                             file_list && !already_loaded;
                             file_list = file_list->next)
                        {
                            if (equals(file_list->first_path, load_path))
                                already_loaded = true;
                        }

                        if (!already_loaded)
                        {
                            auto interp_result = interpretFile(state, arena, full_path);
                            if (!interp_result)
                                tokenError("failed loading file");
                        }
                    }
                    popContext();
                } break;

                default:
                {
                    tokenError("unknown meta directive");
                } break;
            }
        }
        else
        {
            switch (Keyword keyword = matchKeyword(&token))
            {
                case Keyword_Typedef:
                    parseTypedef(arena);
                    break;

                case Keyword_Define:
                    parseDefine(arena);
                    break;

                case Keyword_Theorem:
                    parseDefine(arena, true);
                    break;

                case Keyword_Print:
                case Keyword_PrintRaw:
                {
                    b32 should_print = ((keyword == Keyword_PrintRaw)
                                        || (keyword == Keyword_Print));

                    auto temp = beginTemporaryMemory(arena);
                    auto exp = parseExpression(arena, global_bindings);

                    if (parsing())
                    {
                        Stack empty_stack = {};
                        empty_stack.arena = arena;
                        Expression *reduced = normalize(arena, &empty_stack, exp);

                        if (should_print)
                        {
                            auto buffer = subArena(arena, 256);
                            {
                                if (keyword == Keyword_Print)
                                    printExpression(&buffer, reduced, true);
                                else
                                    printExpression(&buffer, exp, true);
                            }
                            printf("%s\n", buffer.base);
                        }
                    }
                    endTemporaryMemory(temp);
                    requireChar(';');
                } break;

                case Keyword_Check:
                {
                    auto exp = parseExpression(temp_arena, global_bindings);
                    if (parsing())
                    {
                        requireChar(':');
                        auto expected_type = parseExpression(temp_arena, global_bindings);
                        if (parsing())
                        {
                            Stack stack = {};
                            stack.arena = temp_arena;
                            auto expected_reduced = normalize(temp_arena, &stack, expected_type);
                            auto actual_reduced = normalize(temp_arena, &stack, exp->type);
                            if (!expressionsIdenticalB32(expected_reduced, actual_reduced))
                            {
                                tokenError(&token, "type check failed");
                                pushAttachment("expected type", expected_reduced);
                                pushAttachment("actual type", actual_reduced);
                            }
                        }
                    }
                    requireChar(';');
                } break;

                default:
                    tokenError("unexpected token");
            }
        }
        endTemporaryMemory(top_level_temp);
    }

    popContext();
}

inline b32
isMatchingPair(Token *left, Token *right)
{
    char l = left->text.chars[0];
    char r = right->text.chars[0];
    return (((l == '(') && (r == ')')) ||
            ((l == '{') && (r == '}')));
}

internal void
initializeEngine(MemoryArena *arena)
{
    global_temp_arena_ = subArena(arena, megaBytes(2));
    global_temp_arena  = &global_temp_arena_;
    allocate(arena, global_bindings);
    global_bindings->arena = arena;

    addBuiltinName("identical", &builtin_identical);
    addBuiltinName("Set",  &builtin_Set);
    addBuiltinName("Prop", &builtin_Prop);
    addBuiltinName("Proc", &builtin_Proc);
    addBuiltinMacro("=");

    const char *true_members[] = {"truth"};
    addBuiltinStruct(arena, "True", true_members, 1);
    builtin_True = castAst(Expression, lookupNameCurrentFrame(global_bindings, toString("True"), false).slot->value);
    builtin_truth = castAst(Expression, lookupNameCurrentFrame(global_bindings, toString("truth"), false).slot->value);

    addBuiltinStruct(arena, "False", (const char **)0, 0);
    builtin_False = castAst(Expression, lookupNameCurrentFrame(global_bindings, toString("False"), false).slot->value);
}

internal b32
interpretFile(EngineState *state, MemoryArena *arena, FilePath input_path, b32 is_root_file)
{
    b32 success = true;
#if 0
    auto begin_time = platformGetWallClock(arena);
#endif

    ReadFileResult read = platformReadEntireFile(input_path.path);
    if (read.content)
    {
        auto new_file_list           = pushStruct(arena, FileList);
        new_file_list->first_path    = input_path.path;
        new_file_list->first_content = read.content;
        new_file_list->next          = state->file_list;
        state->file_list             = new_file_list;

        auto tk = newTokenizer(arena, input_path.directory, read.content);
        auto old_tokenizer = global_tokenizer;
        global_tokenizer   = tk;

        parseTopLevel(state, arena);
        ParseError error = tk->error;
        if (error)
        {
            success = false;
            printf("%s:%d:%d: [%s] %s",
                   input_path.path,

                   error->token.line_number,
                   error->token.column,

                   error->context,
                   error->message.base);

            if (error->attached_count > 0)
            {
                printf(" (");
                for (int attached_id = 0;
                     attached_id < error->attached_count;
                     attached_id++)
                {
                    auto attachment = error->attached[attached_id];
                    printf("%s: ", attachment.string);
                    printExpression(0, attachment.expression);
                    if (attached_id != error->attached_count-1) 
                        printf(", ");
                }
                printf(")");
            }
            printf("\n");
        }

#if 0
        auto compile_time = platformGetSecondsElapsed(begin_time, platformGetWallClock(arena));
        printf("Compile time for file %s: %fs\n", file_path, compile_time);
        printf("----------------\n");
#endif

        global_tokenizer = old_tokenizer;
    }
    else
    {
        printf("Failed to read input file %s\n", input_path.file);
        success = false;
    }

    if (is_root_file)
        checkArena(global_temp_arena);

    return success;
}

internal b32
beginInterpreterSession(MemoryArena *arena, char *initial_file)
{
    initializeEngine(arena);
    auto state = pushStruct(arena, EngineState);
    auto input_path = platformGetFileFullPath(arena, initial_file);
    b32 success = interpretFile(state, arena, input_path, true);

    for (FileList *file_list = state->file_list;
         file_list;
         file_list = file_list->next)
    {
        platformFreeFileMemory(file_list->first_content);
    }
    
    checkArena(arena);
    return success;
}

int
engineMain(EngineMemory *memory)
{
    assert(arrayCount(keywords)       == Keywords_Count_);
    assert(arrayCount(metaDirectives) == MetaDirective_Count_);

    int success = true;

    auto init_arena_ = newArena(memory->storage_size, memory->storage);
    auto init_arena = &init_arena_;

    builtin_identical.cat = EC_Builtin_identical;
    builtin_Set.cat       = EC_Builtin_Set;
    builtin_Prop.cat      = EC_Builtin_Prop;
    builtin_Proc.cat      = EC_Builtin_Proc;
    builtin_Type.cat      = EC_Builtin_Type;

    builtin_Set.type  = &builtin_Type;
    builtin_Prop.type = &builtin_Type;
    builtin_Proc.type = &builtin_Type;

    {
        // Here we give 'identical' a type (A: Set, a:A, b:A) -> Prop
        // TODO: so we can't prove equality between props.
        builtin_identical.type = newExpression(init_arena, EC_ArrowType, 0);
        auto signature = castExpression(ArrowType, builtin_identical.type);
        signature->arg_count   = 3;
        signature->return_type = &builtin_Prop;

        allocateArray(init_arena, 3, signature->args);
        auto args = signature->args;
        args[0]                       = newExpression(init_arena, EC_Variable, &builtin_Set);
        args[0]->Variable.stack_delta = 0;
        args[0]->Variable.name        = toString("A");
        args[1]                       = newExpression(init_arena, EC_Variable, args[0]);
        args[1]->Variable.id          = 1;
        args[1]->Variable.stack_delta = 0;
        args[1]->Variable.name        = toString("a");
        args[2]                       = newExpression(init_arena, EC_Variable, args[0]);
        args[2]->Variable.id          = 2;
        args[2]->Variable.stack_delta = 0;
        args[2]->Variable.name        = toString("b");
    }

    auto interp_arena_ = subArena(init_arena, getArenaFree(init_arena));
    auto interp_arena = &interp_arena_;
    if (!beginInterpreterSession(interp_arena, "..\\data\\operator.rea"))
        success = false;

    resetZeroArena(interp_arena);
    if (!beginInterpreterSession(interp_arena, "..\\data\\test.rea"))
        success = false;

    return success;
}

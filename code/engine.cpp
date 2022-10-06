#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"

// NOTE: Eventually this will talk to the editor, but let's work in console mode for now.
// Important: abort all parsing when tokenizer reports error.

enum ExpressionCategory
{
    EC_Unknown,
    EC_Variable,                // reference to some unknown on "the stack"
    EC_Application,             // operator application
    EC_Switch,                  // switch statement
    EC_Struct,                  // struct information
    EC_Procedure,               // holds actual computation (ie body that can be executed)
    EC_ArrowType,               // type of procedure and built-in objects
    EC_ConstructorRef,           // reference to a constructor of a type

    EC_Builtin_Set_Type,        // a type to hold structs
    EC_Builtin_Prop_Type,       // a type to hold all propositions
    EC_Builtin_Proc_Type,       // NOTE: invented type
    EC_Builtin_Equality,        // computational meta-equality
    // TODO: remove these after we have proper proof facility!
    EC_Builtin_True,
    EC_Builtin_False,
};

#define castExpression(Type, exp) (exp->cat == EC_##Type) ? &exp->Type : 0;

struct Expression;

struct Variable
{
    String name;
    s32    stack_depth;
    u32    id;
};

struct Application
{
    Expression *op;
    u32        arg_count;
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
    Expression         *type;
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

Expression builtin_equality;
Expression builtin_true;
Expression builtin_false;
Expression builtin_set_type;
Expression builtin_prop_type;
Expression builtin_proc_type;

internal void
printConstructor(MemoryArena *buffer, Constructor *ctor)
{
    myprint(buffer, ctor->name);
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
                myprint(buffer, " | ");
                printConstructor(buffer, subject_struct->ctors + ctor_id);
                myprint(buffer, " { ");
                printExpression(buffer, myswitch->case_bodies[ctor_id]);
                myprint(buffer, " }");
            }
            myprint(buffer, " }");
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
                    printExpression(buffer, signature->args[arg_id], true);
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

        case EC_Builtin_Equality:
        {
            myprint(buffer, "=");
        } break;

        case EC_Builtin_True:
        {
            myprint(buffer, "true");
        } break;

        case EC_Builtin_False:
        {
            myprint(buffer, "false");
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

        default:
        {
            myprint(buffer, "<unsupported category>");
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

struct Binding
{
    String      key;
    Expression *value;
    Binding    *next;
};

struct Bindings
{
    s32          stack_depth;
    MemoryArena *arena;
    Binding      first[128];
    Bindings    *next;
};

struct Stack
{
    s32           depth;
    MemoryArena  *arena;
    u32           count;
    Expression  **first;
    Stack        *next;
};

inline Bindings *
extendBindings(MemoryArena *arena, Bindings *outer)
{
    Bindings *out = pushStruct(arena, Bindings);
    for (int i = 0; i < arrayCount(out->first); i++)
    {// invalidate these slots
        Binding *slot = &out->first[i];
        slot->key.length = 0;
    }
    out->stack_depth = outer->stack_depth+1;
    out->next        = outer;
    out->arena       = arena;
    return out;
}

struct ParserState
{
    MemoryArena scoped_arena;   // used for storing e.g stack frames
    Bindings    global_bindings;
    Tokenizer   tokenizer;
};

struct ExpressionParserState
{
    MemoryArena *arena;
    Bindings    *bindings;
    Tokenizer   *tk;
};

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
        slot->value = 0;
    }

    LookupName out = { slot, found };
    return out;
}

struct LookupNameRecursive { Expression *value; b32 found; };

inline LookupNameRecursive
lookupNameRecursive(Bindings *bindings, Token *token)
{
    Expression *value = 0;
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
parseConstructorDef(ParserState *state, MemoryArena *arena, Expression *type, s32 ctor_id)
{
    Constructor out = {};
    Tokenizer *tk = &state->tokenizer;
    Token ctor_token = advance(tk);
    switch (ctor_token.cat)
    {
        case TC_Special:
        case TC_Alphanumeric:
        {
            LookupName ctor_lookup = lookupNameCurrentFrame(&state->global_bindings, ctor_token.text, true);
            if (ctor_lookup.found)
            {
                todoErrorReport;
            }
            else
            {
                out.name      = ctor_token.text;

                auto exp = newExpression(arena, EC_ConstructorRef, type);
                auto ctor_ref = &exp->ConstructorRef;
                ctor_ref->id  = ctor_id;

                ctor_lookup.slot->value = exp;
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
parseError(Tokenizer *tk, Token *token, char *format, ...)
{
    assert(parsing(tk));
    auto arena = &tk->error_arena;
    tk->error = pushStructZero(arena, ParseErrorData);
    tk->error->message = subArena(&tk->error_arena, 256);

    va_list arg_list;
    __crt_va_start(arg_list, format);
    printToBufferVA(&tk->error->message, format, arg_list);
    __crt_va_end(arg_list);

    tk->error->token = *token;
    tk->error->context = tk->context->first;

}

internal void
tokenError(Tokenizer *tk, Token *token, char *message)
{
    auto arena = tk->error_arena;
    parseError(tk, token, message);
    myprint(&tk->error->message, ": ");
    myprint(&tk->error->message, token->text);
}

internal void
tokenError(Tokenizer *tk, char *message)
{
    tokenError(tk, &tk->last_token, message);
}

inline b32
requireChar(Tokenizer *tk, char c)
{
    auto out = true;

    Token token = advance(tk);
    if (!((token.text.length == 1) && (token.text.chars[0] == c)))
    {
        parseError(tk, &token, "expected character %c", c);
        out = false;
    }

    return out;
}

inline void
optionalChar(Tokenizer *tk, char c)
{
    Token token = peekNext(tk);
    if (equals(&token, c))
        advance(tk);
}

internal void
parseTypedef(ParserState *state, MemoryArena *arena)
{
    Tokenizer *tk = &state->tokenizer;
    Token type_name = advance(tk);
    if (type_name.cat == TC_Alphanumeric)
    {
        // NOTE: the type is in scope of its own constructor.
        LookupName type_lookup = lookupNameCurrentFrame(&state->global_bindings, type_name.text, true);
        if (type_lookup.found)
            tokenError(tk, "redefinition of type");
        else
        {
            auto *struct_exp = newExpression(arena, EC_Struct, &builtin_set_type);
            type_lookup.slot->value = struct_exp;

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
                    mystruct->ctors[constructor_id] = parseConstructorDef(state, arena, struct_exp, constructor_id);
                    actual_case_count++;
                }
                else
                    parseError(tk, &bar_or_stop, "Expected '|' or '}'");
            }
            assert(actual_case_count == expected_case_count);
            mystruct->ctor_count = actual_case_count;

            assert(lookupNameCurrentFrame(&state->global_bindings, type_name.text).found);
        }
    }
}

struct OptionalU32 { b32 success; u32 value; };

inline b32
equals(Variable atom1, Variable atom2)
{
    return ((atom1.id == atom2.id)
            && (atom1.stack_depth == atom2.stack_depth));
}

internal Expression *
resolve(Stack *stack, Variable variable)
{
    u32 traverse_count = stack->depth - variable.stack_depth;
    for (u32 i = 0; i < traverse_count; i++)
        stack = stack->next;
    assert(variable.id < stack->count);
    Expression *out = stack->first[variable.id];
    return out;
}

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
        else
            todoIncomplete;  // handle composite cases
    }
    
    return out;
}

enum Trinary
{
    Trinary_False, Trinary_True, Trinary_Unknown,
};

inline Trinary
expressionsIdentical(Expression *lhs, Expression *rhs)
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
                if ((lhs->Variable.stack_depth == rhs->Variable.stack_depth)
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
                    for (auto arg_id = 0;
                         (arg_id < arg_count) && (!mismatch_found);
                         arg_id++)
                    {
                        auto lhs_arg = lhs->ArrowType.args[arg_id];
                        auto rhs_arg = rhs->ArrowType.args[arg_id];
                        auto compare = expressionsIdentical(lhs_arg->type, rhs_arg->type);
                        if (compare != Trinary_True)
                        {
                            out = Trinary_False;
                            mismatch_found = true;
                        }
                    }
                    if (!mismatch_found)
                        out = Trinary_True;
                }
                else
                    out = Trinary_False;
            } break;

            default:
                todoIncomplete;
        }
    }

    return out;
}

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
    return inString("{},).", token);
}

inline s32
precedenceOf(Expression *exp)
{
    // todo: implement for real
    switch (exp->cat)
    {
        case EC_Procedure:
        {
            if (equals(exp->Procedure.name, "&"))
                return 20;
            else if (equals(exp->Procedure.name, "|"))
                return 10;
            else
                return 100;
        } break;

        case EC_Builtin_Equality:
        {
            return 0;
        } break;

        invalidDefaultCase;
    }
    return 0;
}

internal Expression *
parseOperand(ExpressionParserState *state);

internal Expression *
getArgType(Expression *op, s32 arg_id)
{
    auto signature = castExpression(ArrowType, op->type);
    assert(arg_id < signature->arg_count);
    return signature->args[arg_id]->type;
}

internal b32
typecheckAndAssignArg(Tokenizer *tk, Token *blame_token, Application *app, Expression *arg, s32 arg_id)
{
    b32 success = false;
    auto expected_arg_type = getArgType(app->op, arg_id);
    auto compare = expressionsIdentical(arg->type, expected_arg_type);
    if (compare == Trinary_True)
    {
        success = true;
        app->args[arg_id] = arg;
    }
    else
    {
        parseError(tk, blame_token, "argument %d has wrong type", arg_id);
        auto msg = &tk->error->message;
        pushAttachment(tk, "got", arg->type);
        pushAttachment(tk, "expected", expected_arg_type);
    }

    return success;
}

internal Expression *
parseExpressionContinue(ExpressionParserState *state, Expression *left, s32 min_precedence, Application *hole)
{
    Tokenizer   *tk       = state->tk;
    pushContext(tk);
    MemoryArena *arena    = state->arena;
    Bindings    *bindings = state->bindings;

    Expression *out = 0;

    Token arg0_token = peekNext(tk);
    Expression *arg0 = parseOperand(state);
    if (parsing(tk))
    {
        // (a+b) * c
        //     ^
        Token op_token = peekNext(tk);
        if (isIdentifier(&op_token))
        {// infix operator syntax
            advance(tk);
            // (a+b) * c
            //        ^
            auto op_lookup = lookupNameRecursive(bindings, &op_token);
            if (op_lookup.found)
            {
                auto op = op_lookup.value;
                if (op->type->cat == EC_ArrowType)
                {
                    auto return_type = op->type->ArrowType.return_type;
                    Expression *app_exp = newExpression(arena, EC_Application, return_type);
                    auto app = &app_exp->Application;

                    auto todo_arg_count = 2;
                    app->op        = op;
                    app->arg_count = todo_arg_count;
                    allocateArray(arena, app->arg_count, app->args);

                    auto precedence = precedenceOf(app->op);
                    if (left)
                    {
                        assert(left->cat == EC_Application);
                        if (precedence >= min_precedence)
                        {
                            // a + b * c
                            //      ^
                            if (typecheckAndAssignArg(tk, &arg0_token, app, arg0, 0) &&
                                typecheckAndAssignArg(tk, &op_token, hole, app_exp, 1))
                            {
                                out = parseExpressionContinue(state, left, min_precedence, app);
                            }
                        }
                        else
                        {
                            // a * b + c
                            //      ^
                            if (typecheckAndAssignArg(tk, &arg0_token, hole, arg0, 1) &&
                                typecheckAndAssignArg(tk, &op_token, app, left, 0))
                            {
                                out = parseExpressionContinue(state, app_exp, precedence, app);
                            }
                        }
                    }
                    else
                    {
                        // a * b
                        //    ^
                        if (typecheckAndAssignArg(tk, &arg0_token, app, arg0, 0))
                            out = parseExpressionContinue(state, app_exp, precedence, app);
                    }
                }
                else
                    tokenError(tk, &op_token, "operator must have an arrow type");
            }
            else
                tokenError(tk, &op_token, "unbound operator");
        }
        else if (isExpressionEndMarker(&op_token))
        {
            if (left)
            {
                typecheckAndAssignArg(tk, &arg0_token, hole, arg0, 1);
                out = left;
            }
            else
                out = arg0;
        }
        else
            tokenError(tk, &op_token, "expected operator token, got");
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

inline Expression *
parseExpression(ExpressionParserState *state)
{
    return parseExpressionContinue(state, 0, 0, 0);
}

inline Expression *
parseExpression(MemoryArena *arena, Bindings *bindings, Tokenizer *tokenizer)
{
    ExpressionParserState state;
    state.arena = arena;
    state.bindings = bindings;
    state.tk = tokenizer;
    return parseExpressionContinue(&state, 0, 0, 0);
}

internal Expression *
parseOperand(ExpressionParserState *state)
{
    Tokenizer   *tk       = state->tk;
    pushContext(tk);
    MemoryArena *arena    = state->arena;
    Bindings    *bindings = state->bindings;

    Expression *out = 0;
    Token token1 = advance(tk);
    if (isKeyword(&token1))
    {
        switch (token1.cat)
        {
            case TC_KeywordSwitch:
            {
                out = newExpression(arena, EC_Switch, 0);
                auto myswitch = castExpression(Switch, out);

                Token subject_token = peekNext(tk);
                myswitch->subject = parseExpression(state);
                requireChar(tk, '{');
                if (myswitch->subject)
                {
                    Expression *subject_type = myswitch->subject->type;
                    if (subject_type->cat == EC_Struct)
                    {
                        auto subject_struct = &subject_type->Struct;
                        auto expected_ctor_count = subject_struct->ctor_count;
                        allocateArray(arena, expected_ctor_count, myswitch->case_bodies);

                        s32 actual_case_id = 0;
                        Expression *switch_type = 0;
                        b32 mismatch_found = false;
                        for (b32 stop = false; !stop;)
                        {
                            Token bar_or_closing_brace = advance(tk);
                            switch (bar_or_closing_brace.text.chars[0])
                            {
                                case '|':
                                {
                                    MemoryArena temp_arena = beginTemporaryArena(arena);

                                    auto new_state = *state;
                                    new_state.arena = &temp_arena;
                                    Expression *switch_case = parseExpression(state);
                                    if (parsing(tk) && requireChar(tk, '{'))
                                    {
                                        auto matched_case_id = matchSwitchCase(switch_case);
                                        endTemporaryArena(&temp_arena);

                                        if (matched_case_id.success)
                                        {
                                            auto body_token = peekNext(tk);
                                            auto body = parseExpression(state);
                                            requireChar(tk, '}');

                                            if (switch_type)
                                            {
                                                auto compare = expressionsIdentical(body->type, switch_type);
                                                if (compare != Trinary_True)
                                                {
                                                    parseError(tk, &body_token, "mismatched return type in input case %d", actual_case_id);
                                                    pushAttachment(tk, "got", body->type);
                                                    pushAttachment(tk, "expected", switch_type);
                                                    mismatch_found = true;
                                                    stop = true;
                                                }
                                            }
                                            else
                                                switch_type = body->type;

                                            if (body)
                                                myswitch->case_bodies[matched_case_id.value] = body;
                                            else
                                                tokenError(tk, "body cannot be empty");
                                        }
                                        else
                                            tokenError(tk, "expression is not a constructor for type");
                                    }

                                    actual_case_id++;
                                } break;

                                case '}':
                                    stop = true;
                                    break;

                                default:
                                    tokenError(tk, "expect either '|' or '}'");
                            }
                        }

                        if (actual_case_id != expected_ctor_count)
                            parseError(tk, &token1, "wrong number of cases, expected: %d, got: %d", expected_ctor_count, actual_case_id);
                        else if (!mismatch_found)
                        {
                            if (actual_case_id != 0)
                                out->type = switch_type;
                            else
                            {
                                // TODO: support empty switch later.
                                tokenError(tk, &token1, "cannot assign type to empty switch expression");
                                out->type = 0;
                            }
                        }
                    }
                    else
                        tokenError(tk, &subject_token, "cannot switch over a non-struct");
                }
                else
                    tokenError(tk, "expected subject");
            } break;

            default:
                tokenError(tk, "keyword not part of expression");
        }
    }
    else if (isIdentifier(&token1))
    {
        auto lookup1 = lookupNameRecursive(bindings, &token1);
        if (lookup1.found)
            out = lookup1.value;
        else
            tokenError(tk, "unbound identifier in expression");
    }
    else if (equals(&token1, '('))
    {
        out = parseExpression(state);
        if (parsing(tk))
            requireChar(tk, ')');
    }
    else
        tokenError(tk, "expected start of expression");

    if (parsing(tk))
    {
        Token funcall = peekNext(tk);
        if (equals(&funcall, '('))
        {// function call syntax, let's keep going
            advance(tk);
            auto op = out;
            if (op->type->cat == EC_ArrowType)
            {
                auto arrow = &op->type->ArrowType;
                auto args = pushArray(arena, arrow->arg_count, Expression*);
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
                        auto arg = parseExpression(state);
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
                    if (actual_arg_count == arrow->arg_count)
                    {
                        out = newExpression(arena, EC_Application, 0);
                        auto application = &out->Application;;
                        application->op        = op;
                        application->arg_count = arrow->arg_count;
                        application->args      = args;
                    }
                    else
                        parseError(tk, &funcall, "incorrect arg count: %d (procedure expected %d)", actual_arg_count, arrow->arg_count);
                }
            }
            else
                tokenError(tk, "cannot call non-procedure");
        }
    }

    if (parsing(tk))
    {
        if (out->cat == EC_Application)
        {// Since there are so many ways application can happen, we typecheck it
         // after the fact here. Plus this gets complicated with operator overloading.
            auto app = castExpression(Application, out);
            auto op_signature = castExpression(ArrowType, app->op->type);
            assert(app->arg_count == op_signature->arg_count);
            b32 mismatch_found = false;
            for (int arg_id = 0;
                 (arg_id < app->arg_count) && !mismatch_found;
                 arg_id++)
            {
                auto expected_arg_type = op_signature->args[arg_id]->type;
                auto arg = app->args[arg_id];
                auto compare = expressionsIdentical(expected_arg_type, arg->type);
                if (compare != Trinary_True)
                {
                    mismatch_found = true;
                    parseError(tk, &token1, "argument %d has type mismatch", arg_id);
                    tk->error->attached[tk->error->attached_count++] = {"got", arg->type};
                    tk->error->attached[tk->error->attached_count++] = {"expected", expected_arg_type};
                }
            }

            if (!mismatch_found)
                out->type = op_signature->return_type;
        }
        else
            assert(out->type);
    }
    else
        out = 0;

    popContext(tk);
    return out;
}

internal Stack
extendStack(Stack *outer, u32 arg_count, Expression **args)
{    
    Stack out = {};

    out.depth = outer->depth+1;
    out.arena = outer->arena;
    out.count = arg_count;
    out.first = args;
    out.next  = outer;

    return out;
}

inline Expression *
makeBinopExpression(MemoryArena *arena, Expression *op, Expression *lhs, Expression *rhs,
                    // TODO: get type from the op
                    Expression *type)
{
    Expression *out = newExpression(arena, EC_Application, type);

    out->Application.op        = op;
    out->Application.arg_count = 2;
    allocateArray(arena, 2, out->Application.args);
    out->Application.args[0] = lhs;
    out->Application.args[1] = rhs;
    return out;
}

internal Expression *
reduceExpression(MemoryArena *arena, Stack *stack, Expression *in)
{
    Expression *out = 0;

    switch (in->cat)
    {
        case EC_Variable:
        {
            out = resolve(stack, in->Variable);
        } break;

        case EC_Application:
        {
            auto application = &in->Application;
            Expression **reduced_args = pushArray(arena, application->arg_count, Expression*);
            for (auto arg_id = 0;
                 arg_id < application->arg_count;
                 arg_id++)
            {
                Expression *in_arg   = application->args[arg_id];
                reduced_args[arg_id] = reduceExpression(arena, stack, in_arg);
            }

            Expression *reduced_op = reduceExpression(arena, stack, application->op);
            if (reduced_op->cat == EC_Procedure)
            {
                Stack new_env = extendStack(stack, application->arg_count, reduced_args);
                out = reduceExpression(arena, &new_env, reduced_op->Procedure.body);
            }
            else if (reduced_op->cat == EC_Builtin_Equality)
            {
                assert(application->arg_count == 2);
                auto lhs = reduceExpression(arena, stack, application->args[0]);
                auto rhs = reduceExpression(arena, stack, application->args[1]);
                switch (expressionsIdentical(lhs, rhs))
                {
                    case Trinary_True:
                    {
                        out = &builtin_true;
                    } break;

                    case Trinary_False:
                    {
                        out = &builtin_false;
                    } break;

                    case Trinary_Unknown:
                    {
                        // I must be confident that reduction preserves type
                        out = makeBinopExpression(arena, &builtin_equality, lhs, rhs, &builtin_prop_type);
                    } break;
                }
            }
            else
            {
                out->cat = EC_Application;
                auto app = castExpression(Application, out);
                app->op        = reduced_op;
                app->arg_count = application->arg_count;
                app->args      = reduced_args;
            }
        } break;

        case EC_Switch:
        {
            auto switch0 = &in->Switch;
            Expression *reduced_subject = reduceExpression(arena, stack, switch0->subject);

            auto subject_type = reduced_subject->type;
            assert(subject_type->cat == EC_Struct);
            auto ctor_id = matchSwitchCase(reduced_subject);

            if (ctor_id.success)
                out = reduceExpression(arena, stack, switch0->case_bodies[ctor_id.value]);
            else
                todoIncomplete;
        } break;

        default:
        {
            out = in;
        } break;
    }

    return out;
}

internal Expression *
parseProof(ExpressionParserState *state, Expression *goal)
{
    auto tk = state->tk;
    pushContext(tk);
    auto arena = state->arena;
    auto bindings = state->bindings;

    Expression *out = 0;
    Token token = advance(tk);
    switch (token.cat)
    {
        case TC_KeywordSwitch:
        {
            auto switch_subject = parseExpression(state);
            if (parsing(tk) && requireChar(tk, '.'))
            {
                out = newExpression(arena, EC_Switch, 0);
                auto myswitch = &out->Switch;
                myswitch->subject = switch_subject;
                auto subject_type = switch_subject->type;
                if (!subject_type)
                    tokenError(tk, "cannot infer subject type");
                else if (subject_type->cat != EC_Struct)
                    tokenError(tk, "cannot switch on non-structs");
                else
                {
                    auto subject_struct = &subject_type->Struct;
                    auto ctor_count = subject_struct->ctor_count;
                    allocateArray(arena, ctor_count, myswitch->case_bodies);
                    for (s32 ctor_id = 0;
                         (ctor_id < ctor_count) && parsing(tk);
                         ctor_id++)
                    {
                        if (requireChar(tk, '-'))
                        {
                            // TODO: maybe memory leak
                            Stack stack = {};
                            stack.arena = arena;
                            // TODO: what to do with the stack?
                            Expression *subgoal = reduceExpression(arena, &stack, goal);
                            Expression *subproof = parseProof(state, subgoal);
                        }
                        else
                            tokenError(tk, "please begin subproof with '-'");
                    }
                }
            }
        } break;

        case TC_KeywordReturn:
        {
            Token return_token = peekNext(tk);
            Expression *returned = parseExpression(state);
            if (parsing(tk))
            {
                if (!returned->type)
                    tokenError(tk, &return_token, "failed to infer type");
                else if (expressionsIdentical(returned->type, goal)
                         != Trinary_True)
                {
                    parseError(tk, &return_token, "returned expression doesn't have the correct type");
                    auto error_buffer = &tk->error->message;
                    myprint(error_buffer, "returned type: ");
                    printExpression(error_buffer, returned->type);
                    myprint(error_buffer, ", actual goal: ");
                    printExpression(error_buffer, goal);
                }
                else
                    out = returned;
            }
            optionalChar(tk, '.');
        } break;
    }

    popContext(tk);
    return out;
}

internal void
parseDefine(ParserState *state, MemoryArena *arena, b32 is_theorem = false)
{
    Tokenizer *tk = &state->tokenizer;
    pushContext(tk);

    Token define_name = advance(tk);
    if ((define_name.cat == TC_Alphanumeric)
        || (define_name.cat == TC_Special))
    {
        auto define_slot = lookupNameCurrentFrame(&state->global_bindings, define_name.text, true);
        if (define_slot.found)
            tokenError(tk, "re-definition");
        else
        {
            auto  define_type       = newExpression(arena, EC_ArrowType, &builtin_proc_type);
            auto *define_exp        = newExpression(arena, EC_Procedure, define_type);
            define_slot.slot->value = define_exp;
            auto proc  = &define_exp->Procedure;
            proc->name = define_name.text;

            auto signature = &define_type->ArrowType;

            requireChar(tk, '(');

            s32 arg_count = 0;
            {// peek ahead to get the arg count
                Tokenizer tk1_ = *tk;
                Tokenizer *tk1 = &tk1_;
                s32 nesting_depth = 0;
                b32 previous_is_comma = false;
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
                            if (!previous_is_comma)
                                arg_count++;
                            stop = true;
                        }
                    }
                    else if ((nesting_depth == 0)
                             && (equals(&token, ',')))
                    {
                        arg_count++;
                        current_is_comma = true;
                    }
                    previous_is_comma = current_is_comma;
                }
            }
            signature->arg_count = arg_count;
            allocateArray(arena, arg_count, signature->args);

            MemoryArena scoped_arena = beginTemporaryArena(&state->scoped_arena);
            Bindings *local_bindings = extendBindings(&scoped_arena, &state->global_bindings);
            for (s32 arg_id = 0, stop = 0; !stop; arg_id++)
            {// parsing arguments
                Token arg_name_or_end = advance(tk);
                if (equals(&arg_name_or_end, ')'))
                    stop = true;

                else if (arg_name_or_end.cat == TC_Alphanumeric)
                {
                    auto arg_name_lookup = lookupNameCurrentFrame(local_bindings, arg_name_or_end.text, true);
                    if (arg_name_lookup.found)
                        tokenError(tk, "duplicate arg name");
                    else
                    {
                        auto arg_exp = newExpression(arena, EC_Variable, 0);
                        arg_name_lookup.slot->value = arg_exp;

                        arg_exp->Variable.name        = arg_name_or_end.text;
                        arg_exp->Variable.id          = arg_id;
                        arg_exp->Variable.stack_depth = 1;

                        requireChar(tk, ':');

                        Expression *arg_type = parseExpression(arena, local_bindings, tk);
                        arg_exp->type        = arg_type;
                        signature->args[arg_id] = arg_exp;

                        Token delimiter = advance(tk);
                        if (equals(&delimiter, ')'))
                            stop = true;
                        else if (!equals(&delimiter, ','))
                            tokenError(tk, "unexpected token after arg type");
                    }
                }
                else
                    tokenError(tk, "expected arg name");

                if (stop)
                    assert(arg_id = arg_count);
            }

            // return type
            requireChar(tk, ':');
            signature->return_type = parseExpression(arena, local_bindings, tk);
            if (parsing(tk) && requireChar(tk, '{'))
            {
                Token body_token = peekNext(tk);
                ExpressionParserState exp_state = {arena, local_bindings, tk};
                Expression *body = is_theorem ?
                    parseProof(&exp_state, signature->return_type) :
                    parseExpression(&exp_state);
                if (parsing(tk) && requireChar(tk, '}'))
                {
                    proc->body = body;

                    if (!is_theorem)
                    {
                        auto body_type = proc->body->type;
                        if (body_type != signature->return_type)
                            tokenError(tk, &body_token, "body has wrong type");
                    }
                }
            }
                
            endTemporaryArena(&scoped_arena);
        }
    }
    else
        tokenError(tk, "expected a name to be defined");

    popContext(tk);
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(ParserState *state, MemoryArena *arena)
{
    Tokenizer *tk = &state->tokenizer;
    pushContext(tk);

    while (parsing(tk))
    {
        Token token = advance(tk); 
        switch (token.cat)
        {
            case TC_KeywordTypedef:
                parseTypedef(state, arena);
                break;

            case TC_KeywordDefine:
                parseDefine(state, arena);
                break;

            case TC_KeywordTheorem:
                parseDefine(state, arena, true);
                break;

            case TC_KeywordPrint:
            case TC_KeywordPrintRaw:
            case TC_KeywordAssert:
            case TC_KeywordAssertFalse:
            {
                b32 should_print = ((token.cat == TC_KeywordPrintRaw)
                                     || (token.cat == TC_KeywordPrint));

                requireChar(tk, '(');
                auto temp_arena = beginTemporaryArena(arena);
                {
                    auto arena = &temp_arena;

                    ExpressionParserState exp_state = {};
                    exp_state.bindings  = &state->global_bindings;
                    exp_state.tk = tk;
                    exp_state.arena     = arena;
                    auto exp = parseExpression(&exp_state);

                    if (parsing(tk) && requireChar(tk, ')'))
                    {
                        MemoryArena buffer = {};

                        Stack empty_stack = {};
                        empty_stack.arena = arena;
                        Expression *reduced = reduceExpression(arena, &empty_stack, exp);

                        if (should_print)
                        {
                            buffer = subArena(arena, 256);
                            {
                                if (token.cat == TC_KeywordPrint)
                                    printExpression(&buffer, reduced, true);
                                else
                                    printExpression(&buffer, exp, true);
                            }
                            printf("%s\n", buffer.base);
                        }
                        else if (token.cat == TC_KeywordAssert)
                        {
                            if (reduced->cat != EC_Builtin_True)
                                parseError(tk, &token, "assertion failed");
                        }
                        else
                        {
                            assert(token.cat == TC_KeywordAssertFalse);
                            if (reduced->cat != EC_Builtin_False)
                                parseError(tk, &token, "assertion failed");
                        }
                    }
                }
                endTemporaryArena(&temp_arena);
            } break;

            case 0: break;

            default:
                tokenError(tk, "unexpected token at top-level");
        }
    }

    popContext(tk);
}

inline b32
isMatchingPair(Token *left, Token *right)
{
    char l = left->text.chars[0];
    char r = right->text.chars[0];
    return (((l == '(') && (r == ')')) ||
            ((l == '{') && (r == '}')));
}

struct CompileOutput { ParserState *state; b32 success; };

internal CompileOutput
compile(MemoryArena *arena, char *input, char *input_file)
{
    b32 success = 0;

    ParserState *state = pushStruct(arena, ParserState);

    {// mark: initialize state
        state->scoped_arena          = subArena(arena, megaBytes(2));
        state->global_bindings.arena = arena;
        state->tokenizer             = {};
        state->tokenizer.error_arena = subArena(arena, kiloBytes(8));
        state->tokenizer.line_number = 1;
        state->tokenizer.column      = 1;
        state->tokenizer.at          = input;

        auto lookupequal = lookupNameCurrentFrame(&state->global_bindings, toString("="), true);
        auto lookuptrue  = lookupNameCurrentFrame(&state->global_bindings, toString("true"), true);
        auto lookupfalse = lookupNameCurrentFrame(&state->global_bindings, toString("false"), true);

        lookupequal.slot->value = &builtin_equality;
        lookuptrue.slot->value  = &builtin_true;
        lookupfalse.slot->value = &builtin_false;
    }

    parseTopLevel(state, arena);
    ParseError error = state->tokenizer.error;
    if (error)
    {
        success = 1;
        printf("%s:%d:%d: [%s] %s",
               input_file,

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

    return CompileOutput{ state, success, };
}

inline int
testCaseCompile(MemoryArena *arena, char *input_file)
{
    int out = 0;
    ReadFileResult read = platformReadEntireFile(input_file);
    if (read.content)
    {
        auto [state, success] = compile(arena, read.content, input_file);
        out = success;
        platformFreeFileMemory(read.content);
    }
    else
    {
        printf("Failed to read input file %s", input_file);
        out = 1;
    }
    return out;
}

int
engineMain(EngineMemory *memory)
{
    assert(arrayCount(keywords) == TC_KeywordsEnd_ - TC_KeywordsBegin_);

    int out = 0;
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    builtin_equality.cat  = EC_Builtin_Equality;
    builtin_true.cat      = EC_Builtin_True;
    builtin_false.cat     = EC_Builtin_False;
    builtin_set_type.cat  = EC_Builtin_Set_Type;
    builtin_prop_type.cat = EC_Builtin_Prop_Type;
    builtin_proc_type.cat = EC_Builtin_Proc_Type;

    auto arena = newArena(memory->storage_size, memory->storage);

    if (testCaseCompile(&arena, "..\\data\\test\\operator.rea"))
        out = 1;

    zeroMemory(memory->storage, memory->storage_size);
    if (testCaseCompile(&arena, "..\\data\\test.rea"))
        out = 1;

    return out;
}

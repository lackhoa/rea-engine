#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"

#include <stdio.h>

// TODO: Eventually this will talk to the editor, but let's work in console mode for now.

enum ExpressionCategory
{
    EC_Variable,                // reference to some unknown on "the stack"
    EC_Application,             // operator application
    EC_Switch,                  // switch statement
    EC_Type,                    // type information
    EC_Procedure,               // holds actual computation (ie body that can be executed)
    EC_ConstructorId,           // reference to a constructor of a type

    EC_Builtin_Equality,        // computational meta-equality
    EC_Builtin_True,
    EC_Builtin_False,
};

#define castExpression(Type, exp, type) Type *type = &exp->Type;

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
struct Type
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
    u32     arg_count;
    Type   *arg_types;
};

// NOTE: we need the id to arrange the switch body. otw it's just a pointer.
struct ConstructorId
{
    u32   id;
};

struct Procedure
{
    String       name;
    s32          arg_count;
    Type       **arg_types;
    Type        *return_type;
    Expression  *body;
};

struct Expression
{
    ExpressionCategory  cat;
    Type               *type_of_this;
    union
    {
        Variable       Variable;
        Application    Application;
        Switch         Switch;
        Type           Type;
        Procedure      Procedure;
        ConstructorId  ConstructorId;
    };
};

Expression builtin_equality;
Expression builtin_true;
Expression builtin_false;

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
    Tokenizer   *tokenizer;
    MemoryArena *arena;
    Bindings    *bindings;
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
parseConstructorDef(ParserState *state, MemoryArena *arena, Type *type, s32 ctor_id)
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
                todoErrorReport;
            else
            {
                out.name      = ctor_token.text;
                // todo: incomplete
                out.arg_count = 0;
                out.arg_types = 0;

                Expression *exp = pushStruct(arena, Expression);
                exp->cat          = EC_ConstructorId;
                exp->type_of_this = type;
                castExpression(ConstructorId, exp, ctor_ref);
                ctor_ref->id   = ctor_id;

                ctor_lookup.slot->value = exp;
            }
        } break;

        default:
            todoErrorReport;
    }
    return out;
}

internal void
parseError(Tokenizer *tk, Token *token, char *format, ...)
{
    auto arena = &tk->error_arena;
    allocate(arena, tk->error);
    s32 message_length = strlen(format) + 1;
    tk->error->message = subArena(&tk->error_arena, 256);

    va_list arg_list;
    __crt_va_start(arg_list, format);
    printToBuffer(&tk->error->message, format, arg_list);
    __crt_va_end(arg_list);

    tk->error->token = *token;
}

internal void
tokenError(Tokenizer *tk, char *message, Token *token)
{
    auto arena = tk->error_arena;
    parseError(tk, token, message);
    printToBuffer(&tk->error->message, ": ");
    printToBuffer(&tk->error->message, token->text);
}

internal void
tokenError(Tokenizer *tk, char *message)
{
    tokenError(tk, message, &tk->last_token);
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
            Expression *type_exp    = pushStruct(arena, Expression);
            type_lookup.slot->value = type_exp;
            type_exp->cat           = EC_Type;

            Type *type = &type_exp->Type;
            type->name = type_name.text;

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

            allocateArray(arena, expected_case_count, type->ctors);

            s32 actual_case_count = 0;
            for (s32 stop = 0, constructor_id = 0; !stop; constructor_id++)
            {
                Token bar_or_stop = advance(tk);
                if (equals(&bar_or_stop, '}'))
                    stop = true;
                else if (equals(&bar_or_stop, '|'))
                {
                    type->ctors[constructor_id] = parseConstructorDef(state, arena, type, constructor_id);
                    actual_case_count++;
                }
                else
                    parseError(tk, &bar_or_stop, "Expected '|' or '}'");
            }
            assert(actual_case_count == expected_case_count);
            type->ctor_count = actual_case_count;

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
matchSwitchCase(Type *subject_type, Expression *matched)
{
    OptionalU32 out = {};

    if (matched)
    {
        if (matched->cat == EC_Variable)
        {}  // surrender
        else if (matched->cat == EC_ConstructorId)
        {
            auto ctor   = matched->ConstructorId;
            out.success = true;
            out.value   = ctor.id;
        }
        else
            todoIncomplete;  // handle composite cases
    }
    
    return out;
}

internal Type *
inferType(Expression *exp)
{
    Type *out = 0;

    if (exp->type_of_this)
        out = exp->type_of_this;
    else
    {
        switch (exp->cat)
        {
            case EC_Variable:
            {
                invalidCodePath;  // this should already have the type
            } break;

            case EC_Application:
            {
                todoIncomplete;
            } break;

            case EC_Switch:
            {
                todoIncomplete;
            } break;

            case EC_Type:
            {
                // higher-order type
                todoIncomplete;
            } break;

            case EC_Procedure:
            {
                // another arrow type
                todoIncomplete;
            } break;

            case EC_ConstructorId:
            {
                // yet another arrow type
                todoIncomplete;
            } break;
        }
    }
        
    return out;
}

inline b32
isExpressionEndMarker(Token *token)
{
    return inString("{},)", token);
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
parseExpressionContinue(ExpressionParserState *state, Expression *left, s32 min_precedence, Expression **hole)
{
    Tokenizer   *tk       = state->tokenizer;
    MemoryArena *arena    = state->arena;
    Bindings    *bindings = state->bindings;

    Expression *out = 0;

    Expression *arg0 = parseOperand(state);
    if (arg0)
    {
        // (a+b) * c
        //       ^
        Token op_token = peekNext(tk);
        if (isIdentifier(&op_token))
        {// infix operator syntax
            advance(tk);
            // (a+b) * c
            //         ^
            auto op_lookup = lookupNameRecursive(bindings, &op_token);
            if (op_lookup.found)
            {
                auto op = op_lookup.value;

                Expression *app_exp = pushStruct(arena, Expression);
                app_exp->cat        = EC_Application;
                auto        app     = &app_exp->Application;

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
                        //       ^
                        app->args[0] = arg0;
                        *hole = app_exp;
                        out = parseExpressionContinue(state, left, min_precedence, app->args+1);
                    }
                    else
                    {
                        // a * b + c
                        //       ^
                        *hole = arg0;
                        app->args[0] = left;
                        out = parseExpressionContinue(state, app_exp, precedence, app->args+1);
                    }
                }
                else
                {
                    app->args[0] = arg0;
                    out = parseExpressionContinue(state, app_exp, precedence, app->args+1);
                }
            }
            else
                tokenError(tk, "unbound operator", &op_token);
        }
        else if (isExpressionEndMarker(&op_token))
        {
            if (left)
            {
                *hole = arg0;
                out = left;
            }
            else
                out = arg0;
        }
        else
            tokenError(tk, "expected operator token, got:", &op_token);
    }
    else if (parsing(tk))
        invalidCodePath; // e1 must have failed

    return out;
}

inline Expression *
parseExpression(ExpressionParserState *state)
{
    return parseExpressionContinue(state, 0, 0, 0);
}

// a subexpression is like the '+' or the 'a' in the full expression 'a + b'
internal Expression *
parseOperand(ExpressionParserState *state)
{
    Tokenizer   *tk       = state->tokenizer;
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
                allocate(arena, out);
                out->cat = EC_Switch;
                castExpression(Switch, out, switch0);

                switch0->subject = parseExpression(state);
                requireChar(tk, '{');
                if (switch0->subject)
                {
                    Type *subject_type = inferType(switch0->subject);
                    auto expected_ctor_count = subject_type->ctor_count;
                    allocateArray(arena, expected_ctor_count, switch0->case_bodies);

                    s32 actual_case_count = 0;
                    for (b32 stop = false; !stop;)
                    {
                        Token bar_or_closing_brace = advance(tk);
                        switch (bar_or_closing_brace.text.chars[0])
                        {
                            case '|':
                            {
                                actual_case_count++;

                                MemoryArena temp_arena = beginTemporaryArena(arena);

                                auto new_state = *state;
                                new_state.arena = &temp_arena;
                                Expression *switch_case = parseExpression(state);
                                requireChar(tk, '{');

                                auto case_match = matchSwitchCase(subject_type, switch_case);
                                endTemporaryArena(&temp_arena);

                                if (case_match.success)
                                {
                                    auto body = parseExpression(state);
                                    requireChar(tk, '}');

                                    // todo: type-check the body
                                    if (body)
                                        switch0->case_bodies[case_match.value] = body;
                                    else
                                        todoErrorReport;  // body cannot be empty
                                }
                                else
                                    todoErrorReport;  // expression is not a constructor for type.
                            } break;

                            case '}':
                            {
                                stop = true;
                            } break;

                            default:
                                todoErrorReport;  // expect either '|' or '}'
                        }
                    }
                    if (actual_case_count != expected_ctor_count)
                        todoErrorReport; // wrong number of cases
                }
                else
                    todoErrorReport;  // expected subject
            } break;

            default:
                todoErrorReport; // keyword not part of expression
        }
    }
    else if (isIdentifier(&token1))
    {
        auto lookup1 = lookupNameRecursive(bindings, &token1);
        if (lookup1.found)
            out = lookup1.value;
        else
            todoErrorReport;    // Unbound identifier
    }
    else if (equals(&token1, '('))
    {
        out = parseExpression(state);
        requireChar(tk, ')');
    }
    else
        todoErrorReport;  // expected start of expression

    Token next = peekNext(tk);
    if (equals(&next, '('))
    {// function call syntax, let's keep going
        advance(tk);
        auto op = out;
        auto todo_arg_count = 2;  // this requires knowing the type of the operator
        auto args = pushArray(arena, todo_arg_count, Expression*);
        s32 actual_arg_count = 0;
        for(s32 stop = false, arg_id = 0;
            !stop;
            arg_id++)
        {
            auto arg = parseExpression(state);
            if (!arg)
                stop = true;
            else
                args[arg_id] = arg;

            for (b32 non_comma = false; !non_comma;)
            {// eat all commas for now
                if (*tk->at == ',')
                    advance(tk);
                else
                    non_comma = true;
            }

            if (stop)
                actual_arg_count = arg_id;
        }
        requireChar(tk, ')');

        if (actual_arg_count == todo_arg_count)
        {
            allocate(arena, out);
            out->cat = EC_Application;
            castExpression(Application, out, application);
            application->op        = op;
            application->arg_count = todo_arg_count;
            application->args      = args;
        }
        else
            todoErrorReport;  // incorrect arg count
    }

    return out;
}

internal Type  *
parseType(ParserState *state, Bindings *bindings)
{
    Tokenizer *tk = &state->tokenizer;
    Type *out = 0;

    Token type = advance(tk);
    if (type.cat == TC_Alphanumeric)
    {
        auto type_lookup = lookupNameRecursive(bindings, &type);
        if (type_lookup.found)
        {
            if (type_lookup.value->cat == EC_Type)
                out = &type_lookup.value->Type;
            else
                todoErrorReport; // not a type
        }
        else
            todoErrorReport; // type not found.
    }
    else
        todoErrorReport; // expected a type here

    return out;
}

internal Stack
extendEnvironment(Stack *outer, u32 arg_count, Expression **args)
{    
    Stack out = {};

    out.depth = outer->depth+1;
    out.arena = outer->arena;
    out.count = arg_count;
    out.first = args;
    out.next  = outer;

    return out;
}

internal void
parseDefine(ParserState *state, MemoryArena *arena)
{
    Tokenizer *tk = &state->tokenizer;
    Token define_name = advance(tk);
    if ((define_name.cat == TC_Alphanumeric)
        || (define_name.cat == TC_Special))
    {
        auto define_slot = lookupNameCurrentFrame(&state->global_bindings, define_name.text, true);
        if (define_slot.found)
            todoErrorReport;
        else
        {
            auto *define_exp        = pushStruct(arena, Expression);
            define_slot.slot->value = define_exp;

            define_exp->cat = EC_Procedure;
            auto procedure  = &define_exp->Procedure;
            procedure->name = define_name.text;

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
            procedure->arg_count = arg_count;
            allocateArray(arena, arg_count, procedure->arg_types);

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
                        todoErrorReport;  // Duplicate arg name
                    else
                    {
                        Expression *arg_exp         = pushStruct(arena, Expression);
                        arg_name_lookup.slot->value = arg_exp;

                        arg_exp->cat = EC_Variable;
                        arg_exp->Variable.name        = arg_name_or_end.text;
                        arg_exp->Variable.id          = arg_id;
                        arg_exp->Variable.stack_depth = 1;

                        requireChar(tk, ':');

                        Type *arg_type               = parseType(state, local_bindings);
                        procedure->arg_types[arg_id] = arg_type;
                        arg_exp->type_of_this        = arg_type;

                        Token delimiter = advance(tk);
                        if (equals(&delimiter, ')'))
                            stop = true;
                        else if (!equals(&delimiter, ','))
                            todoErrorReport;  // no comma after type
                    }
                }
                else
                    todoErrorReport;  // expected arg name

                if (stop)
                    assert(arg_id = arg_count);
            }

            // return type
            requireChar(tk, ':');
            procedure->return_type = parseType(state, local_bindings);

            requireChar(tk, '{');
            allocate(arena, procedure->body);
            ExpressionParserState exp_state = {};
            exp_state.arena = arena;
            exp_state.bindings = local_bindings;
            exp_state.tokenizer = tk;
            auto body = parseExpression(&exp_state);
            requireChar(tk, '}');
            if (body)
                procedure->body = body;
            else
                todoErrorReport;  // empty procedure body.

            endTemporaryArena(&scoped_arena);
        }
    }
    else
        todoErrorReport;
}

inline Expression *
makeBinopExpression(MemoryArena *arena, Expression *op, Expression *lhs, Expression *rhs)
{
    Expression *out = pushStruct(arena, Expression);
    out->cat = EC_Application;
    out->Application.op        = op;
    out->Application.arg_count = 2;
    allocateArray(arena, 2, out->Application.args);
    out->Application.args[0] = lhs;
    out->Application.args[1] = rhs;
    return out;
}

enum TrinaryValue
{
    Trinary_True, Trinary_False, Trinary_Unknown,
};

inline TrinaryValue
reduceEquality(Expression *lhs, Expression *rhs)
{
    TrinaryValue out = Trinary_Unknown;

    if (lhs->cat == rhs->cat)
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

            case EC_ConstructorId:
            {
                if (lhs->ConstructorId.id == rhs->ConstructorId.id)
                    out = Trinary_True;
                else
                    out = Trinary_False;
            } break;

            default:
                todoIncomplete;
        }
    }

    return out;
}

internal Expression *
reduce(ParserState *state, MemoryArena *arena, Stack *stack, Expression *in)
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
            allocate(arena, out);
            auto application = &in->Application;
            Expression **reduced_args = pushArray(arena, application->arg_count, Expression*);
            for (auto arg_id = 0;
                 arg_id < application->arg_count;
                 arg_id++)
            {
                Expression *in_arg   = application->args[arg_id];
                reduced_args[arg_id] = reduce(state, arena, stack, in_arg);
            }

            Expression *reduced_op = reduce(state, arena, stack, application->op);
            if (reduced_op->cat == EC_Procedure)
            {
                Stack new_env = extendEnvironment(stack, application->arg_count, reduced_args);
                out = reduce(state, arena, &new_env, reduced_op->Procedure.body);
            }
            else if (reduced_op->cat == EC_Builtin_Equality)
            {
                assert(application->arg_count == 2);
                auto lhs = reduce(state, arena, stack, application->args[0]);
                auto rhs = reduce(state, arena, stack, application->args[1]);
                switch (reduceEquality(lhs, rhs))
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
                        out = makeBinopExpression(arena, &builtin_equality, lhs, rhs);
                    } break;
                }
            }
            else
            {
                out->cat = EC_Application;
                castExpression(Application, out, app);
                app->op        = reduced_op;
                app->arg_count = application->arg_count;
                app->args      = reduced_args;
            }
        } break;

        case EC_Switch:
        {
            auto switch0 = &in->Switch;
            Expression *reduced_subject = reduce(state, arena, stack, switch0->subject);

            Type *subject_type = reduced_subject->type_of_this;
            auto ctor_id = matchSwitchCase(subject_type, reduced_subject);

            if (ctor_id.success)
                out = reduce(state, arena, stack, switch0->case_bodies[ctor_id.value]);
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

internal void
printExpression(MemoryArena *buffer, Expression *exp)
{
    switch (exp->cat)
    {
        case EC_Variable:
        {
            castExpression(Variable, exp, var);
            printToBuffer(buffer, "var %.*s (%d, %d)", var->name.length, var->name.chars, var->stack_depth, var->id);
        } break;

        case EC_Application:
        {
            castExpression(Application, exp, app);

            printExpression(buffer, app->op);

            printToBuffer(buffer, "(");
            for (s32 arg_id = 0; arg_id < app->arg_count; arg_id++)
            {
                printExpression(buffer, app->args[arg_id]);
                if (arg_id < app->arg_count-1)
                    printToBuffer(buffer, ", ");
            }
            printToBuffer(buffer, ")");
        } break;

        case EC_Switch:
        {
            todoIncomplete;
        } break;

        case EC_Type:
        {
            todoIncomplete;
        } break;

        case EC_Procedure:
        {
            castExpression(Procedure, exp, proc);
            printToBuffer(buffer, proc->name);
        } break;

        case EC_ConstructorId:
        {
            Constructor *ctor = exp->type_of_this->ctors + exp->ConstructorId.id;
            printToBuffer(buffer, ctor->name);
        } break;

        case EC_Builtin_Equality:
        {
            printToBuffer(buffer, "=");
        } break;

        case EC_Builtin_True:
        {
            printToBuffer(buffer, "true");
        } break;

        case EC_Builtin_False:
        {
            printToBuffer(buffer, "false");
        } break;

        default:
        {
            printToBuffer(buffer, "<unsupported category>");
        } break;
    }
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(ParserState *state, MemoryArena *arena)
{
    Tokenizer *tk = &state->tokenizer;

    Stack empty_stack = {};
    empty_stack.arena = arena;

    ExpressionParserState exp_parser_state = {};
    exp_parser_state.bindings = &state->global_bindings;
    exp_parser_state.tokenizer = tk;

    for (;parsing(tk);)
    {
        Token token = advance(tk); 
        switch (token.cat)
        {
            case TC_KeywordTypedef:
            {
                parseTypedef(state, arena);
            } break;

            case TC_KeywordDefine:
            {
                parseDefine(state, arena);
            } break;

            case TC_KeywordPrintraw:
            {
                requireChar(tk, '(');
                auto temp_arena = beginTemporaryArena(arena);
                {
                    auto arena = &temp_arena;

                    exp_parser_state.arena = arena;
                    auto exp = parseExpression(&exp_parser_state);
                    requireChar(tk, ')');
                    if (exp)
                    {
                        auto buffer = subArena(arena, 256);
                        printExpression(&buffer, exp);
                        printf("%s\n", buffer.base);
                    }
                    else
                        tokenError(tk, "empty expression passed to 'printraw'");
                }
                endTemporaryArena(&temp_arena);
            } break;

            case TC_KeywordPrint:
            {
                requireChar(tk, '(');
                auto temp_arena = beginTemporaryArena(arena);
                {
                    auto arena = &temp_arena;

                    exp_parser_state.arena = arena;
                    auto exp = parseExpression(&exp_parser_state);

                    requireChar(tk, ')');
                    if (exp)
                    {
                        auto reduced = reduce(state, arena, &empty_stack, exp);
                        auto buffer = subArena(arena, 256);
                        printExpression(&buffer, exp);
                        printToBuffer(&buffer, " => ");
                        printExpression(&buffer, reduced);
                        printf("%s\n", buffer.base);
                    }
                    else
                        tokenError(tk, "empty expression passed to 'print'");
                }
                endTemporaryArena(&temp_arena);
            } break;

            case TC_KeywordAssert:
            {
                if (requireChar(tk, '('))
                {
                    auto temp_arena = beginTemporaryArena(arena);
                    {
                        auto arena = &temp_arena;

                        exp_parser_state.arena = arena;
                        Expression *exp = parseExpression(&exp_parser_state);

                        if (parsing(tk))
                            requireChar(tk, ')');
                        if (exp)
                        {
                            auto reduced = reduce(state, arena, &empty_stack, exp);
                            if (reduced->cat != EC_Builtin_True)
                                parseError(tk, &token, "assertion failed");
                        }
                        else
                            tokenError(tk, "empty expression passed to 'assert'");
                    }
                    endTemporaryArena(&temp_arena);
                }
            } break;

            case 0: break;

            default:
                tokenError(tk, "unexpected token at top-level");
        }
    }
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
    ParserError error = state->tokenizer.error;
    if (error)
    {
        success = 1;
        printf("%s:%d:%d: %s\n", input_file, error->token.line_number, error->token.column, error->message.base);
    }

    return CompileOutput{ state, success, };
}

inline int
testCaseMain(MemoryArena *arena)
{
    int out = 0;
    char *input_file = "..\\data\\test.rea";
    ReadFileResult read = platformReadEntireFile(input_file);
    if (read.content)
    {
        auto [state, success] = compile(arena, read.content, input_file);
        out = success;
        // NOTE: you can put some assertions here.
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
    testWrapper("hello %s", "world");

    int out = 0;
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    builtin_equality.cat = EC_Builtin_Equality;
    builtin_true.cat     = EC_Builtin_True;
    builtin_false.cat    = EC_Builtin_False;

    auto arena = newArena(memory->storage_size, memory->storage);
    if (testCaseMain(&arena))
        out = 1;
    // zeroMemory(memory->storage, memory->storage_size);
    return out;
}

#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"
#include "intrinsics.h"
#include "tokenization.cpp"

#include <stdio.h>

// TODO: Eventually this will talk to the editor, but let's work in console mode for now.

enum ExpCat
{
    ExpCat_Variable,            // reference to some unknown on "the stack"
    ExpCat_Application,         // operator application
    ExpCat_Switch,              // switch statement
    ExpCat_Type,                // type information
    ExpCat_Procedure,           // holds actual computation (ie body that can be executed)
    ExpCat_ConstructorRef,      // reference to a constructor of a type
};

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
    Expression *args;
};

struct Switch
{
    Expression *subject;
    Expression *case_bodies;
};

struct Constructor;
struct Type
{
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
struct ConstructorRef
{
    Type *type;
    u32   id;
};

struct Procedure
{
    String       name;
    s32          arg_count;
    Type       **arg_types;
    Type        *return_type;
    Expression  *body;  // todo: this shouldn't be a pointer. I guess procedures
                        // shouldn't actually be expressions.
};

struct Expression
{
    ExpCat  cat;
    Type   *type_of_this;       // temporary pointer
    // todo: these should all be pointers. Saves space, but do they though b/c
    // expressions are always pointers anyway.
    union
    {
        Variable       variable;
        Application    apply;
        Switch         switch0;
        Type           type;
        Procedure      procedure;
        ConstructorRef constructor_ref;
    };
};

typedef u32 AtomId;
struct Binding
{
    String      key;
    Expression *value;
    Binding    *next;
};

struct Bindings
{
    u32          stack_depth;
    MemoryArena *arena;
    Binding      first[128];
    Bindings    *next;
};

struct Stack
{
    u32          depth;
    MemoryArena *arena;
    u32          count;
    Expression  *first;
    Stack       *next;
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

struct EngineState
{
    MemoryArena scoped_arena;   // used for storing e.g stack frames

    Bindings    global_bindings;
};

struct LookupName { Binding* slot; b32 found; };

internal LookupName
lookupNameCurrentFrame(Bindings *bindings, Token *token, b32 add_if_missing = false)
{
    String key = token->text;
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
lookupNameRecursive(Bindings *bindings, Token *key)
{
    Expression *value = 0;
    b32 found = false;

    for (b32 stop = false;
         !stop;
         )
    {
        LookupName lookup = lookupNameCurrentFrame(bindings, key, false);
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

internal void
parseConstructorDef(EngineState *state, MemoryArena *arena, Tokenizer *tk, Type *type, s32 ctor_id, Constructor *out)
{
    Token ctor_token = advance(tk);
    switch (ctor_token.cat)
    {
        case TokenCat_Special:
        case TokenCat_Alphanumeric:
        {
            LookupName ctor_lookup = lookupNameCurrentFrame(&state->global_bindings, &ctor_token, true);
            if (ctor_lookup.found)
                todoErrorReport;
            else
            {
                out->name      = ctor_token.text;
                out->arg_count = 0;
                out->arg_types = 0;

                Expression *exp = pushStruct(arena, Expression);
                exp->cat        = ExpCat_ConstructorRef;
                exp->constructor_ref.type = type;
                exp->constructor_ref.id   = ctor_id;

                ctor_lookup.slot->value = exp;
            }
        } break;

        default:
            todoErrorReport;
    }
}

internal void
parseTypedef(EngineState *state, MemoryArena *arena, Tokenizer *tk)
{
    Token type_name = advance(tk);
    if (type_name.cat == TokenCat_Alphanumeric)
    {
        // NOTE: the type is in scope of its own constructor.
        LookupName type_lookup = lookupNameCurrentFrame(&state->global_bindings, &type_name, true);
        if (type_lookup.found)
            todoErrorReport;
        else
        {
            Expression *type_exp    = pushStruct(arena, Expression);
            type_lookup.slot->value = type_exp;
            type_exp->cat           = ExpCat_Type;
            Type       *type        = &type_exp->type;

            requireChar(tk, '{');

            s32 expected_case_count = 0;
            {// peek ahead to get the case count. this code can be crappy since
             // the real error checking is done later.
                Tokenizer tk1 = *tk;
                s32 nesting_depth = 0;
                for (b32 stop = false; !stop;)
                {
                    Token token = advance(&tk1);
                    if (token.cat == TokenCat_PairingOpen)
                        nesting_depth++;
                    else if (token.cat == TokenCat_PairingClose)
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
                    parseConstructorDef(state, arena, tk, type, constructor_id, type->ctors + constructor_id);
                    actual_case_count++;
                }
                else
                    todoErrorReport;  // expected '|' or '}'
            }
            assert(actual_case_count == expected_case_count);
            type->ctor_count = actual_case_count;
        }
    }
    assert(lookupNameCurrentFrame(&state->global_bindings, &type_name).found);
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
    Expression *out = stack->first + variable.id;
    return out;
}

internal OptionalU32
matchSwitchCase(EngineState *state, Type *subject_type, Expression *matched)
{
    OptionalU32 out = {};

    if (matched->cat == ExpCat_Variable)
    {}  // surrender
    else if (matched->cat == ExpCat_ConstructorRef)
    {
        auto ctor   = matched->constructor_ref;
        out.success = true;
        out.value   = ctor.id;
    }
    else
        todoIncomplete;  // handle composite cases

    return out;
}

internal Type *
inferType(EngineState *state, Expression *exp)
{
    Type *out = 0;

    if (exp->type_of_this)
        out = exp->type_of_this;
    else
    {
        switch (exp->cat)
        {
            case ExpCat_Variable:
            {
                invalidCodePath;  // this should already have the type
            } break;

            case ExpCat_Application:
            {
                todoIncomplete;
            } break;

            case ExpCat_Switch:
            {
                todoIncomplete;
            } break;

            case ExpCat_Type:
            {
                // higher-order type
                todoIncomplete;
            } break;

            case ExpCat_Procedure:
            {
                // another arrow type
                todoIncomplete;
            } break;

            case ExpCat_ConstructorRef:
            {
                // yet another arrow type
                todoIncomplete;
            } break;
        }
    }
        
    return out;
}

// todo: is the 'Expression *out' thing wise?  sometimes we want to write to a
// specific address, other times we just wanna return references.
internal void
parseExp(EngineState *state, MemoryArena *arena, Bindings *bindings, Tokenizer *tk, Expression *out)
{
    Token first = advance(tk);
    if (isKeyword(&first))
    {
        switch (first.cat)
        {
            case TokenCat_KeywordSwitch:
            {
                out->cat = ExpCat_Switch;
                allocate(arena, out->switch0.subject);
                parseExp(state, arena, bindings, tk, out->switch0.subject);
                requireChar(tk, '{');
                Type *subject_type = inferType(state, out->switch0.subject);
                auto expected_ctor_count = subject_type->ctor_count;
                allocateArray(arena, expected_ctor_count, out->switch0.case_bodies);

                s32 actual_case_count = 0;
                for (b32 stop = false; !stop;)
                {
                    Token bar_or_closing_brace = advance(tk);
                    switch (bar_or_closing_brace.text.chars[0])
                    {
                        case '|':
                        {
                            actual_case_count++;
                            Expression switch_case = {};
                            parseExp(state, arena, bindings, tk, &switch_case);
                            requireChar(tk, '{');
                            auto case_match = matchSwitchCase(state, subject_type, &switch_case);
                            if (case_match.success)
                            {
                                parseExp(state, arena, bindings, tk, out->switch0.case_bodies + case_match.value);
                                requireChar(tk, '}');
                                // todo: type-check the body
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
                assert(actual_case_count = expected_ctor_count);
            } break;

            default:
                todoErrorReport; // keyword not part of expression
        }
    }
    else if ((first.cat == TokenCat_Alphanumeric)
             || (first.cat == TokenCat_Special))
    {
        LookupNameRecursive identifier_lookup = lookupNameRecursive(bindings, &first);
        if (identifier_lookup.found)
        {
            *out = *identifier_lookup.value;
        }
        else
            todoErrorReport;    // Unbound identifier
    }
    else
        todoErrorReport;        // unexpected start of expression
}

internal Type  *
parseType(EngineState *state, Bindings *bindings, Tokenizer *tk)
{
    Type *out = 0;

    Token type = advance(tk);
    if (type.cat == TokenCat_Alphanumeric)
    {
        auto type_lookup = lookupNameRecursive(bindings, &type);
        if (type_lookup.found)
        {
            if (type_lookup.value->cat == ExpCat_Type)
                out = &type_lookup.value->type;
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
extendEnvironment(Stack *outer, u32 arg_count, Expression *reduced_args)
{    
    Stack out = {};

    out.depth       = outer->depth+1;
    out.arena       = outer->arena;
    out.count         = arg_count;
    out.first = reduced_args;
    out.next        = outer;

    return out;
}

internal void
parseDefine(EngineState *state, MemoryArena *arena, Tokenizer *tk)
{
    Token define_name = advance(tk);
    if ((define_name.cat == TokenCat_Alphanumeric)
        || (define_name.cat == TokenCat_Special))
    {
        auto define_slot = lookupNameCurrentFrame(&state->global_bindings, &define_name, true);
        if (define_slot.found)
            todoErrorReport;
        else
        {
            auto *define_exp        = pushStruct(arena, Expression);
            define_slot.slot->value = define_exp;
            define_exp->cat         = ExpCat_Procedure;
            auto  procedure         = &define_exp->procedure;

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

                else if (arg_name_or_end.cat == TokenCat_Alphanumeric)
                {
                    auto arg_name_lookup = lookupNameCurrentFrame(local_bindings, &arg_name_or_end, true);
                    if (arg_name_lookup.found)
                        todoErrorReport;  // Duplicate arg name
                    else
                    {
                        Expression *arg_exp         = pushStruct(arena, Expression);
                        arg_name_lookup.slot->value = arg_exp;

                        arg_exp->cat = ExpCat_Variable;
                        arg_exp->variable.name        = arg_name_or_end.text;
                        arg_exp->variable.id          = arg_id;
                        arg_exp->variable.stack_depth = 1;

                        requireChar(tk, ':');

                        Type *arg_type               = parseType(state, local_bindings, tk);
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
            procedure->return_type = parseType(state, local_bindings, tk);

            requireChar(tk, '{');
            allocate(arena, procedure->body);
            parseExp(state, arena, local_bindings, tk, procedure->body);
            requireChar(tk, '}');

            endTemporaryArena(&state->scoped_arena, &scoped_arena);
        }
    }
    else
        todoErrorReport;
}

internal void
reduce(EngineState *state, MemoryArena *arena, Stack *stack, Expression *in, Expression *out)
{
    out->cat = in->cat;  // assume that we can't reduce this.
    out->type_of_this = in->type_of_this;

    switch (in->cat)
    {
        case ExpCat_Variable:
        {
            *out = *resolve(stack, in->variable);
        } break;

        case ExpCat_Application:
        {
            auto apply = &in->apply;
            Expression *reduced_args = pushArray(arena, apply->arg_count, Expression);
            for (auto arg_id = 0;
                 arg_id < apply->arg_count;
                 arg_id++)
            {
                auto in_arg      = apply->args + arg_id;
                auto reduced_arg = reduced_args + arg_id;
                reduce(state, arena, stack, in_arg, reduced_arg);
            }

            Expression *reduced_op = pushStruct(arena, Expression);
            reduce(state, arena, stack, apply->op, reduced_op);

            if (reduced_op->cat == ExpCat_Procedure)
            {
                Stack new_env = extendEnvironment(stack, apply->arg_count, reduced_args);
                reduce(state, arena, &new_env, reduced_op->procedure.body, out);
            }
            else
            {
                out->apply.op        = reduced_op;
                out->apply.arg_count = apply->arg_count;
                out->apply.args      = reduced_args;
            }
        } break;

        case ExpCat_Switch:
        {
            auto switch0 = &in->switch0;
            Expression *reduced_subject = pushStruct(arena, Expression);
            reduce(state, arena, stack, switch0->subject, reduced_subject);
            Type *subject_type = reduced_subject->type_of_this;
            auto ctor_id = matchSwitchCase(state, subject_type, reduced_subject);
            if (ctor_id.success)
                reduce(state, arena, stack, switch0->case_bodies + ctor_id.value, out);
            else
                *out = *in;
        } break;

        case ExpCat_Type:
        case ExpCat_Procedure:
        case ExpCat_ConstructorRef:
        {
            *out = *in;
        } break;
    }
}

internal void
testPrintExp(Expression *out)
{
    switch (out->cat)
    {
        case ExpCat_Variable:
        {
            printf("atom(%d, %d)\n", out->variable.stack_depth, out->variable.id);
        } break;

        case ExpCat_Application:
        {
            todoIncomplete;
        } break;

        case ExpCat_Switch:
        {
            todoIncomplete;
        } break;

        case ExpCat_Type:
        {
            todoIncomplete;
        } break;

        case ExpCat_Procedure:
        {
            todoIncomplete;
        } break;

        case ExpCat_ConstructorRef:
        {
            Constructor *ctor = out->constructor_ref.type->ctors + out->constructor_ref.id;
            printf("%.*s\n", ctor->name.length, ctor->name.chars);
        } break;
    }
}

// NOTE: Main didspatch parse function
internal void
parseTopLevel(EngineState *state, MemoryArena *arena, Tokenizer *tk)
{
    b32 eof = false;
    while (!eof)
    {
        Token token = advance(tk); 
        switch (token.cat)
        {
            case 0:
            {
                eof = true;
            } break;

            case TokenCat_KeywordTypedef:
            {
                parseTypedef(state, arena, tk);
            } break;

            case TokenCat_KeywordDefine:
            {
                parseDefine(state, arena, tk);
            } break;

            // TODO: test code!
            case TokenCat_KeywordPrint:
            {
                requireChar(tk, '(');

                auto temp_arena = beginTemporaryArena(arena);
                {
                    MemoryArena *arena = &temp_arena;
                    Expression *exp = pushStruct(arena, Expression);
                    exp->cat = ExpCat_Application;
                    exp->apply.arg_count = 2;
                    allocate(arena, exp->apply.op);
                    allocateArray(arena, 2, exp->apply.args);

                    // Hacking the expression since we can't parse operators yet.
                    Expression *op   = exp->apply.op;
                    Expression *arg1 = exp->apply.args;
                    Expression *arg2 = exp->apply.args + 1;
                    parseExp(state, arena, &state->global_bindings, tk, arg1);
                    parseExp(state, arena, &state->global_bindings, tk, op);
                    parseExp(state, arena, &state->global_bindings, tk, arg2);

                    requireChar(tk, ')');

                    Expression *out = pushStruct(arena, Expression);
                    Stack empty_stack = {};
                    empty_stack.arena = arena;
                    reduce(state, arena, &empty_stack, exp, out);
                    testPrintExp(out);
                }
                endTemporaryArena(arena, &temp_arena);
            } break;

            default:
                todoIncomplete;
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

internal EngineState *
compile(MemoryArena *arena, ReadFileResult *source)
{
    EngineState *state = pushStruct(arena, EngineState);

    {// mark: initialize engine state
        state->scoped_arena = subArena(arena, megaBytes(2));

        state->global_bindings.arena = arena;
    }
    
#if 0
    {   // MARK: Parsing: Dealing with grouping constructs (not keywords), forming AST
        if (expressions->last_chunk != &expressions->first_chunk)
        {
            assert(expressions->first_chunk.next != 0);
        }
        s32 ast_count = 0;
        AstStackItem ast_stack[128];
        ast_stack[0].ast = root_ast;
        s32 stack_size = 1;
        for (s32 token_index = 0;
             token_index < token_count;
             token_index++)
        {
            char buffer[256];
            Token *token = tokens + token_index;

#if 0
            printStringToBuffer(buffer, token->chars, token->length);
            platformPrint(buffer);
            sprintf(buffer, "\n");
            platformPrint(buffer);
#endif

            if (token->type == TokenCat_PairingClose)
            {
                if ((stack_size > 1)  // NOTE: 0 is root.
                    && isMatchingPair((ast_stack + stack_size-1)->ast->token, token))
                {
                    stack_size--;
                }
                else todoErrorReport;
            }
            else
            {
                AstStackItem *outer = ((stack_size > 0) ?
                                       (ast_stack + stack_size-1) : 0);
                    
                AstList *last_ast_slot = &outer->ast->children;
                while (last_ast_slot->c)
                    last_ast_slot = &last_ast_slot->c->cdr;
                last_ast_slot->c = pushStruct(arena, AstListContent);
                Ast *new_ast = &last_ast_slot->c->car;

                new_ast->token = token;
                if (token->type == TokenCat_PairingOpen)
                {
                    new_ast->is_branch = true;
                    new_ast->token = token;
                    AstStackItem *new_outer = ast_stack + (stack_size++);
                    assert(stack_size <= arrayCount(ast_stack));
                    new_outer->ast = new_ast;
                }
                else
                {
                    new_ast->is_branch = false;
                }
            }
        }
    }
#endif

    {// MARK: Executing
#if 1
        Tokenizer tk = { source->content };
        parseTopLevel(state, arena, &tk);
#endif

#if 0
        Tokenizer tk = { source->content };
        debugPrintTokens(tk);
#endif
    }

    return state;
}

inline void
testCaseMain(MemoryArena *arena)
{
    char *input = "test.rea";
    ReadFileResult read = platformReadEntireFile(input);
    if (read.content)
    {
        auto *state = compile(arena, &read);
        // NOTE: you can put some assertions here.
        platformFreeFileMemory(read.content);
    }
    else
        printf("Failed to read input file %s", input);
}

internal void
engineMain(EngineMemory *memory)
{
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    auto arena = newArena(memory->storage_size, memory->storage);
    testCaseMain(&arena);
    // zeroMemory(memory->storage, memory->storage_size);
}

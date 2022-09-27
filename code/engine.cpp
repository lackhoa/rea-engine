#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"
#include "intrinsics.h"

#include <stdio.h>

// TODO: Eventually this will talk to the editor, but let's work in console mode for now.

struct String
{
    char *chars;
    s32  length;
};

typedef u64 AtomId;

struct Expr
{
    AtomId  op;  // NOTE: This might want to be an Expression pointer.
    s32     arg_count;
    Expr   *args;
};

struct ExpSwitch
{
};

struct Operator
{
    s32  arg_count;
    Expr *arg_types;
    Expr return_type;
    Expr body;
};

// There is an infinite type hierarchy, think of a 2D array referenced by
// "order" and "index".
struct Atom
{
    s32 order;  // 0 means atomic values, 1 means sets, then 2 means sets of sets, etc.
    s32 index;
};

#include "generated/Vector_Atom.h"

struct Type
{
    s32 member_count;
    s32 first_member;
    s32 case_count;  // for now it is equal to member_count, but for complex
                     // expressions it's different.
};

struct AtomSlot
{
    String   key;
    AtomId   value;
    AtomSlot *next;
};

struct Frame
{
    AtomSlot slots[128];
};

struct Bindings
{
    MemoryArena *arena;
    Frame        first;
    Bindings     *next;
};

inline Bindings *
extend(MemoryArena *arena, Bindings *outer)
{
    Bindings *result = pushStruct(arena, Bindings);
    for (int i = 0; i < arrayCount(result->first.slots); i++)
    {// invalidate these slots
        result->first.slots[i].key.length = 0;
    }
    result->next  = outer;
    result->arena = arena;
    return result;
}

enum TokenType
{
    // 0-255 reserved for single-char ASCII types.
    TokenType_Special         = 256,
    TokenType_PairingOpen     = 257,
    TokenType_PairingClose    = 258,
    TokenType_Alphanumeric    = 259,

    // TODO: Do I really need these? The tokenizer doesn't really produce this
    // information during its tokenization process.
    TokenType_KeywordsBegin_  = 300,
    TokenType_KeywordTypedef  = 301,
    TokenType_KeywordDefine   = 302,
    TokenType_KeywordSwitch   = 303,
    TokenType_KeywordsEnd_    = 400,
};

const char *keywords[] = {"_ignore_", "typedef", "define", "switch"};

struct Token
{
    String text;
    TokenType type;
};

inline b32
equals(String s, const char *cstring)
{
    if (!s.chars)
    {
        return false;
    }
    else
    {
        s32 at = 0;
        for (;
             (at < s.length);
             at++)
        {
            if ((cstring[at] == 0) || (s.chars[at] != cstring[at]))
            {
                return false;
            }
        }
        return (cstring[at] == 0);
    }
}

inline b32
equals(Token *token, const char *string)
{
    return equals(token->text, string);
}

inline b32
equals(Token *token, char c)
{
    return ((token->text.length == 1)
            &&  (token->text.chars[0] == c));
}

inline Token
newToken(char *first_char, TokenType category)
{
    Token result;
    result.text = {first_char, 0};
    result.type = category;
    return result;
}

internal TokenType
getCharacterType(char c)
{
    if ((('a' <= c) && (c <= 'z'))
        || (('A' <= c) && (c <= 'Z'))
        || (('0' <= c) && (c <= '9')))
    {
        return TokenType_Alphanumeric;
    }
    else
    {
        switch (c)
        {
            case '.':
            case '`':
            case ',':
            case '/':
            case '?':
            case '<':
            case '>':
            case '!':
            case '~':
            case '@':
            case '#':
            case '$':
            case '^':
            case '&':
            case '*':
            case '-':
            case '+':
            case '=':
            {
                return TokenType_Special;
            } break;

            case '(':
            case '{':
            {
                return TokenType_PairingOpen;
            } break;

            case ')':
            case '}':
            {
                return TokenType_PairingClose;
            }
        
            default:
                // NOTE: Self-describing category
                return (TokenType)c;
        }
    }
}

inline void
printStringToBuffer(char *buffer, String s)
{
    char *c = s.chars;
    for (s32 index = 0 ;
         index < s.length;
         index++)
    {
        buffer[index] = *c;
        c++;
    }
    buffer[s.length] = 0;
}

inline void
printCharToBufferRepeat(char *buffer, char c, s32 repeat)
{
    for (s32 index = 0 ;
         index < repeat;
         index++)
    {
        buffer[index] = c;
    }
    buffer[repeat] = 0;
}

struct Tokenizer
{
    char *at;
};

internal void
eatAllSpaces(Tokenizer *tk)
{
    b32 stop = false;
    while ((*tk->at) && (!stop))
    {
        switch (*tk->at)
        {
            case '\n':
            case '\t':
            case ' ':
            {
                tk->at++;
            } break;

            case ';':
            {
                if (*(tk->at+1) == ';')
                {
                    tk->at += 2;
                    while ((*tk->at) && (*tk->at != '\n'))
                        tk->at++;
                }
            } break;

            default:
                stop = true;
        }
    }
}

inline TokenType
keywordMatch(Token *token)
{
    TokenType result = (TokenType)0;
    for (int i = 1;
         i < arrayCount(keywords);
         i++)
    {
        if (equals(token, keywords[i]))
        {
            result = (TokenType)(TokenType_KeywordsBegin_ + i);
            break;
        }
    }
    return result;
}

inline b32
isKeyword(Token *token)
{
    return ((token->type > TokenType_KeywordsBegin_) && (token->type > TokenType_KeywordsEnd_));
}

inline Token
advance(Tokenizer *tk)
{
    Token result = {};
    eatAllSpaces(tk);
    result.text.chars = tk->at;
    b32 stop = false;

    TokenType type = getCharacterType(*tk->at++);
    result.type = type;
    switch (type)
    {
        case TokenType_Alphanumeric:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        case TokenType_Special:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        default: {}
    }

    result.text.length = tk->at - result.text.chars;
    if (result.type == TokenType_Alphanumeric)
    {
        if (TokenType new_type = keywordMatch(&result))
            result.type = new_type;
    }
    return result;
}

inline void
requireChar(Tokenizer *tk, char c)
{
    Token token = advance(tk);
    if (!((token.text.length == 1) && (token.text.chars[0] == c)))
        todoErrorReport;
}

internal void
debugPrintTokens(Tokenizer tk)
{
    while (*tk.at)
    {
        Token token = advance(&tk);
        printf("%.*s ", token.text.length, token.text.chars);
    }
    printf("\n");
}

#include "generated/Vector_Operator.h"
#include "generated/Vector_Type.h"

struct EngineState
{
    MemoryArena permanent_arena;
    MemoryArena temporary_arena;

    Bindings       global_scope;
    OperatorVector operators;

    s32        zeroth_order_count; // How many items currently are in the 0th order.
    s32        order_count;        // Including the 0th order.
    TypeVector orders[3];
    AtomVector atoms;
};

inline b32
equals(String a, String b)
{
    b32 result = true;
    if (a.length != b.length)
        result = false;
    else
    {
        for (int i = 0; i < a.length; i++)
        {
            if (a.chars[i] != b.chars[i])
            {
                result = false;
                break;
            }
        }
    }
    return result;
}

// TODO: Better hash function!
internal u32
stringHash(String string)
{
    u32 result = 0;
    for (int i = 0; i < string.length; i++)
    {
        result = 65599*result + string.chars[i];
    }
    return result;
}

struct AtomLookup
{
    AtomSlot *slot;
    b32 found;
};

internal AtomLookup
lookupBinding(Bindings *bindings, String key, b32 add_if_missing)
{
    AtomLookup result = {};
    u32 hash = stringHash(key) % arrayCount(Frame::slots);
    result.slot = (bindings->first.slots + hash);
    b32 first_slot_valid = result.slot->key.length;
    if (first_slot_valid)
    {
        b32 stop = false;
        while (!stop)
        {
            if (equals(result.slot->key, key))
            {
                stop = true;
                result.found = true;
            }
            else if (result.slot->next)
            {
                result.slot = result.slot->next;
            }
            else
            {
                stop = true;
                if (add_if_missing)
                {
                    allocate(bindings->arena, result.slot->next);
                    result.slot = result.slot->next;
                    result.slot->key  = key;
                    result.slot->next = 0;
                }
            }
        }
    }
    else
    {
        if (add_if_missing)
        {
            result.slot->key = key;
        }
    }

    return result;
}

inline AtomLookup
lookupBinding(Bindings *bindings, Token *key, b32 add_if_missing)
{
    return lookupBinding(bindings, key->text, add_if_missing);
}

inline b32
hasBinding(Bindings *bindings, Token key)
{
    AtomLookup lookup = lookupBinding(bindings, key.text, false);
    return lookup.found;
}

#if 0
internal void
parseExpression(EngineState *state, InstructionVector *instructions, Bindings *bindings, AstIterator *it, char end_delimiter = 0)
{
    MemoryArena *permanent = &state->permanent_arena;
    b32 not_empty = (it->list.c
                     && !isChar(it->list.c->car.token, end_delimiter));
    if (not_empty)
    {
        Ast *first = advance(it);
        b32 is_combination = (it->list.c
                              && !isChar(it->list.c->car.token, end_delimiter));
        if (is_combination)
        {
            // NOTE: the first thing is either a unary op, a function call, an
            // identifier, or a composite expression.
            if (first->is_branch)
            {
                todoIncomplete;
            }
            else
            {
                // NOTE: This is a composite: operator + operands.
                OpId op_id = lookupOperator(state, first);
                if (op_id)
                {
                    // MARK: Function call.
                    // TODO: could also be unary operator, but I suspect they go through the same path?
                    result.op = op_id;
                    AstList args = parseList(it);
                    if (args.c)
                    {
                        ExpressionList *dst = &result.args;
                        AstIterator arg_it = getIterator(args);
                        while (arg_it.list.c)
                        {
                            dst->c = pushStruct(permanent, ExpressionListContent);
                            dst->c->car = parseExpression(state, bindings, &arg_it);
                            dst = &dst->c->cdr;
                        }
                    }
                }
                else
                    todoErrorReport;
            }
        }
        else
        {
            if (first->is_branch)
            {
                AstIterator it = getIterator(first->children);
                // NOTE: Extra parens don't matter (we're not lisp).
                result = parseExpression(state, bindings, &it);
            }
            else
            {
                result.type = ExpressionTypeAtom;
                s32 id = lookupAtom(bindings, first);
                if (!id)
                    todoErrorReport;
                result.atom_id = id;
            }
        }
    }
    return result;
}
#endif

internal void
parseTypedef(EngineState *state, Tokenizer *tk)
{
    Type *type = pushItem(&state->orders[1]);

    Token type_name = advance(tk);
    if (type_name.type == TokenType_Alphanumeric)
    {
        // Check for global naming conflict
        AtomLookup lookup = lookupBinding(&state->global_scope, type_name.text, true);
        if (lookup.found) {todoErrorReport;}
        else
        {
            // Declare top-level value.
            Atom *atom = pushItem(&state->atoms);
            *atom = {};
            atom->order = 1;
            type->first_member = state->zeroth_order_count;
            atom->index = state->orders[1].count;

            requireChar(tk, '{');

            b32 stop = false;
            while (!stop)
            {
                Token token = advance(tk);
                if (equals(&token, '}'))
                {
                    stop = true;
                }
                else if (equals(&token, '|'))
                {
                    Token token = advance(tk);
                    if (token.type == TokenType_Alphanumeric)
                    {
                        AtomLookup lookup = lookupBinding(&state->global_scope, token.text, true);
                        if (lookup.found)
                            todoErrorReport;
                        else
                        {
                            lookup.slot->value = state->zeroth_order_count++;
                        }
                        type->member_count++;
                        type->case_count++;
                    }
                }
                else
                    todoErrorReport;
            }
        }
    }
}

struct Argument
{
    s32 identifier;
    s32 type_id;
};

enum BuiltInOperator
{
    BuiltInOperator_Null_,

    BuiltInOperator_Switch,

    BuiltInOperator_Count_,
};

// this eats the end marker too
internal Expr
parseExpression(EngineState *state, Bindings *bindings, Tokenizer *tk, char* end_markers)
{
    Expr out = {};
    Token first = advance(tk);
    if (isKeyword(&first))
    {
        switch (first.type)
        {
            out.op = BuiltInOperator_Switch;
            case TokenType_KeywordSwitch:
            {
                Expr switch_subject = parseExpression(state, bindings, tk, "{");

                // TODO: Need to check that all these cases are satisfied, somehow.
                for (b32 stop = false; !stop;)
                {
                    Token bar_or_closing_brace = advance(tk);
                    switch (bar_or_closing_brace.text.chars[0])
                    {
                        case '|':
                        {
                            Expr switch_case = parseExpression(state, bindings, tk, "{");
                            Expr case_body = parseExpression(state, bindings, tk, "}");
                        } break;

                        case '}':
                        {
                            stop = true;
                        } break;

                        default:
                            todoErrorReport;  // in switch expression, expect either '|' or '}'
                    }
                }

                requireChar(tk, '}');
            } break;

            default:
                todoIncomplete;
        }
    }
    else if (first.type == TokenType_Alphanumeric)
    {
        AtomLookup lookup = lookupBinding(bindings, &first, false);
        if (lookup.found)
        {
            out.op = lookup.slot->value;
        }
        else
            todoErrorReport;  // Unbound identifier
    }
    return out;
}

internal void
parseDefine(EngineState *state, Tokenizer *tk)
{
    Token define_name = advance(tk);
    if (define_name.type == TokenType_Alphanumeric)
    {
        AtomLookup lookup = lookupBinding(&state->global_scope, define_name.text, true);
        if (lookup.found)
            todoErrorReport;
        else
        {
            MemoryArena temp = subArena(&state->temporary_arena, kiloBytes(256));
            Bindings *bindings = extend(&temp, &state->global_scope);
            requireChar(tk, '(');
            Operator op = {};

            s32 arg_count = 0;
            {
                Tokenizer tk1_ = *tk;
                Tokenizer *tk1 = &tk1_;
                Token token = advance(tk1);
                b32 stop = false;
                s32 nesting_depth = 0;
                b32 previous_is_comma;
                while (!stop)
                {
                    previous_is_comma = false;
                    if (equals(&token, '('))
                    {
                        nesting_depth++;
                    }
                    else if (equals(&token, ')'))
                    {
                        if (nesting_depth)
                        {
                            nesting_depth--;
                        }
                        else
                        {
                            if (!previous_is_comma)
                            {
                                arg_count++;
                            }
                            stop = true;
                        }
                    }
                    else if ((nesting_depth == 0)
                             && (equals(&token, ',')))
                    {
                        arg_count++;
                        previous_is_comma = true;
                    }
                }
            }
            op.arg_count = arg_count;
            op.arg_types = pushArray(&state->permanent_arena, arg_count, Expr);
            
            s32 arg_it;
            b32 stop = false;
            for (arg_it = 0; !stop; arg_it++)
            {// parsing arguments
                Token arg_name_or_close = advance(tk);
                if (equals(&arg_name_or_close, ')'))
                {
                    stop = true;
                }
                else if (arg_name_or_close.type == TokenType_Alphanumeric)
                {
                    requireChar(tk, ':');

                    op.arg_types[arg_it] = parseExpression(state, bindings, tk, ",)");

                    Token delimiter = advance(tk);
                    if (equals(&delimiter, ')'))
                        stop = true;
                    else if (!equals(&delimiter, ','))
                        todoErrorReport;  // no comma after type
                }
                else
                    todoErrorReport;  // expected arg name
            }
            assert(arg_it == arg_count);

            // return type
            requireChar(tk, ':');
            op.return_type = parseExpression(state, bindings, tk, "{");
            op.body = parseExpression(state, bindings, tk, "}");

            endTemporaryArena(&state->temporary_arena, &temp);
        }
    }
    else
        todoErrorReport;
}

// NOTE: Main didspatch parse function
internal void
parseTopLevel(EngineState *state, Tokenizer *tk)
{
    b32 eof = false;
    while (!eof)
    {
        Token token = advance(tk); 
        switch (token.type)
        {
            case 0:
            {
                eof = true;
            } break;

            case TokenType_KeywordTypedef:
            {
                parseTypedef(state, tk);
            } break;

            case TokenType_KeywordDefine:
            {
                parseDefine(state, tk);
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

internal void
compile(EngineState *state, ReadFileResult *source)
{
    MemoryArena *permanent_arena = &state->permanent_arena;

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

            if (token->type == TokenType_PairingClose)
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
                last_ast_slot->c = pushStruct(permanent_arena, AstListContent);
                Ast *new_ast = &last_ast_slot->c->car;

                new_ast->token = token;
                if (token->type == TokenType_PairingOpen)
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
        parseTopLevel(state, &tk);
#endif

#if 0
        Tokenizer tk = { source->content };
        debugPrintTokens(tk);
#endif
    }
}

inline void
testCaseMain(EngineState *state)
{
    char *input = "test.rea";
    ReadFileResult read = platformReadEntireFile(input);
    if (read.content)
    {
        compile(state, &read);
        platformFreeFileMemory(read.content);
    }
    else
        printf("Failed to read input file %s", input);
}

internal EngineState *
resetEngineState(EngineMemory *memory, b32 zero_memory = true)
{
    if (zero_memory)
        zeroMemory(memory->storage, memory->storage_size);
    size_t temporary_arena_size = megaBytes(8);
    MemoryArena arena_ = newArena(memory->storage_size, memory->storage);

    EngineState *state = pushStruct(&arena_, EngineState);
    state->permanent_arena = arena_;
    state->temporary_arena = subArena(&state->permanent_arena, temporary_arena_size);

    state->operators       = newOperatorVector(&state->permanent_arena, 32);
    state->operators.count = 1;

    // TODO: More orders?
    state->order_count = 3;
    state->orders[1]   = newTypeVector(&state->permanent_arena, 128);
    state->orders[2]   = newTypeVector(&state->permanent_arena, 32);

    state->atoms       = newAtomVector(&state->permanent_arena, 1024);
    // NOTE: hack to reserve operators, don't this at home!
    state->atoms.count = BuiltInOperator_Count_;  

    state->global_scope.arena = &state->permanent_arena;

    return state;
}

internal void
engineMain(EngineMemory *memory)
{
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    EngineState *state = resetEngineState(memory, false);
    testCaseMain(state);
}

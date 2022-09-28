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

typedef s32 AtomId;  // This is an array index so it can't be too large.

enum ExpType
{
    ExpType_Atom,
    ExpType_Composite,
    ExpType_Switch,
};

struct Exp;

struct ExpComplex
{
    Exp *op;
    Exp *args;
};

struct ExpAtom
{
    AtomId id;
};

struct ExpSwitch
{
    Exp *subject;
    Exp *case_bodies;
};

struct Exp
{
    ExpType type;
    union
    {
        ExpComplex abstract;
        ExpSwitch  switch0;
        ExpAtom    atom;
    };
};

struct Operator
{
    s32  arg_count;
    Exp *arg_types;
    Exp return_type;
    Exp body;
};

enum AtomType
{
    AtomType_Data,
    AtomType_Operator,
};

// Atoms are just references to stores.
struct Atom
{
    AtomType type;
    union
    {
        struct
        {
            // There is an infinite type hierarchy, think of a 2D array
            // referenced by "order" and "index". 0th order means atomic values, 1st
            // means sets, 2 means sets of sets.
            s32 order;
            s32 order_index;
            Exp *type_exp;  // so atom types can be complex, and here we are.
        } data;
        struct
        {
            s32 index;
        } op;
    };
};

#include "generated/Vector_Atom.h"

struct Type
{
    s32 member_count;
    s32 first_member;
    s32 case_count;  // for now it is equal to member_count, but for composite
                     // cases it's different.
};

struct AtomSlot
{
    String   key;
    AtomId   value;
    AtomSlot *next;
};

struct Bindings
{
    MemoryArena *arena;
    AtomSlot     first[128];
    Bindings     *next;
};

inline Bindings *
extend(MemoryArena *arena, Bindings *outer)
{
    Bindings *out = pushStruct(arena, Bindings);
    for (int i = 0; i < arrayCount(out->first); i++)
    {// invalidate these slots
        AtomSlot *slot = &out->first[i];
        slot->value = 0;
    }
    out->next  = outer;
    out->arena = arena;
    return out;
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
    Token out;
    out.text = {first_char, 0};
    out.type = category;
    return out;
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
    TokenType out = (TokenType)0;
    for (int i = 1;
         i < arrayCount(keywords);
         i++)
    {
        if (equals(token, keywords[i]))
        {
            out = (TokenType)(TokenType_KeywordsBegin_ + i);
            break;
        }
    }
    return out;
}

inline b32
isKeyword(Token *token)
{
    return ((token->type > TokenType_KeywordsBegin_) && (token->type > TokenType_KeywordsEnd_));
}

inline Token
advance(Tokenizer *tk)
{
    Token out = {};
    eatAllSpaces(tk);
    out.text.chars = tk->at;
    b32 stop = false;

    TokenType type = getCharacterType(*tk->at++);
    out.type = type;
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

    out.text.length = tk->at - out.text.chars;
    if (out.type == TokenType_Alphanumeric)
    {
        if (TokenType new_type = keywordMatch(&out))
            out.type = new_type;
    }
    return out;
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
    MemoryArena scoped_arena;  // used for storing e.g stack frames

    Bindings       global_scope;
    OperatorVector operators;
    AtomVector     atoms;

    s32        zeroth_order_count; // How many items currently are in the 0th order.
    s32        order_count;        // Including the 0th order.
    FormVector orders[3];
};

inline b32
equals(String a, String b)
{
    b32 out = true;
    if (a.length != b.length)
        out = false;
    else
    {
        for (int i = 0; i < a.length; i++)
        {
            if (a.chars[i] != b.chars[i])
            {
                out = false;
                break;
            }
        }
    }
    return out;
}

// TODO: Better hash function!
internal u32
stringHash(String string)
{
    u32 out = 0;
    for (int i = 0; i < string.length; i++)
    {
        out = 65599*out + string.chars[i];
    }
    return out;
}

// If the value in the output slot is 0, that means lookup failed
internal AtomSlot *
lookupBindingCurrentFrame(Bindings *bindings, String key, b32 add_if_missing = false)
{
    AtomSlot *out = 0;
    u32 hash = stringHash(key);
    out = (bindings->first + (hash % arrayCount(bindings->first)));
    b32 first_slot_valid = out->key.length;
    if (first_slot_valid)
    {
        b32 stop = false;
        while (!stop)
        {
            if (equals(out->key, key))
            {
                stop = true;
            }
            else if (out->next)
            {
                out = out->next;
            }
            else
            {
                stop = true;
                if (add_if_missing)
                {
                    allocate(bindings->arena, out->next);
                    out = out->next;
                    out->key  = key;
                    out->value = 0;
                    out->next = 0;
                }
            }
        }
    }
    else if (add_if_missing)
    {
        out->key = key;
        out->value = 0;
    }

    return out;
}

inline AtomSlot *
lookupBindingCurrentFrame(Bindings *bindings, Token *key, b32 add_if_missing = false)
{
    return lookupBindingCurrentFrame(bindings, key->text, add_if_missing);
}

inline AtomId
lookupBindingRecursive(Bindings *bindings, Token *key, b32 add_if_missing = false)
{
    AtomId out = 0;
    for (b32 stop = false; !stop;)
    {
        AtomSlot *lookup = lookupBindingCurrentFrame(bindings, key, false);
        if (lookup->value)
        {
            out = lookup->value;
            stop = true;
        }
        else
        {
            if (bindings->next)
                bindings = bindings->next;
            else
                stop = true;
        }
    }
    return out;
}

internal void
parseTypedef(EngineState *state, MemoryArena *arena, Tokenizer *tk)
{
    Token type_name = advance(tk);
    if (type_name.type == TokenType_Alphanumeric)
    {
        AtomSlot *type_lookup = lookupBindingCurrentFrame(&state->global_scope, &type_name, true);
        if (type_lookup->value)
            todoErrorReport;
        else
        {
            s32 type_atom_id = state->atoms.count;
            type_lookup->value = type_atom_id;
            Atom *type_atom = pushItem(&state->atoms);
            type_atom->type = AtomType_Data;
            type_atom->data.order = 1;
            type_atom->data.order_index = state->orders[1].count;
            type_atom->data.type_exp = 0;  // todo: not sure what goes here.

            Type *type = pushItem(&state->orders[1]);
            type->first_member = state->zeroth_order_count;

            requireChar(tk, '{');

            b32 stop = false;
            s32 member_count = 0;
            s32 case_count = 0;
            Exp *type_exp = pushStruct(arena, Exp);
            type_exp->type = ExpType_Atom;
            type_exp->atom.id = type_atom_id;
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
                        AtomSlot *member_lookup = lookupBindingCurrentFrame(&state->global_scope, &token, true);
                        if (member_lookup->value)
                            todoErrorReport;
                        else
                        {
                            member_lookup->value = state->atoms.count;
                            Atom *member_atom = pushItem(&state->atoms);
                            member_atom->type = AtomType_Data;
                            member_atom->data.order = 0;
                            member_atom->data.order_index = state->zeroth_order_count++;
                            member_atom->data.type_exp = type_exp;
                        }
                        member_count++;
                        case_count++;
                    }
                    else
                        todoIncomplete;  // implement operators
                }
                else
                    todoErrorReport;  // expected '|' or '}'
            }
            type->member_count = member_count;
            type->case_count   = case_count;
        }
    }
    assert(lookupBindingCurrentFrame(&state->global_scope, &type_name));
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

internal s32
matchSwitchCase(EngineState *state, Exp *subject_form, Exp *case0)
{
    s32 out = -1;
    if (case0->type == ExpType_Atom)
    {
        Atom *case_atom = &state->atoms.items[case0->atom.id];
        if (case_atom->type == AtomType_Data)
        {
            if (case_atom->data.order == 0)
            {
                switch (subject_form->type)
                {
                    case ExpType_Atom:
                    {
                        s32 case_index = case_atom->data.order_index;
                        out = (case_index - subject_form->atom.id);
                    } break;

                    case ExpType_Composite:
                    {
                        todoIncomplete;
                    } break;

                    case ExpType_Switch:
                    {
                        todoErrorReport;  // the type of the switch subject is a
                                          // switch? I guess that could happen
                                          // but why, man?
                    } break;
                }
                
            }
            else
                todoIncomplete;  // higher-order subjects
        }
        else
            todoErrorReport;  // operators can't be a switch case
    }
    else
        todoIncomplete;  // handle complex cases

    return out;
}

internal Exp *
inferForm(EngineState *state, Exp *exp)
{
    Exp *out = 0;
    switch (exp->type)
    {
        case ExpType_Atom:
        {
            AtomId atom_id = exp->atom.id;
            Atom *atom = state->atoms.items + atom_id;
            switch (atom->type)
            {
                case AtomType_Data:
                {
                    out = atom->data.type_exp;
                } break;

                case AtomType_Operator:
                {
                    todoIncomplete;
                } break;
            }
        } break;

        case ExpType_Switch:
        {
            todoIncomplete;
        } break;

        case ExpType_Composite:
        {
            todoIncomplete;
        } break;
    }

    return out;
}

// this eats the end marker too.
internal void
parseExp(EngineState *state, MemoryArena *arena, Bindings *bindings, Tokenizer *tk, Exp *out, char* end_markers)
{
    Token first = advance(tk);
    if (isKeyword(&first))
    {
        switch (first.type)
        {
            case TokenType_KeywordSwitch:
            {
                out->type = ExpType_Switch;
                allocate(arena, out->switch0.subject);
                parseExp(state, arena, bindings, tk, out->switch0.subject, "{");
                Exp *form = inferForm(state, out->switch0.subject);

                // TODO: Need to check that all cases are satisfied, somehow.
                s32 case_count = 0;
                for (b32 stop = false; !stop;)
                {
                    Token first = advance(tk);
                    switch (first.text.chars[0])
                    {
                        case '|':
                        {
                            case_count++;
                            Exp switch_case = {};
                            s32 case_match;
                            parseExp(state, arena, bindings, tk, &switch_case, "{");
                            {
                                MemoryArena case_arena = beginTemporaryArena(arena);
                                Exp *subject_form = inferForm(state, out->switch0.subject);
                                case_match = matchSwitchCase(state, subject_form, &switch_case);
                                endTemporaryArena(&case_arena, &case_arena);
                            }
                            if (case_match == -1)
                                todoErrorReport;
                            else
                            {
                                out->switch0.case_bodies[case_match] = pushStruct;
                                parseExp(state, arena, bindings, tk, case_body, "}");
                            }
                        } break;

                        case '}':
                        {
                            stop = true;
                        } break;

                        default:
                            todoErrorReport;  // expect either '|' or '}'
                    }
                }
                assert(case_count = expected_case_count);
            } break;

            default:
                todoErrorReport;
        }
    }
    else if (first.type == TokenType_Alphanumeric)
    {
        AtomId identifier_atom = lookupBindingRecursive(bindings, &first, false);
        if (identifier_atom)
        {
            out->type = ExpType_Atom;
            out->atom.id = identifier_atom;
        }
        else
            todoErrorReport;  // Unbound identifier
    }
}

internal void
parseDefine(EngineState *state, MemoryArena *arena, Tokenizer *tk)
{
    Token define_name = advance(tk);
    if ((define_name.type == TokenType_Alphanumeric)
        || (define_name.type == TokenType_Special))
    {
        AtomSlot *define_slot = lookupBindingCurrentFrame(&state->global_scope, define_name.text, true);
        if (define_slot->value)
            todoErrorReport;
        else
        {
            define_slot->value = state->operators.count;
            Operator *op = pushItem(&state->operators);

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
            op->arg_count = arg_count;
            op->arg_types = pushArray(arena, arg_count, Exp);

            MemoryArena scoped_arena = beginTemporaryArena(&state->scoped_arena);
            Bindings *bindings = extend(&scoped_arena, &state->global_scope);
            s32 arg_it;
            b32 stop = false;
            for (arg_it = 0; !stop; arg_it++)
            {// parsing arguments
                Token arg_name_or_end = advance(tk);
                if (equals(&arg_name_or_end, ')'))
                    stop = true;
                else if (arg_name_or_end.type == TokenType_Alphanumeric)
                {
                    AtomSlot *arg_name_lookup = lookupBindingCurrentFrame(bindings, &arg_name_or_end, true);
                    if (arg_name_lookup->value)
                        todoErrorReport;
                    else
                    {
                        arg_name_lookup->value = state->atoms.count;
                        Atom *arg_atom = pushItem(&state->atoms);
                        // TODO: not sure what this atom even is, and why do we
                        // need to store it.

                        requireChar(tk, ':');

                        parseExp(state, arena, bindings, tk, op->arg_types + arg_it, ",)");
                        arg_atom->data.type_exp = op->arg_types + arg_it;

                        Token delimiter = advance(tk);
                        if (equals(&delimiter, ')'))
                            stop = true;
                        else if (!equals(&delimiter, ','))
                            todoErrorReport;  // no comma after type
                    }
                }
                else
                    todoErrorReport;  // expected arg name
            }
            assert(arg_it == arg_count);

            // return type
            requireChar(tk, ':');
            parseExp(state, arena, bindings, tk, &op->return_type, "{");
            parseExp(state, arena, bindings, tk, &op->body, "}");

            endTemporaryArena(&state->scoped_arena, &scoped_arena);
        }
    }
    else
        todoErrorReport;
}

// NOTE: Main didspatch parse function
internal void
parseTopLevel(EngineState *state, MemoryArena *arena, Tokenizer *tk)
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
                parseTypedef(state, arena, tk);
            } break;

            case TokenType_KeywordDefine:
            {
                parseDefine(state, arena, tk);
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
        state->operators       = newOperatorVector(arena, 32);
        state->operators.count = 1;

        state->scoped_arena = subArena(arena, megaBytes(2));

        // TODO: More orders?
        state->order_count = 3;
        state->orders[1]   = newFormVector(arena, 128);
        state->orders[2]   = newFormVector(arena, 32);

        state->atoms       = newAtomVector(arena, 1024);
        // NOTE: hack to reserve operators, don't this at home!
        state->atoms.count = BuiltInOperator_Count_;  

        state->global_scope.arena = arena;
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
                last_ast_slot->c = pushStruct(arena, AstListContent);
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
        parseTopLevel(state, arena, &tk);
#endif

#if 0
        Tokenizer tk = { source->content };
        debugPrintTokens(tk);
#endif
    }
}

inline void
testCaseMain(MemoryArena *arena)
{
    char *input = "test.rea";
    ReadFileResult read = platformReadEntireFile(input);
    if (read.content)
    {
        EngineState *state = compile(arena, &read);
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

    MemoryArena arena = newArena(memory->storage_size, memory->storage);
    testCaseMain(&arena);
    // zeroMemory(memory->storage, memory->storage_size);
}

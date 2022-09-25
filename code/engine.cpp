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
// TODO: implement code gen
generate(List, String)

#include "generated_List.h"

struct Axiom
{
    String name;
    // TODO: arguments, and return.
};
generate(Vector, Axiom)

struct Operator
{
    s32    arg_count;
    String name;
};
generate(Vector, Operator)

struct Atom
{
    String text;
};
generate(Vector, Atom)

struct Type
{
    String     name;
    StringList members;
};
generate(Vector, Type)

#include "generated_Vector.h"

struct ArrayListChunk
{
    s32  count;
    u8 *items;
    ArrayListChunk *next;
};

struct ArrayList
{
    // NOTE: We don't know what the count of the whole list is.
    MemoryArena *arena;
    s32 item_size;
    s32 chunk_size;
    ArrayListChunk first_chunk;

    ArrayListChunk *last_chunk;
};

struct ArrayListIterator
{
    ArrayList *list;
    ArrayListChunk *chunk;
    void *current;
    s32 index;
};

inline ArrayListIterator
getIterator(ArrayList *list)
{
    ArrayListIterator it;
    it.list = list;
    it.chunk = &list->first_chunk;
    it.index = 0;

    if (list->first_chunk.count != 0)
        it.current = list->first_chunk.items;
    else
        it.current = 0;

    return it;
}

inline void
advance(ArrayListIterator *it)
{
    void *current = 0;
    if (it->chunk)
    {
        it->index++;
        if (it->index >= it->chunk->count)
        {
            it->chunk = it->chunk->next;
            it->index = 0;
            if ((it->chunk) && (it->chunk->count != 0))
                it->current = it->chunk->items + 0;
        }
        else
        {
            current = it->chunk + it->index;
        }
    }
    it->current = current;
}

inline void
initializeArrayList(MemoryArena *arena, ArrayList *list, s32 chunk_size, s32 item_size)
{
    list->arena = arena;
    list->item_size = item_size;
    list->chunk_size = chunk_size;
    list->first_chunk = {};
    list->first_chunk.items = (u8 *) pushSize(arena, (chunk_size * item_size));
    list->last_chunk = &list->first_chunk;
}

inline ArrayList *
allocateArrayList(MemoryArena *arena, s32 chunk_size, s32 item_size)
{
    ArrayList *list = pushStruct(arena, ArrayList);
    initializeArrayList(arena, list, chunk_size, item_size);
    return list;
}

inline void *
arrayListAdd_(ArrayList *list, s32 item_size)
{
    // TODO: @Polymorphic
    assert(item_size == list->item_size);
    assert(list->last_chunk->count <= list->chunk_size);
    if (list->last_chunk->count == list->chunk_size)
    {
        ArrayListChunk *new_chunk = pushStruct(list->arena, ArrayListChunk);
        new_chunk->items = (u8 *)pushSize(list->arena, (list->chunk_size * list->item_size));
        new_chunk->count = 0;
        new_chunk->next = 0;
        list->last_chunk->next = new_chunk;
        list->last_chunk = new_chunk;
    }
    void *added = (u8 *)list->last_chunk->items + ((list->last_chunk->count++) * list->item_size);
    return added;
}

#define arrayListAdd(list, type) (type*) arrayListAdd_(list, sizeof(type))

enum TokenType
{
    // 0-255 reserved for single-char ASCII types.
    TokenType_Null_           = 0,

    TokenType_Space           = 256,
    TokenType_Special         = 257,
    TokenType_PairingOpen     = 258,
    TokenType_PairingClose    = 259,
    TokenType_Alphabetical    = 260,

    TokenType_Keywords_       = 300,
    TokenType_KeywordTypedef  = 301,
    TokenType_KeywordAxiom    = 302,
    TokenType_KeywordDefine   = 302,
};

struct Token
{
    String text;
    TokenType type;
};

inline b32
equalToCString(String s, const char *cstring)
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
tokenEqualCString(Token *token, const char *string)
{
    return equalToCString(token->text, string);
}

inline b32
partOfToken(TokenType category)
{
    switch (category)
    {
        case 0:
        case TokenType_Space:
        case '\n':
        case ';':
            return false;
        default:
            return true;
    }
}

inline Token
newToken(char *first_char, TokenType category)
{
    Token result;
    result.text = {first_char, 0};
    result.type = category;
    return result;
}

struct AstListContent;
struct AstList
{
    AstListContent *c;
};
struct Ast
{
    // TODO: Reduce pointer chasing!
    b32 is_branch;
    Token *token;  // NOTE: If this tree is a branch, then this is the group
                   // begin character (e.g '(' or '{').
    // TODO: No more linked list please!
    AstList children;
};
struct AstListContent
{
    Ast     car;
    AstList cdr;
};

internal TokenType
categorizeCharacter(char character)
{
    if ((65 <= character) && (character <= 122))
    {
        return TokenType_Alphabetical;
    }
    else
    {
        switch (character)
        {
            case '\t':
            case ' ':
            {
                return TokenType_Space;
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
            } break;

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

            default:
                // NOTE: Self-describing category
                return (TokenType)character;
        }
    }
}

struct AstStackItem
{
    Ast *ast;
};

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

internal void
debugPrintAst(Ast *ast, s32 indentation)
{
    if (ast->is_branch)
    {
        for (AstList child = ast->children;
             child.c;
             child = child.c->cdr)
        {
            debugPrintAst(&child.c->car, indentation+1);
        }
    }
    else
    {
        char buffer[256];
        assert(ast->token);
        printCharToBufferRepeat(buffer, ' ', 4*indentation);
        platformPrint(buffer);

        printStringToBuffer(buffer, ast->token->text);
        platformPrint(buffer);

        sprintf(buffer, "\n");
        platformPrint(buffer);
    }
}

typedef s32 OpId;

struct AstIterator
{
    AstList list;
};

inline AstIterator
getIterator(AstList list)
{
    return AstIterator{list};
}

inline Ast *
getCurrent(AstIterator *it)
{
    return &it->list.c->car;
}

inline Ast *
advance(AstIterator *it)
{
    Ast *current = getCurrent(it);
    it->list = it->list.c->cdr;
    return current;
}

#if 0
inline s32
parseOperatorArgCount(AstIterator *it)
{
    Ast *arg_count = getCurrent(it);
    assert(arg_count->token);

    s32 arg_count_parsed = 0;
    if (tokenEqualCString(arg_count->token, "unary"))
    {
        arg_count_parsed = 1;
    }
    else if (tokenEqualCString(arg_count->token, "binary"))
    {
        arg_count_parsed = 2;
    }
    else if (tokenEqualCString(arg_count->token, "ternary"))
    {
        arg_count_parsed = 3;
    }
    else
    {
        todoErrorReport;
    }

    advance(it);
    return arg_count_parsed;
}
#endif

struct EngineState
{
    MemoryArena permanent_arena;

    OperatorVector operators;
    AxiomVector    axioms;
    TypeVector     types;
};

inline Token *
parseToken(AstIterator *it)
{
    Ast *op = advance(it);
    if (op->is_branch)
    {
        todoErrorReport;
    }
    return op->token;
}

inline char
parseChar(AstIterator *it)
{
    Ast *op = advance(it);
    if (op->token->text.length != 1)
    {
        todoErrorReport;
    }
    return op->token->text.chars[0];
}

inline AstList
parseList(AstIterator *it)
{
    AstList result = {};
    Ast *list = advance(it);
    if (list->is_branch)
        result = list->children;
    else
        todoErrorReport;
    return result;
}

enum ExpressionType
{
    ExpressionTypeAtom,
    ExpressionTypeComposite,
};

struct ExpressionList;
struct Expression
{
    ExpressionType type;
    union
    {
        // NOTE: Atomic
        struct
        {
            s32 atom_id;
        };
        // NOTE: Composite
        struct
        {
            OpId op;
            ExpressionList *args;
        };
    };
};

// TODO: linked list
struct ExpressionList
{
    Expression car;
    ExpressionList *cdr;
};

inline void
addArg(MemoryArena *arena, Expression *e)
{
    if (e->args)
    {
        ExpressionList *last = e->args;
        while(last->cdr)
            last = last->cdr;
        last->cdr = pushStruct(arena, ExpressionList);
        last->cdr->car = *e;
        last->cdr->cdr = 0;
    }
    else
    {
        e->args = pushStruct(arena, ExpressionList);
        e->args->car = *e;
        e->args->cdr = 0;
    }
}

inline b32
stringEqual(String a, String b)
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

inline OpId
lookupOperator(EngineState *state, Ast *ast)
{
    OpId result = 0;
    OperatorVector *operators = &state->operators;
    if (ast->token)
    {
        for (s32 i = 1;
             i < operators->count;
             i++)
        {
            // TODO: could be a hash table lookup
            if (stringEqual(operators->items[i].name, ast->token->text))
                result = i;
        }
    }
    return result;
}

inline s32
lookupAtom(AtomVector *atoms, Ast *ast)
{
    s32 result = 0;
    assert(!ast->is_branch);
    for (int i = 1;
         i < atoms->count;
         i++)
    {
        if (stringEqual(atoms->items[i].text, ast->token->text))
        {
            result = i;
            break;
        }
    }
    return result;
}

// TODO: Should this take an expression pointer instead?
internal Expression
parseExpression(EngineState *state, AtomVector *atoms, AstIterator *it)
{
    MemoryArena *arena = &state->permanent_arena;
    Expression result = {};
    if (it->list.c)
    {
        Ast *first = advance(it);
        if (it->list.c)
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
                result.type = ExpressionTypeComposite;
                OpId op_id = lookupOperator(state, first);
                if (op_id)
                {
                    // MARK: Function call.
                    // TODO: could also be unary operator, but I suspect they go through the same path?
                    result.op = op_id;
                    AstList args = parseList(it);
                    if (args.c)
                    {
                        result.args = pushStruct(arena, ExpressionList);
                        AstIterator arg_it = getIterator(args);
                        ExpressionList *result_arg = result.args;
                        result_arg->car = parseExpression(state, atoms, &arg_it);
                        while (arg_it.list.c)
                        {
                            result_arg->cdr = pushStruct(arena, ExpressionList);
                            result_arg->cdr->car = parseExpression(state, atoms, &arg_it);
                            result_arg = result_arg->cdr;
                        }
                    }
                }
                else
                    todoErrorReport;
            }
        }
        else
        {
            // NOTE: we don't have to worry about operator combinations here.
            if (first->is_branch)
            {
                AstIterator it = getIterator(first->children);
                // NOTE: Extra parens don't matter (we're not lisp).
                result = parseExpression(state, atoms, &it);
            }
            else
            {
                result.type = ExpressionTypeAtom;
                s32 id = lookupAtom(atoms, first);
                if (id)
                {
                    Atom *atom = pushItem(atoms);
                    *atom = {first->token->text};
                    id = atoms->count-1;
                }
                result.atom_id = id;
            }
        }
    }
    else
    {
        // NOTE: Empty expression.
    }
    return result;
}

#if 0
internal void
parseAxiomDefinition(EngineState *state, AstIterator *it)
{
    Token *name = parseToken(it);
    AstList args = parseList(it);
    // TODO: BOOKMARK: Record the arguments in the axiom type.
    for (AstList arg = args;
         arg.c;
         arg = arg.c->cdr)
    {
        MemoryArena temp_arena = subArena(&state->permanent_arena, kiloBytes(256));
        AtomVector atoms = newAtomVector(&temp_arena, 8);
        atoms.count = 1;
        parseExpression(state, &atoms, arg.c->car);
    }
    Ast *body = parseBody(it);

    Axiom axiom = {};
    addItem(&state->axioms, &axiom);
}
#endif

internal void
parseTypedef(EngineState *state, AstIterator *it)
{
    Type *result = pushItem(&state->types);

    Token *type_name = parseToken(it);
    result->name = type_name->text;

    StringList *dst = &result->members;
    AstList members_ast = parseList(it);
    AstIterator members_it = getIterator(members_ast);
    while (members_it.list.c)
    {
        if (parseChar(&members_it) == '|')
        {
            Token *member = parseToken(&members_it);
            dst->c = pushStruct(&state->permanent_arena, StringListContent);
            dst->c->car = member->text;
            dst = &dst->c->cdr;
        }
        else
            todoErrorReport;
    }
}

// NOTE: Main didspatch parse function
internal void
parseAstTopLevel(EngineState *state, AstIterator *it)
{
    Ast *ast = advance(it);
    if (Token *token = ast->token)
    {
        switch (token->type)
        {
            case TokenType_KeywordTypedef:
            {
                parseTypedef(state, it);
            } break;

#if 0
            case TokenType_KeywordAxiom:
            {
                parseAxiomDefinition(state, it);
            } break;
#endif

            default: todoIncomplete;
        }
    }
    else todoIncomplete;
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
compile(EngineState *state, ReadFileResult *source_code)
{
    MemoryArena *permanent_arena = &state->permanent_arena;
    TokenType previous_category = (TokenType_Null_);
    s32 token_count = 0;
    s32 todo_token_cap = source_code->content_size / 2;
    Token *tokens = pushArray(permanent_arena, todo_token_cap, Token);
    b32 being_commented = false;
    // TODO: Unicode support?
    for (s32 content_index = 0;
         content_index < source_code->content_size;
         content_index++)
    {   // MARK: tokenizing
        char *character = &((char *)source_code->content)[content_index];
        TokenType token_type = categorizeCharacter(*character);

        if (token_type == ';')
            being_commented = true;
        if (token_type == '\n')
            being_commented = false;

        if (!being_commented)
        {
            b32 char_is_part_of_token = partOfToken(token_type);
            b32 add_token = (((previous_category != token_type)
                              || (token_type == TokenType_PairingOpen)
                              || (token_type == TokenType_PairingClose))
                             && char_is_part_of_token);

            if (add_token)
            {
                Token *token = tokens + token_count++;
                token->text = {character, 0};
                token->type = token_type;
            }

            b32 extending_previous_token = char_is_part_of_token;
            if (extending_previous_token)
            {
                tokens[token_count-1].text.length++;
            }
            else if (token_count >= 1)
            {
                Token *previous_token = tokens + token_count-1;
                if (tokenEqualCString(previous_token, "axiom"))
                    previous_token->type = TokenType_KeywordAxiom;
                else if (tokenEqualCString(previous_token, "typedef"))
                    previous_token->type = TokenType_KeywordTypedef;
            }

            previous_category = token_type;
        }
    }

    s32 todo_ast_chunk_size = 1024;
    ArrayList *expressions = allocateArrayList(&state->permanent_arena, todo_ast_chunk_size, sizeof(Ast));
    Ast *root_ast = arrayListAdd(expressions, Ast);
    root_ast->is_branch = true;
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

    {// MARK: Executing
#if 1
        AstIterator it = getIterator(root_ast->children);
        parseAstTopLevel(state, &it);
#endif

#if 1
        debugPrintAst(root_ast, 0);
#endif
    }
}

inline void
testCaseMain(EngineState *state)
{
    ReadFileResult read = platformReadEntireFile("test.rea");
    compile(state, &read);

    assert(state->types.count == 2);
    assert(equalToCString(state->types.items[1].name, "Bool"));
    assert(length(state->types.items[1].members) == 2);

    platformFreeFileMemory(read.content);
}

internal EngineState *
resetEngineState(EngineMemory *memory)
{
    zeroMemory(memory->storage, memory->storage_size);
    MemoryArena arena_ = newArena(memory->storage_size, memory->storage);

    EngineState *state = pushStruct(&arena_, EngineState);
    state->permanent_arena = arena_;

    state->axioms    = newAxiomVector(&state->permanent_arena, 32);
    state->operators = newOperatorVector(&state->permanent_arena, 32);
    state->types     = newTypeVector(&state->permanent_arena, 32);
    state->axioms.count    = 1;
    state->operators.count = 1;
    state->types.count     = 1;

    return state;
}

internal void
engineMain(EngineMemory *memory)
{
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    EngineState *state = resetEngineState(memory);
    testCaseMain(state);
}

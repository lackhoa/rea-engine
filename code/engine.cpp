#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"
#include "intrinsics.h"

#include <stdio.h>

// TODO: Eventually this will talk to the editor, but let's work in console mode for now.

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
    TokenTypeNull_           = 0,

    TokenTypeSpace           = 256,
    TokenTypeOperator        = 257,
    TokenTypeAlphabetical    = 258,

    TokenTypeKeywords_       = 259,
    TokenTypeKeywordOperator = 260,
    TokenTypeKeywordAxiom    = 261,
};

struct String
{
    char *chars;
    s32 length;
};

struct Token
{
    String text;
    TokenType type;
};

inline b32
equalToCString(String s, const char *string)
{
    b32 result = true;
    if (!s.chars)
    {
        result = false;
    }
    else
    {
        for (s32 i = 0;
          (i < s.length);
          i++)
        {
            if ((string[i] == '\0') || (s.chars[i] != string[i]))
            {
                result = false;
                break;
            }
        }
    }
    return result;
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
        case TokenTypeSpace:
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

struct Ast;
struct AstList
{
    Ast *ast;
    AstList *next;
};

struct Ast
{
    // TODO: Reduce pointer chasing!
    b32 is_branch;
    union
    {
        struct
        {
            // TODO: No more linked list please!
            AstList *children;
        };
        struct
        {
            // NOTE: Single-token leaf ast.
            Token *token;
        };
    };
};

inline b32
astSlotValid(AstList *slot)
{
    return (slot->ast != 0);
}

internal TokenType
categorizeCharacter(char character)
{
    if ((65 <= character) && (character <= 122))
    {
        return TokenTypeAlphabetical;
    }
    else
    {
        switch (character)
        {
            case '\t':
            case ' ':
            {
                return TokenTypeSpace;
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
                return TokenTypeOperator;
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
        for (AstList *child = ast->children;
             child && child->ast;
             child = child->next)
        {
            debugPrintAst(child->ast, indentation+1);
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

struct Operator
{
    s32  arg_count;
    String text;
};

struct OperatorChunk
{
    s32           count;
    Operator      items[32];
    OperatorChunk *next;
};

struct OperatorPool
{
    OperatorChunk first;
};

inline Operator *
addToPool(OperatorPool *pool)
{
    if (pool->first.count == arrayCount(OperatorChunk::items))
    {
        OperatorChunk *copy_destination = pushStruct(global_arena, OperatorChunk);
        *copy_destination               = pool->first;
        copy_destination->next          = pool->first.next;

        pool->first.next  = copy_destination;
        pool->first.count = 0;
    }
    return (pool->first.items + pool->first.count++);
}

struct Axiom
{
    String name;
    // TODO: arguments, and return.
};

struct AxiomChunk
{
    s32        count;
    Axiom      items[32];
    AxiomChunk *next;
};

struct AxiomPool
{
    AxiomChunk first;
};

struct AstIterator
{
    AstList *list;
};

inline AstIterator
getIterator(AstList *list)
{
    return AstIterator{list};
}

inline Ast *
getCurrent(AstIterator *it)
{
    return it->list->ast;
}

inline Ast *
advance(AstIterator *it)
{
    Ast *current = getCurrent(it);
    it->list = it->list->next;
    return current;
}

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

struct EngineState
{
    MemoryArena arena;
    OperatorPool operators;
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

internal void
parseOperatorDefinition(EngineState *state, AstIterator *it)
{
    s32 arg_count         = parseOperatorArgCount(it);
    Token *operator_token = parseToken(it);

    Operator *op  = addToPool(&state->operators);
    op->arg_count = arg_count;
    op->text      = operator_token->text;
}

internal void
parseAxiomDefinition(EngineState *state, AstIterator *it)
{
    Token *name = parseToken(it);
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
            case TokenTypeKeywordOperator:
            {
                parseOperatorDefinition(state, it);
            } break;

            case TokenTypeKeywordAxiom:
            {
                parseAxiomDefinition(state, it);
            } break;

            default:
            {
                todoIncomplete;
            }
        }
    }
    else
    {
        todoIncomplete;
    }
}

inline void
makeBranchAst(Ast *ast)
{
    ast->is_branch = true;
}

inline void
makeLeafAst(Ast *ast, Token *token)
{
    ast->is_branch = false;
    ast->token = token;
}

internal void
compile(EngineState *state, const char *input_file)
{
    MemoryArena *arena = global_arena;
    ReadFileResult read = platformReadEntireFile(input_file);
    if (read.content)
    {
        TokenType previous_category = (TokenTypeNull_);
        s32 token_count = 0;
        s32 todo_token_cap = read.content_size / 2;
        Token *tokens = pushArray(arena, todo_token_cap, Token);
        b32 being_commented = false;
        // TODO: Unicode support?
        for (s32 content_index = 0;
             content_index < read.content_size;
             content_index++)
        {   // MARK: tokenizing
            char *character = &((char *)read.content)[content_index];
            TokenType token_type = categorizeCharacter(*character);

            if (token_type == ';')
                being_commented = true;
            if (token_type == '\n')
                being_commented = false;

            if (!being_commented)
            {
                b32 char_is_part_of_token = partOfToken(token_type);
                b32 add_token = (((previous_category != token_type)
                                  || (token_type == '(')
                                  || (token_type == ')'))
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
                    if (tokenEqualCString(previous_token, "operator"))
                        previous_token->type = TokenTypeKeywordOperator;
                    else if (tokenEqualCString(previous_token, "axiom"))
                        previous_token->type = TokenTypeKeywordAxiom;
                }

                previous_category = token_type;
            }
        }

        s32 todo_ast_chunk_size = 1024;
        ArrayList *expressions = allocateArrayList(&state->arena, todo_ast_chunk_size, sizeof(Ast));
        Ast *root_ast = arrayListAdd(expressions, Ast);
        makeBranchAst(root_ast);
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

                if (token->type == ')')
                {
                    if (stack_size > 1)  // NOTE: 0 is root.
                    {
                        stack_size--;
                        AstStackItem *outer = ast_stack + stack_size-1;
                    }
                    else
                    {
                        // TODO: Error
                        assert(0);
                    }
                }
                else
                {
                    Ast *new_ast = pushStructZero(arena, Ast);
                    AstStackItem *outer = ((stack_size > 0) ?
                                           (ast_stack + stack_size-1) : 0);
                    
                    AstList  *last_child;
                    if (outer->ast->children)
                    {
                        last_child = outer->ast->children;
                        while (last_child->next != 0)
                            last_child = last_child->next;
                        last_child->next = pushStruct(arena, AstList);
                        last_child = last_child->next;
                    }
                    else
                    {
                        outer->ast->children = pushStruct(arena, AstList);
                        last_child = outer->ast->children;
                    }
                    last_child->ast = new_ast;
                    last_child->next = 0;

                    if (token->type == '(')
                    {
                        makeBranchAst(new_ast);
                        AstStackItem *new_outer = ast_stack + (stack_size++);
                        assert(stack_size <= arrayCount(ast_stack));
                        new_outer->ast = new_ast;
                    }
                    else
                    {
                        makeLeafAst(new_ast, token);
                    }
                }
            }
        }

        {// MARK: Executing
#if 1
            debugPrintAst(root_ast, 0);
#endif

#if 1
            AstIterator it = getIterator(root_ast->children);
            parseAstTopLevel(state, &it);
#endif
        }

        // TODO: Only free when we have edits;
        platformFreeFileMemory(read.content);
    }
    else
    {
        todoErrorReport;
    }
}

internal void
testCase(EngineState *state)
{
    compile(state, "test.rea");
    assert(state->operators.first.count == 1);
}

internal EngineState *
clearEngineState(EngineMemory *memory)
{
    zeroMemory(memory->storage, memory->storage_size);
    MemoryArena arena_ = newArena(memory->storage_size, memory->storage);
    EngineState *state = pushStruct(&arena_, EngineState);
    state->arena = arena_;
    global_arena = &state->arena;
    return state;
}

internal void
engineMain(EngineMemory *memory)
{
    platformPrint = memory->platformPrint;
    platformReadEntireFile = memory->platformReadEntireFile;
    platformFreeFileMemory = memory->platformFreeFileMemory;

    EngineState *state = clearEngineState(memory);
    testCase(state);
}

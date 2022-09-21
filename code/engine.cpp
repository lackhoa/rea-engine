#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"

#include <stdio.h>

// TODO: Eventually this will talk to the editor, but let's work in console mode for now.

enum Operator
{
    OperatorSymbol,
    OperatorEquality,

    OperatorCOUNT,
};

struct ArrayListChunk
{
    s32  count;
    u8 *items;
    ArrayListChunk *next;
};

struct ArrayList
{
    // NOTE: We don't know what the count of the whole list is.
    Memory_arena *arena;
    s32 item_size;
    s32 chunk_size;
    ArrayListChunk first_chunk;

    ArrayListChunk *last_chunk;
};

struct ArrayListIterator
{
    ArrayList *list;
    ArrayListChunk *chunk;
    s32 index;
};

inline ArrayListIterator
getIterator(ArrayList *list)
{
    ArrayListIterator it;
    it.list = list;
    it.chunk = &list->first_chunk;
    it.index = 0;
    return it;
}

inline void
advance(ArrayListIterator *it)
{
    if (it->chunk)
    {
        it->index++;
        if (it->index >= it->chunk->count)
        {
            it->chunk = it->chunk->next;
            it->index = 0;
        }
    }
}

inline void *
getCurrent_(ArrayListIterator *it, s32 item_size)
{
    assert(it->list->item_size == item_size);
    void *result = 0;
    if (it->chunk)
    {
        result = it->chunk->items + (item_size * it->index);
    }
    return result;
}

#define getCurrent(it, type) (type *) getCurrent_(it, sizeof(type))

inline void
initializeArrayList(Memory_arena *arena, ArrayList *list, s32 chunk_size, s32 item_size)
{
    list->arena = arena;
    list->item_size = item_size;
    list->chunk_size = chunk_size;
    list->first_chunk = {};
    list->first_chunk.items = (u8 *) pushSize(arena, (chunk_size * item_size));
    list->last_chunk = &list->first_chunk;
}

inline ArrayList *
allocateArrayList(Memory_arena *arena, s32 chunk_size, s32 item_size)
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

struct Expression
{
    Expression *op;
    // TODO: @Memory: Do we want the arg list in the expression always? Most
    // expressions don't have args.
    ArrayList  args;  // NOTE: Pool of Expression*

    // NOTE: Mandatory for  expressions with 0 args.
    char       *name;
    s32        name_length;
};

inline void
initializeExpression(Memory_arena *arena, Expression *expression)
{
    initializeArrayList(arena, &expression->args, 8, sizeof(Expression*));
    expression->name = 0;
    expression->name_length = 0;
    expression->op = 0;
}

#define arrayListAdd(list, type) (type*) arrayListAdd_(list, sizeof(type))

#if 0
internal b32
metaEqual(Expression *a, Expression *b)
{
    if (a->op == b->op)
    {
        if (operatorArgCount[a->op] == 0)
        {
            return (a->name == b->name);
        }
        else
        {
            for (s32 arg_index = 0;
                 arg_index < operatorArgCount[a->op];
                 arg_index++)
            {
                if (!metaEqual(a->args[arg_index],
                               b->args[arg_index]))
                    return false;
            }
            return true;
        }
    }
    else return false;
}
#endif

enum CharacterCategory
{
    CharacterCategoryNull,
    CharacterCategorySpace,
    CharacterCategoryNewline,
    CharacterCategorySemicolon,
    CharacterCategoryGroupBegin,
    CharacterCategoryGroupEnd,
    CharacterCategoryOperator,
    CharacterCategoryAlphabetical,

    CharacterCategoryCOUNT,
};

struct Token
{
    char *chars;
    s32 length;
    CharacterCategory category;  // NOTE: Characters in a token are the same, for now...
};

inline b32
partOfToken(CharacterCategory category)
{
    switch (category)
    {
        case CharacterCategoryNull:
        case CharacterCategorySpace:
        case CharacterCategoryNewline:
        case CharacterCategorySemicolon:
            return false;
        default:
            return true;
    }
}

inline Token
newToken(char *first_char, CharacterCategory category)
{
    Token result;
    result.chars = first_char;
    result.length = 0;
    result.category = category;
    return result;
}

struct TokenPool
{
    s32       capacity;
    s32       count;
    Token     *tokens;
    TokenPool *next;
};

struct EngineState
{
    Memory_arena arena;
};

internal CharacterCategory
categorizeCharacter(char character)
{
    switch (character)
    {
        case ' ':
        {
            return CharacterCategorySpace;
        } break;

        case '\n':
        {
            return CharacterCategoryNewline;
        } break;

        case ';':
        {
            return CharacterCategorySemicolon;
        } break;

        // NOTE: We're not gonna reserve brackets or braces
        case '(':
        {
            return CharacterCategoryGroupBegin;
        } break;
        case ')':
        {
            return CharacterCategoryGroupEnd;
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
            return CharacterCategoryOperator;
        } break;

        default:
            return CharacterCategoryAlphabetical;
    }
}

struct ExpressionStackItem
{
    Expression *expression;
};

inline void
addTokenToPool(Memory_arena *arena, ArrayList *token_pool, char *first_char, CharacterCategory category)
{
    Token *token = arrayListAdd(token_pool, Token);
    token->chars = first_char;
    token->category = category;
    token->length = 0;
}

inline void
printStringToBuffer(char *buffer, char *first_char, s32 count)
{
    char *c = first_char;
    for (s32 index = 0 ;
         index < count;
         index++)
    {
        buffer[index] = *c;
        c++;
    }
    buffer[count] = 0;
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
printExpression(Expression *expression, s32 indentation)
{
    if (expression->op)
    {
        printExpression(expression->op, indentation+1);
        for (ArrayListIterator arg_it = getIterator(&expression->args);
             arg_it.chunk;
             advance(&arg_it))
        {
            Expression **arg = getCurrent(&arg_it, Expression *);
            printExpression(*arg, indentation+1);
        }
    }
    else
    {
        char buffer[256];
        assert(expression->name);
        printCharToBufferRepeat(buffer, ' ', indentation);
        platformPrint(buffer);

        printStringToBuffer(buffer, expression->name, expression->name_length);
        platformPrint(buffer);

        sprintf(buffer, "\n");
        platformPrint(buffer);
    }
}

internal void
engineTest(EngineMemory *memory)
{
    platformPrint = memory->platformPrint;

    if (!memory->initialized)
    {
        Memory_arena init_arena = newArena(memory->storage_size, memory->storage);
        EngineState *state = pushStruct(&init_arena, EngineState);
        state->arena = init_arena;
        memory->initialized = true;
    }

    EngineState *state = (EngineState *)memory->storage;
    Memory_arena *arena = &state->arena;

    ReadFileResult read = memory->platformReadEntireFile("test.rea");
    if (read.contents)
    {
        CharacterCategory previous_category = CharacterCategoryNull;
        s32 todo_token_pool_size = 1024;
        ArrayList *token_pool = allocateArrayList(arena, todo_token_pool_size, sizeof(Token));
        b32 being_commented = false;
        // TODO: Unicode support?
        for (s32 content_index = 0;
             content_index < read.contentsSize;
             content_index++)
        {   // MARK: tokenizing
            char *character = &((char *)read.contents)[content_index];
            CharacterCategory category = categorizeCharacter(*character);
            if (category == CharacterCategoryNewline)
                being_commented = false;

            if (!being_commented)
            {
                switch (category)
                {
                    case CharacterCategorySpace:
                    case CharacterCategoryNewline:
                    {
                        // NOTE: space means the next character makes a new token.
                    } break;

                    case CharacterCategoryGroupBegin:
                    case CharacterCategoryGroupEnd:
                    {
                        addTokenToPool(arena, token_pool, character, category);
                    } break;

                    case CharacterCategorySemicolon:
                    {
                        being_commented = true;
                    } break;

                    case CharacterCategoryOperator:
                    {
                        if (previous_category != CharacterCategoryOperator)
                        {
                            addTokenToPool(arena, token_pool, character, category);
                        }
                    } break;

                    case CharacterCategoryAlphabetical:
                    {
                        if (previous_category != CharacterCategoryAlphabetical)
                        {
                            addTokenToPool(arena, token_pool, character, category);
                        }
                    } break;

                    invalidDefaultCase;
                }

                if (partOfToken(category))
                {
                    Token *current_token =
                        (Token *)token_pool->last_chunk->items + (token_pool->last_chunk->count-1);
                    current_token->length++;
                }

                previous_category = category;
            }
        }

        {   // MARK: Parsing
            s32 todo_expression_pool_size = 1024;
            ArrayList *expression_pool = allocateArrayList(&state->arena, todo_expression_pool_size, sizeof(Expression));
            if (expression_pool->last_chunk != &expression_pool->first_chunk)
            {
                assert(expression_pool->first_chunk.next != 0);
            }
            s32 expression_count = 0;
            ExpressionStackItem expression_stack[128];
            Expression *root_expression = arrayListAdd(expression_pool, Expression);
            initializeExpression(arena, root_expression);
            root_expression->name = (char *)"<ROOT>";
            root_expression->name_length = 6;
            expression_stack[0].expression = root_expression;
            s32 stack_size = 1;
            b32 input_error = false;
            for (ArrayListIterator token_it = getIterator(token_pool);
                 token_it.chunk && (!input_error);
                 advance(&token_it))
            {
                char buffer[256];
                Token *token = getCurrent(&token_it, Token);
                printStringToBuffer(buffer, token->chars, token->length);
                platformPrint(buffer);
                sprintf(buffer, "\n");
                platformPrint(buffer);

                if (token->category == CharacterCategoryGroupEnd)
                {
                    if (stack_size > 1)  // NOTE: 0 is root.
                    {
                        stack_size--;
                        ExpressionStackItem *outer = expression_stack + stack_size-1;
                    }
                    else
                    {
                        sprintf(buffer, "Invalid end-of-expression");
                        platformPrint(buffer);
                        input_error = true;
                    }
                }
                else
                {
                    Expression *new_expression = arrayListAdd(expression_pool, Expression);
                    initializeExpression(&state->arena, new_expression);
                    ExpressionStackItem *outer = ((stack_size > 0) ? (expression_stack + stack_size-1) : 0);
                    if (outer)
                    {
                        if ((outer->expression != root_expression) && (outer->expression->op == 0))
                        {
                            outer->expression->op = new_expression;
                        }
                        else
                        {
                            Expression **arg = arrayListAdd(&outer->expression->args, Expression*);
                            *arg = new_expression;
                        }
                    }

                    if (token->category == CharacterCategoryGroupBegin)
                    {
                        ExpressionStackItem *new_outer = expression_stack + (stack_size++);
                        assert(stack_size <= arrayCount(expression_stack));
                        new_outer->expression = new_expression;
                    }
                    else
                    {
                        new_expression->name = token->chars;
                        new_expression->name_length = token->length;
                    }
                }
            }

            {// MARK: Test parsing
                for (ArrayListIterator expression_it = getIterator(&root_expression->args);
                     expression_it.chunk;
                     advance(&expression_it))
                {
                    Expression **expression = getCurrent(&expression_it, Expression*);
                    printExpression(*expression, 0);
                }
            }
        }

        // TODO: Only free when we have edits;
        memory->platformFreeFileMemory(read.contents);
    }
    else
    {
        printf("Cannot open test input file!\n");
    }
}

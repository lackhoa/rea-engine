#include "utils.h"
#include "memory.h"
#include "globals.h"
#include "platform.h"

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

struct Expression;
struct ExpressionSlot
{
    Expression *expression;
    ExpressionSlot *next;
};

struct Expression
{
    Expression *op;
    // TODO: @Memory: Do we want the arg list in the expression always? Most
    // expressions don't have args.
    ExpressionSlot args;

    // NOTE: Name is mandatory for  expressions with 0 args.
    char *name;
    s32  name_length;
};

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

enum TokenType
{
    // 0-255 reserved for single-char ASCII types.
    TokenTypeNull = 0,

    TokenTypeSpace = 256,
    TokenTypeOperator = 257,
    TokenTypeAlphabetical = 258,
};


struct Token
{
    char *chars;
    s32 length;
    TokenType type;
};

inline b32
tokenEqualString(Token *token, const char *string)
{
    b32 result = true;
    for (s32 i = 0;
         (i < token->length);
         i++)
    {
        if ((string[i] == '\0')
            || (token->chars[i] != string[i]))
        {
            result = false;
            break;
        }
    }
    return result;
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
    result.chars = first_char;
    result.length = 0;
    result.type = category;
    return result;
}

struct EngineState
{
    Memory_arena arena;
};

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

struct ExpressionStackItem
{
    Expression *expression;
};

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
        for (ExpressionSlot *arg = &expression->args;
             arg && arg->expression;
             arg = arg->next)
        {
            printExpression(arg->expression, indentation+1);
        }
    }
    else
    {
        char buffer[256];
        assert(expression->name);
        printCharToBufferRepeat(buffer, ' ', 4*indentation);
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
    if (read.content)
    {
        TokenType previous_category = (TokenTypeNull);
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
            if (token_type == TokenTypeSpace)
                being_commented = false;

            if (!being_commented)
            {
                b32 add_token = (((previous_category != token_type)
                                  || (token_type == '(')
                                  || (token_type == ')'))
                                 && (partOfToken(token_type)));

                if (add_token)
                {
                    Token *token = tokens + token_count;
                    token_count += 1;
                    token->chars = character;
                    TokenType token_category;
                    token->type = token_type;
                    token->length = 0;
                }

                b32 token_extended = partOfToken(token_type);
                if (token_extended)
                {
                    tokens[token_count-1].length++;
                }

                previous_category = token_type;
            }
        }

        {   // MARK: Parsing
            s32 todo_expression_chunk_size = 1024;
            ArrayList *expressions = allocateArrayList(&state->arena, todo_expression_chunk_size, sizeof(Expression));
            if (expressions->last_chunk != &expressions->first_chunk)
            {
                assert(expressions->first_chunk.next != 0);
            }
            s32 expression_count = 0;
            ExpressionStackItem expression_stack[128];
            Expression *root_expression = arrayListAdd(expressions, Expression);
            *root_expression = {};
            root_expression->name = (char *)"<ROOT>";
            root_expression->name_length = 6;
            expression_stack[0].expression = root_expression;
            s32 stack_size = 1;
            b32 input_error = false;
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
                    Expression *new_expression = pushStructZero(arena, Expression);
                    ExpressionStackItem *outer = ((stack_size > 0) ?
                                                  (expression_stack + stack_size-1) : 0);
                    if ((outer->expression != root_expression) && (outer->expression->op == 0))
                    {
                        outer->expression->op = new_expression;
                    }
                    else
                    {
                        if (!outer->expression->args.expression)
                            outer->expression->args.expression = new_expression;
                        else
                        {
                            ExpressionSlot *final_arg = &outer->expression->args;
                            while (final_arg->next != 0)
                            {
                                final_arg = final_arg->next;
                            }
                            final_arg->next = pushStruct(arena, ExpressionSlot);
                            final_arg->next->expression = new_expression;
                            final_arg->next->next = 0;
                        }
                    }

                    if (token->type == '(')
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
                for (ExpressionSlot *arg = &root_expression->args;
                     arg && arg->expression;
                     arg = arg->next)
                {
                    printExpression(arg->expression, 0);
                }
            }
        }

        // TODO: Only free when we have edits;
        memory->platformFreeFileMemory(read.content);
    }
    else
    {
        printf("Cannot open test input file!\n");
    }
}

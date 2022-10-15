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
    Tokenizer   *tk         = global_tokenizer;  (void) tk; \
    MemoryArena *temp_arena = global_temp_arena; (void) temp_arena; \

enum ExpressionCategory
{
    EC_Unknown,
    EC_Variable,                // reference to some unknown on "the stack"
    EC_Application,             // operator application
    EC_Switch,                  // switch statement
    EC_Form,                    // like Coq inductive types
    EC_Constructor,             // canonical members of structs
    EC_Procedure,               // holds actual computation (ie body that can be executed)
    EC_ArrowType,               // type of procedure and built-in objects
    EC_Hole,                    // hole left in for type-checking
    EC_Macro,                   // just like the name says, it's a macro

    EC_Builtin_identical,
    EC_Builtin_Set,
    EC_Builtin_Prop,
    EC_Builtin_Proc,
    EC_Builtin_Type,
};

#define castExpression(Type, exp) ((exp)->cat == EC_##Type) ? &(exp)->Type : 0;

struct Expression;

// NOTE: this is just a dummy struct for us to debug scopes.
struct Scope { char *at; };

inline Scope *
newScope(MemoryArena *arena, char* at)
{
    auto scope = pushStruct(arena, Scope);
    scope->at = at;
    return scope;
}

struct Stack
{
    MemoryArena  *arena;
    Scope        *scope;
    s32           count;
    Expression  **args;
    Stack        *next;
};

struct Variable
{
    String      name;
    Expression **value;  // pointer to a stack location
    s32         stack_delta;
    u32         id;

    Scope  *scope;
};

inline void
initVariable(Variable *var, String name, u32 id, Scope *scope)
{
    var->name        = name;
    var->stack_delta = 0;
    var->id          = id;
    var->scope       = scope;
}

struct Application
{
    Expression  *op;
    s32          arg_count;
    Expression **args;
};

struct Switch
{
    Expression  *subject;
    Expression **case_bodies;
    s32          case_count;
};

struct Constructor
{
    s32     id;
    String  name;
};

struct Form
{
    String      name;
    s32         ctor_count;
    Expression *ctors;  // note: We don't hold arbitrary expressions here, only
                        // constructors. But storing full expressions here is
                        // more convenient since then you don't need a separate
                        // type with constructor id and then jump through hoops
                        // to get back the constructor info.
};

// NOTE: most of the information is in the (arrow) type;
struct Procedure
{
    String      name;
    Expression *body;
};

struct ArrowType
{
    s32          param_count;
    Expression **params;
    Expression  *return_type;
    Scope       *scope;
};

// IMPORTANT: All expressions are well-typed (except in parsing phase).
struct Expression
{
    ExpressionCategory  cat;
    Expression         *type;  // IMPORTANT: always in normal form
    union
    {
        Variable       Variable;
        Application    Application;
        Switch         Switch;
        Form           Form;
        Constructor    Constructor;
        Procedure      Procedure;
        ArrowType      ArrowType;
    };
};

global_variable Expression *builtin_identical;
global_variable Expression *builtin_identical_macro;
global_variable Expression *builtin_True;
global_variable Expression *builtin_truth;
global_variable Expression *builtin_False;
global_variable Expression *builtin_Set;
global_variable Expression *builtin_Prop;
global_variable Expression *builtin_Proc;
global_variable Expression *builtin_Type;
global_variable Expression *hole_expression;

inline s32
switchCtorCount(Switch *myswitch)
{
    return myswitch->subject->type->Form.ctor_count;
}

internal void
printExpression(MemoryArena *buffer, Expression *exp, b32 detailed = false)
{
    b32 print_type = detailed ? true : false;
    switch (exp->cat)
    {
        case EC_Variable:
        {
            auto var = castExpression(Variable, exp);
            myprint(buffer, "%.*s", var->name.length, var->name.chars);
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
            auto subject_struct = castExpression(Form, myswitch->subject->type);
            for (s32 ctor_id = 0;
                 ctor_id < subject_struct->ctor_count;
                 ctor_id++)
            {
                printExpression(buffer, subject_struct->ctors + ctor_id);
                myprint(buffer, " -> ");
                printExpression(buffer, myswitch->case_bodies[ctor_id]);
                if (ctor_id != subject_struct->ctor_count-1)
                    myprint(buffer, ", ");
            }
            myprint(buffer, "}");
        } break;

        case EC_Form:
        {
            auto mystruct = &exp->Form;
            myprint(buffer, mystruct->name);
        } break;

        case EC_Procedure:
        {
            print_type = false; // we print type in the following code
            auto proc = castExpression(Procedure, exp);
            auto signature = castExpression(ArrowType, exp->type);
            myprint(buffer, proc->name);
            if (detailed)
            {
                myprint(buffer, "(");
                for (int arg_id = 0;
                     arg_id < signature->param_count;
                     arg_id++)
                {
                    auto arg = signature->params[arg_id];
                    printExpression(buffer, arg);
                    myprint(buffer, ": ");
                    printExpression(buffer, arg->type);
                    if (arg_id < signature->param_count-1)
                        myprint(buffer, ", ");
                }
                myprint(buffer, ") => ");

                printExpression(buffer, proc->body);
                myprint(buffer, " : ");

                printExpression(buffer, signature->return_type);
            }
        } break;

        case EC_Constructor:
        {
            auto ctor = castExpression(Constructor, exp);
            myprint(buffer, ctor->name);
        } break;

        case EC_ArrowType:
        {
            auto arrow = castExpression(ArrowType, exp);
            myprint(buffer, "(");
            for (int arg_id = 0;
                 arg_id < arrow->param_count;
                 arg_id++)
            {
                printExpression(buffer, arrow->params[arg_id], true);
                if (arg_id < arrow->param_count-1)
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

    if (print_type)
    {
        myprint(buffer, " : ");
        printExpression(buffer, exp->type);
    }
}

inline void
initExpression(Expression *in, ExpressionCategory cat, Expression *type)
{
    in->cat  = cat;
    in->type = type;
}

inline Expression *
newExpression(MemoryArena *arena, ExpressionCategory cat, Expression *type)
{
    auto out = pushStruct(arena, Expression);
    initExpression(out, cat, type);
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
    MemoryArena *arena;
    Binding      first[128];  // NOTE: this is hash table
    Bindings    *next;
};

global_variable Bindings *global_bindings;

internal Expression *
parseExpression(MemoryArena *arena, Bindings *bindings, s32 min_precedence = -9999);

// todo why not allow the stack frame to alter the arena here?
internal Stack
extendStack(Stack *outer, Scope *scope, u32 arg_count, Expression **in_args)
{    
    Stack out = {};

    out.arena = outer->arena;
    out.scope = scope;
    out.count = arg_count;
    out.args  = in_args;
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
    out->next    = outer;
    out->arena   = arena;
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

inline b32
addGlobalName(String key, Expression *value)
{
    auto lookup = lookupNameCurrentFrame(global_bindings, key, true);
    b32 succeed = true;
    if (lookup.found)
        succeed = false;
    else
        lookup.slot->value = value;
    return succeed;
}

inline b32
addGlobalName(char *key, Expression *value)
{
    return addGlobalName(toString(key), value);
}

struct LookupNameRecursive { Expression *value; b32 found; };

inline LookupNameRecursive
lookupNameRecursive(MemoryArena *arena, Bindings *bindings, Token *token)
{
    Expression *value = {};
    b32 found = false;

    for (b32 stop = false, stack_delta = 0;
         !stop;
         stack_delta++)
    {
        LookupName lookup = lookupNameCurrentFrame(bindings, token->text, false);
        if (lookup.found)
        {
            found = true;
            stop = true;
            value = lookup.slot->value;
            if ((value->cat == EC_Variable) && (stack_delta != 0))
            {
                assert(value->Variable.stack_delta == 0);
                // todo: we're copying variable, which is kinda bad.
                allocate(arena, value);
                *value = *lookup.slot->value;
                value->Variable.stack_delta = stack_delta;
            }
        }
        else
        {
            if (bindings->next)
            {
                bindings = bindings->next;
            }
            else
                stop = true;
        }
    }

    LookupNameRecursive out = { value, found };
    return out;
}

internal void
parseErrorVA(Token *token, char *format, va_list arg_list, Tokenizer *tk = global_tokenizer)
{

    assert(!tk->error);  // note: prevent parser from doing huge amount of
                         // useless work after failure (#speed).

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
parseError(Tokenizer *tk, Token *token, char *format, ...)
{
    va_list arg_list;
    __crt_va_start(arg_list, format);
    parseErrorVA(token, format, arg_list, tk);
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
requireChar(Tokenizer *tk, char c, char *reason = 0)
{
    auto out = false;
    if (!reason)
        reason = "<no reason provided>";
    if (parsing(tk))
    {
        Token token = nextToken(tk);
        if (token.text.length == 1 && token.text.chars[0] == c)
            out = true;
        else
            parseError(&token, "expected character '%c' (%s)", c, reason);
    }
    return out;
}

inline b32
requireChar(char c, char *reason = 0)
{
    return requireChar(global_tokenizer, c, reason);
}

inline b32
requireCategory(TokenCategory tc, char *message, Tokenizer *tk = global_tokenizer)
{
    b32 out = false;
    if (parsing())
    {
        if (nextToken(tk).cat == tc)
            out = true;
        else
            tokenError(message);
    }
    return out;
}

inline b32
optionalChar(Tokenizer *tk, char c)
{
    b32 out = false;
    Token token = peekNext(tk);
    if (equals(&token, c))
    {
        out = true;
        nextToken(tk);
    }
    return out;
}

inline b32
optionalChar(char c)
{
    return optionalChar(global_tokenizer, c);
}

internal s32
getCommaSeparatedListLength(Tokenizer *tk)
{
    Token opening_token = tk->last_token;
    char opening = opening_token.text.chars[0];
    char closing = getMatchingPair(opening);
    assert(closing);
    char previous = opening;
    s32 out = 0;
    for (b32 stop = false; !stop;)
    {
        Token token = nextToken(tk);
        if (!parsing(tk))
        {
            stop = true;
            parseError(tk, &opening_token, "could not find matching pair for");
        }
        else
        {
            char matching_pair = getMatchingPair(token.text.chars[0]);
            if (matching_pair)
            {
                if (!eatUntil(matching_pair, tk))
                    parseError(tk, &token, "could not find matching pair for");
            }
            else if (equals(&token, closing))
            {
                if ((previous != ',') && (previous != opening))
                    out++;
                stop = true;
            }
            else if (equals(&token, ','))
                out++;
            previous = tk->last_token.text.chars[0];
        }
    }
    return out;
}

internal b32
addGlobalNameBinding(String key, Expression *value)
{
    b32 succeed = false;
    LookupName lookup = lookupNameCurrentFrame(global_bindings, key, true);
    if (!lookup.found)
    {
        succeed = true;
        lookup.slot->value = value;
    }
    return succeed;
}

internal void
addBuiltinForm(MemoryArena *arena, char *name, const char **ctor_names, s32 ctor_count, Expression *type)
{
    auto exp = newExpression(arena, EC_Form, type);
    auto form_name = toString(name);
    assert(addGlobalNameBinding(form_name, exp));

    Form *form = &exp->Form;
    form->name = form_name;
    form->ctor_count = ctor_count;
    allocateArray(arena, form->ctor_count, form->ctors);

    for (auto ctor_id = 0; ctor_id < ctor_count; ctor_id++)
    {
        auto ctor_exp = form->ctors + ctor_id;
        initExpression(ctor_exp, EC_Constructor, exp);
        auto ctor  = &ctor_exp->Constructor;
        ctor->name = toString((char*)ctor_names[ctor_id]);
        ctor->id   = ctor_id;
        assert(addGlobalNameBinding(ctor->name, ctor_exp));
    }
}

struct OptionalU32 { b32 success; u32 value; };

enum Trinary
{
    Trinary_Unknown, Trinary_False, Trinary_True,
};

internal Trinary
compareExpressions(Expression *lhs, Expression *rhs);

internal Trinary
compareExpressionList(Expression **lhs_list, Expression **rhs_list, s32 count)
{
    Trinary out = Trinary_Unknown;
    b32 mismatch_found = false;
    b32 unknown_found  = false;
    for (s32 id = 0;
         (id < count) && !mismatch_found;
         id++)
    {
        auto lhs = lhs_list[id];
        auto rhs = rhs_list[id];
        auto compare = compareExpressions(lhs, rhs);
        if (compare == Trinary_Unknown)
            unknown_found = true;
        if (compare == Trinary_False)
            mismatch_found = true;
    }
    if (mismatch_found)
        out = Trinary_False;
    else if (unknown_found)
        out = Trinary_Unknown;   
    else
        out = Trinary_True;

    return out;
}

inline b32
isCompositeConstructor(Expression *expression)
{
    return ((expression->cat == EC_Application)
            && (expression->Application.op->cat == EC_Constructor));
}

// NOTE: values going in must be normalized
// NOTE: we need a trinary return value to detect if the comparison is false.
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
                if (lhs->Variable.value == rhs->Variable.value)
                {
                    out = Trinary_True;
                }
            } break;

            case EC_Constructor:
            {
                if (lhs->Constructor.id == rhs->Constructor.id)
                    out = Trinary_True;
                else
                    out = Trinary_False;
            } break;

            case EC_ArrowType:
            {
                // todo: important: comparison of dependent types wouldn't work
                // if we compare the scopes. we can fix it by comparing
                // stack_delta (which we're not storing right now)
                auto larrow = castExpression(ArrowType, lhs);
                auto rarrow = castExpression(ArrowType, rhs);
                Trinary return_type_compare = compareExpressions(larrow->return_type, rarrow->return_type);
                if (return_type_compare == Trinary_False)
                    out = Trinary_False;
                else if (return_type_compare == Trinary_True)
                {
                    auto param_count = larrow->param_count;
                    if (rarrow->param_count == param_count)
                    {
                        auto lparam_types = pushArray(global_temp_arena, param_count, Expression*);
                        auto rparam_types = pushArray(global_temp_arena, param_count, Expression*);

                        for (s32 param_id = 0;
                             param_id < param_count;
                             param_id++)
                        {
                            lparam_types[param_id] = larrow->params[param_id]->type;
                            rparam_types[param_id] = rarrow->params[param_id]->type;
                        }

                        out = compareExpressionList(lparam_types, rparam_types, param_count);
                    }
                    else
                        out = Trinary_False;
                }
            } break;

            case EC_Switch:
            {
                out = Trinary_Unknown;
            } break;

            case EC_Application:
            {
                auto lapp = castExpression(Application, lhs);
                auto rapp = castExpression(Application, rhs);
                if ((lapp->op->cat == EC_Constructor)
                    && (rapp->op->cat == EC_Constructor))
                {
                    Trinary op_compare = compareExpressions(lapp->op, rapp->op);
                    if (op_compare == Trinary_False)
                        out = Trinary_False;
                    else
                    {
                        assert(op_compare == Trinary_True);
                        assert(lapp->arg_count == rapp->arg_count);
                        out = compareExpressionList(lapp->args, rapp->args, lapp->arg_count);
                    }
                }
                Trinary op_compare = compareExpressions(lapp->op, rapp->op);
                if (op_compare == Trinary_False)
                {
                }
            } break;

            case EC_Form:
            {
                out = Trinary_False;
            } break;

            default:
                todoIncomplete;
        }
    }
    else if (((lhs->cat == EC_Constructor) && isCompositeConstructor(rhs)) ||
             ((rhs->cat == EC_Constructor) && isCompositeConstructor(lhs)))
    {
        out = Trinary_False;
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
precedenceOf(Expression *op)
{
    int out = 0;
    // TODO: implement for real
    switch (op->cat)
    {
        case EC_Procedure:
        {
            String name = op->Procedure.name;
            if (equals(name, "&")
                || equals(name, "*"))
                out = 20;
            else if (equals(name, "|")
                     || equals(name, "+")
                     || equals(name, "-"))
                out = 10;
            else
                out = 100;
        } break;

        case EC_Constructor:
        {
            out = 100;
        } break;

        case EC_Macro:
        {
            out = 0;
        } break;

        invalidDefaultCase;
    }

    return out;
}

internal Expression *
getArgType(Expression *op, s32 arg_id)
{
    auto signature = castExpression(ArrowType, op->type);
    assert(arg_id < signature->param_count);
    return signature->params[arg_id]->type;
}

#if 0
inline Expression *
transformVariables(MemoryArena *arena, Stack *stack, s32 stack_delta, Expression *in)
{
    Expression *out = in;
    switch(in->cat)
    {
        case EC_Variable:
        {
            if(in->Variable.stack_delta == stack_delta)
            {
                allocate(arena, out);
                *out = *in;
                assert(out->Variable.id < stack->count);
                out->Variable.value = stack->args + out->Variable.id;
            }
        } break;

        case EC_Application:
        {
            allocate(arena, out);
            *out = *in;
            out->Application.op = transformVariables(arena, stack, stack_delta, in->Application.op);
            for (s32 arg_id = 0; arg_id < in->Application.arg_count; arg_id++)
            {
                out->Application.args[arg_id] = transformVariables(arena, stack, stack_delta, in->Application.args[arg_id]);
            }
        } break;

        case EC_Switch:
        {
            allocate(arena, out);
            *out = *in;
            out->Switch.subject = transformVariables(arena, stack, stack_delta, in->Switch.subject);
            for (s32 case_id = 0;
                 case_id < in->Switch.case_count;
                 case_id++)
            {
                out->Switch.case_bodies[case_id] = transformVariables(arena, stack, stack_delta+1, in->Switch.case_bodies[case_id]);
            }
        } break;

        case EC_Procedure:
        {
            allocate(arena, out);
            *out = *in;
            out->Procedure.body = transformVariables(arena, stack, stack_delta+1, in->Procedure.body);
        } break;
    }
    return out;
}
#endif

internal Expression *
normalize(MemoryArena *arena, Stack *stack, s32 stack_offset, Expression *in)
{
    Expression *out = 0;
    unpackGlobals;

    switch (in->cat)
    {
        case EC_Variable:
        {
            s32 stack_delta = in->Variable.stack_delta - stack_offset;
            if (stack_delta >= 0)
            {
                for (s32 id = 0; id < stack_delta; id++)
                    stack = stack->next;
                assert(in->Variable.scope == stack->scope);
                Expression *resolved = stack->args[in->Variable.id];
                if (resolved)
                    out = resolved;
            }
        } break;

        case EC_Application:
        {
            auto in_app = &in->Application;
            Expression **norm_args = pushArray(temp_arena, in_app->arg_count, Expression*);
            for (auto arg_id = 0;
                 arg_id < in_app->arg_count;
                 arg_id++)
            {
                Expression *in_arg = in_app->args[arg_id];
                norm_args[arg_id]  = normalize(arena, stack, stack_offset, in_arg);
            }

            Expression *norm_op = normalize(arena, stack, stack_offset, in_app->op);
            if (norm_op->cat == EC_Procedure)
            {
                ArrowType *signature = &norm_op->type->ArrowType;
                Stack new_env = extendStack(stack, signature->scope, in_app->arg_count, norm_args);
                out = normalize(arena, &new_env, stack_offset, norm_op->Procedure.body);
            }
            else
            {
                if (norm_op->cat == EC_Builtin_identical)
                {// special case for equality
                    auto compare = compareExpressions(norm_args[1], norm_args[2]);
                    if (compare == Trinary_True)
                        out = builtin_True;
                    else if (compare == Trinary_False)
                        out = builtin_False;
                }

                if (!out)
                {
                    // TODO: don't allocate if the out & in are identical.
                    assert(in->type);
                    out = newExpression(arena, EC_Application, in->type);
                    auto app = castExpression(Application, out);

                    app->op        = norm_op;
                    app->arg_count = in_app->arg_count;
                    allocateArray(arena, app->arg_count, app->args);
                    for (int arg_id = 0; arg_id < app->arg_count; arg_id++)
                        app->args[arg_id] = norm_args[arg_id];
                }
            }
        } break;

        case EC_Switch:
        {
            auto myswitch = &in->Switch;
            Expression *subject_norm = normalize(arena, stack, stack_offset, myswitch->subject);

            auto subject_type   = subject_norm->type;

            Stack case_stack;
            Constructor *ctor = 0;
            switch (subject_norm->cat)
            {
                case EC_Constructor:
                {
                    ctor = &subject_norm->Constructor;
                    case_stack = extendStack(stack, 0, 0, 0);
                } break;

                case EC_Application:
                {
                    auto app = castExpression(Application, subject_norm);
                    ctor = castExpression(Constructor, app->op);
                    if (ctor)
                    {
                        auto signature = castExpression(ArrowType, app->op->type);
                        case_stack = extendStack(stack, signature->scope, signature->param_count, app->args);
                    }
                } break;
            }

            if (ctor)
                out = normalize(arena, &case_stack, stack_offset, myswitch->case_bodies[ctor->id]);
            else
            {
                // important: we can't normalize the bodies since they can recurse infinitely.
#if 1
                auto switch_struct = castExpression(Form, subject_type);
                auto ctor_count    = switch_struct->ctor_count;
                auto norm_bodies   = pushArray(arena, switch_struct->ctor_count, Expression*);
                for (int ctor_id = 0; ctor_id < ctor_count; ctor_id++)
                {
                    Expression *ctor_exp = switch_struct->ctors + ctor_id;
                    auto   param_count = 0;
                    auto   signature   = castExpression(ArrowType, ctor_exp->type);
                    Scope *scope       = 0;
                    if (signature)
                    {
                        param_count = signature->param_count;
                        scope       = signature->scope;
                    }
                    auto case_stack = extendStack(stack, scope, param_count, 0);
                    norm_bodies[ctor_id] = normalize(arena, &case_stack, stack_offset, myswitch->case_bodies[ctor_id]);
                }
#endif

                if (!out)
                {
                    if (subject_norm != myswitch->subject)
                    {
                        out = newExpression(arena, EC_Switch, subject_type);
                        out->Switch.subject     = subject_norm;
                        out->Switch.case_bodies = norm_bodies;
                        out->Switch.case_count  = in->Switch.case_count;
                    }
                }
            }
        } break;
    }    

    if (!out)
        out = in;

    return out;
}

internal Expression *
newApplication(MemoryArena *arena, Token *blame_token,
               Expression *op, Expression **args, s32 arg_count)
{
    unpackGlobals;
    Expression *out = 0;

    auto signature = castExpression(ArrowType, op->type);
    if (signature)
    {
        if (signature->param_count == arg_count)
        {
            out = newExpression(arena, EC_Application, 0);
            auto app = &out->Application;
            app->op = op;
            app->arg_count = arg_count;
            allocateArray(arena, arg_count, app->args);

            Stack stack = {};
            stack.arena = arena;
            stack.scope = signature->scope;
            allocateArrayZero(temp_arena, arg_count, stack.args);
            stack.count = arg_count;

            for (int arg_id = 0, stop = 0;
                 (arg_id < signature->param_count) && !stop;
                 arg_id++)
            {
                auto arg = args[arg_id];
                stack.args[arg_id] = args[arg_id];
                Expression *param = signature->params[arg_id];
                auto param_type = normalize(temp_arena, &stack, 0, param->type);
                if (arg->cat == EC_Hole)
                {
                    // NOTE: this expression is still free, it can be anything.
                    // todo: we don't check afterward if the hole has been filled.
                    // just put a variable here
                    stack.args[arg_id] = signature->params[arg_id];
                }
                else if (param_type->cat == EC_Variable)
                {
                    // since the type is still variable, accept it unconditionally.
                    app->args[arg_id] = arg;

                    // write back the new value to the original variable
                    auto var = &param_type->Variable;
                    assert(var->scope == stack.scope);
                    stack.args[var->id] = arg->type;
                    app->args[var->id]   = arg->type;
                }
                else if (expressionsIdenticalB32(arg->type, param_type))
                {
                    app->args[arg_id] = arg;
                }
                else
                {
                    out = 0;
                    parseError(blame_token, "argument %d has wrong type", arg_id);
                    pushAttachment(tk, "got", arg->type);
                    pushAttachment(tk, "expected", param_type);
                    stop = true;
                }
            }

            if (parsing())
                out->type = normalize(arena, &stack, 0, signature->return_type);
        }
        else
            parseError(blame_token, "incorrect arg count: %d (procedure expected %d)", arg_count, signature->param_count);
    }
    else
        tokenError(blame_token, "operator must have an arrow type");
    
    assert(out->type);
    return out;
}

// NOTE: People who use it (like the expression parser) only know that they have
// an operator and some operands (all of which are expressions), and it's up to
// this function to make combine them however it can (including macro expansion,
// typecheck, unification...).
internal Expression *
combineExpressions(MemoryArena *arena, Token *blame_token, Expression *op, Expression **args, s32 arg_count)
{
    if (op->cat == EC_Macro)
    {
        // macro overlay. todo only support builtin equality for now
        op = builtin_identical;
        assert(arg_count == 2);
        arg_count = 3;
        Expression *new_args[3];
        new_args[0] = hole_expression;
        new_args[1] = args[0];
        new_args[2] = args[1];
        args = new_args;
    }

    return newApplication(arena, blame_token, op, args, arg_count);
}

// note: this modifies the bindings, returns the matched id
internal Constructor *
parseSwitchPattern(MemoryArena *arena, Bindings *bindings, Expression *expected_struct)
{
    unpackGlobals;
    pushContext;

    (void)arena;
    Constructor *ctor = 0;
    Token ctor_token = nextToken(tk);
    if (isIdentifier(&ctor_token))
    {
        auto lookup = lookupNameRecursive(arena, bindings, &ctor_token);
        if (!lookup.found)
            tokenError("unbound identifier in expression");
        {
            auto ctor_exp = lookup.value;
            ctor = castExpression(Constructor, ctor_exp);
            if (!ctor)
                tokenError("expected a constructor in switch pattern");
            else if (ctor_exp->type->cat == EC_ArrowType
                     && optionalChar('('))
            {// composite constructor
                auto op = ctor_exp;
                auto signature = &op->type->ArrowType;

                if (!expressionsIdenticalB32(signature->return_type, expected_struct))
                {
                    tokenError("constructor of wrong type");
                    pushAttachment("expected type:", expected_struct);
                    pushAttachment("got type:", signature->return_type);
                }
                else
                {
                    s32 parsed_param_count = 0;
                    for (s32 stop = false, param_id = 0;
                         !stop && parsing();
                         param_id++)
                    {
                        auto arg_token = nextToken();
                        if (arg_token.cat == ')')
                            stop = true;
                        else if (!isIdentifier(&arg_token))
                            tokenError("expected pattern variable");
                        else
                        {
                            auto lookup = lookupNameCurrentFrame(bindings, arg_token.text, true);
                            if (lookup.found)
                                tokenError("reused parameter name");
                            else
                            {
                                assert(signature->params[param_id]);
                                lookup.slot->value = signature->params[param_id];
                                parsed_param_count++;

                                if (!optionalChar(','))
                                {
                                    requireChar(')');
                                    stop = true;
                                }
                            }
                        }
                    }
                    if (parsed_param_count != signature->param_count)
                        parseError(&ctor_token, "pattern has wrong amount of parameters (expected: %d, got: %d)", signature->param_count, parsed_param_count);
                }
            }
            else if (!expressionsIdenticalB32(ctor_exp->type, expected_struct))
            {
                tokenError("constructor of wrong type");
                pushAttachment("expected type:", expected_struct);
                pushAttachment("got type:", ctor_exp->type);
            }
        }
    }
    else
        tokenError("expected an identifier");

    popContext(tk);
    return ctor;
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
    if (requireChar(tk, '{', "to open the typedef body"))
    {
        Expression *subject_type = myswitch->subject->type;
        if (subject_type->cat == EC_Form)
        {
            auto subject_struct = &subject_type->Form;
            auto expected_ctor_count = subject_struct->ctor_count;
            allocateArray(arena, expected_ctor_count, myswitch->case_bodies);

            s32 actual_case_count = 0;
            Expression *switch_type = 0;
            for (b32 stop = false;
                 !stop && parsing();)
            {
                if (optionalChar('}'))
                    stop = true;
                else
                {
                    auto case_bindings = extendBindings(temp_arena, bindings);
                    {
                        auto bindings = case_bindings;
                        Constructor *ctor = parseSwitchPattern(arena, bindings, subject_type);
                        if (parsing() && ctor)
                        {
                            if (requireCategory(TC_Arrow, "syntax: CASE -> BODY"))
                            {
                                auto body_token = peekNext(tk);
                                auto body = parseExpression(arena, bindings);
                                if (parsing())
                                {
                                    if (!switch_type)
                                        switch_type = body->type;
                                    else if (!expressionsIdenticalB32(body->type, switch_type))
                                    {
                                        parseError(&body_token, "mismatched return type in input case %d", actual_case_count);
                                        pushAttachment("got", body->type);
                                        pushAttachment("expected", switch_type);
                                        stop = true;
                                    }

                                    myswitch->case_bodies[ctor->id] = body;
                                    actual_case_count++;

                                    if (!optionalChar(tk, ','))
                                    {
                                        requireChar('}', "to end switch expression; or you might need ',' to end the switch case");
                                        stop = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if (parsing())
            {
                myswitch->case_count = actual_case_count;
                if (actual_case_count != expected_ctor_count)
                {
                    parseError(&token1, "wrong number of cases, expected: %d, got: %d",
                               expected_ctor_count, actual_case_count);
                }
                else if (actual_case_count == 0)
                {
                    // TODO: support empty switch later.
                    tokenError(&token1, "cannot assign type to empty switch expression");
                    out->type = 0;
                }
                else
                    out->type = switch_type;
            }
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
    Token token1 = nextToken(tk);
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
    else if (equals(&token1, '_'))
    {
        out = hole_expression;
    }
    else if (isIdentifier(&token1))
    {
        auto lookup = lookupNameRecursive(arena, bindings, &token1);
        if (lookup.found)
            out = lookup.value;
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
        tokenError("expected start of expression");

    if (parsing(tk))
    {
        Token funcall = peekNext(tk);
        if (equals(&funcall, '('))
        {// function call syntax, let's keep going
            nextToken(tk);
            auto op = out;
            if (op->type->cat == EC_ArrowType)
            {
                auto signature = &op->type->ArrowType;
                auto args = pushArray(arena, signature->param_count, Expression*);
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
                        if (parsing(tk))
                        {
                            args[arg_id] = arg;

                            for (b32 non_comma = false; !non_comma;)
                            {// eat all commas for now
                                if (*tk->at == ',')
                                    nextToken(tk);
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
                    out = combineExpressions(arena, &funcall, op, args, actual_arg_count);
                }
            }
            else
                tokenError(&token1, "cannot call non-procedure");
        }
    }

    popContext(tk);
    return out;
}

internal Expression *
parseExpression(MemoryArena *arena, Bindings *bindings, s32 min_precedence)
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
                auto op_lookup = lookupNameRecursive(arena, bindings, &op_token);
                if (op_lookup.found)
                {
                    Expression *op = op_lookup.value;
                    auto precedence = precedenceOf(op);
                    if (precedence >= min_precedence)
                    {
                        // recurse
                        nextToken(tk);
                        // a + b * c
                        //      ^
                        Expression *recurse = parseExpression(arena, bindings, precedence);
                        if (parsing(tk))
                        {
                            Expression *args[2];
                            args[0] = out;
                            args[1] = recurse;
                            out = combineExpressions(arena, &op_token, op, args, 2);
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

internal void
parseConstructorDef(MemoryArena *arena, Expression *mystruct, s32 ctor_id, Expression *out)
{
    unpackGlobals;
    pushContext;
    initExpression(out, EC_Constructor, 0);
    auto ctor = &out->Constructor;

    Token ctor_token = nextToken(tk);
    if (isIdentifier(&ctor_token))
    {
        LookupName ctor_lookup = lookupNameCurrentFrame(global_bindings, ctor_token.text, true);
        if (ctor_lookup.found)
            tokenError("redefinition of constructor name");
        else
        {
            ctor->id   = ctor_id;
            ctor->name  = ctor_token.text;

            ctor_lookup.slot->value = out;

            if (optionalChar('('))
            {
                Scope *scope = newScope(arena, tk->last_token.text.chars);

                Tokenizer tk_save = *tk;
                auto expected_arg_count = getCommaSeparatedListLength(tk);
                *tk = tk_save;

                // note: not really a "proc", but ikd what's the harm
                auto type = newExpression(arena, EC_ArrowType, builtin_Proc);
                out->type = type;
                auto signature = castExpression(ArrowType, type);
                signature->return_type = mystruct;
                signature->scope       = scope;
                allocateArray(arena, expected_arg_count, signature->params);
                for (s32 stop = false; !stop && parsing(); )
                {
                    if (optionalChar(')'))
                        stop = true;
                    else
                    {
                        auto param_type = parseExpression(arena, global_bindings);
                        if (parsing())
                        {
                            auto param_id = signature->param_count++;
                            auto param    = newExpression(arena, EC_Variable, param_type);

                            initVariable(&param->Variable, toString("no_name"), param_id, scope);

                            signature->params[param_id] = param;
                            if (!optionalChar(','))
                            {
                                requireChar(')');
                                stop = true;
                            }
                        }
                    }
                }
                if (parsing())
                    assert(signature->param_count == expected_arg_count);
            }
            else
                out->type = mystruct;
        }
    }
    else
        tokenError("expected an identifier as constructor name");

    popContext();
}

internal void
parseTypedef(MemoryArena *arena)
{
    unpackGlobals;
    pushContext;

    Token type_name = nextToken(tk);
    if (isIdentifier(&type_name))
    {
        // NOTE: the type is in scope of its own constructor.
        LookupName lookup = lookupNameCurrentFrame(global_bindings, type_name.text, true);
        if (lookup.found)
            tokenError("redefinition of type");
        else if (requireChar(':'))
        {
            Expression *type_of_type = parseExpression(arena, global_bindings);
            if (parsing())
            {
                auto *struct_exp = newExpression(arena, EC_Form, type_of_type);
                lookup.slot->value = struct_exp;

                Form *mystruct = &struct_exp->Form;
                mystruct->name = type_name.text;

                requireChar(tk, '{');

                Tokenizer tk_save = *tk;
                s32 expected_case_count = getCommaSeparatedListLength(tk);
                *tk = tk_save;
                allocateArray(arena, expected_case_count, mystruct->ctors);

                for (s32 stop = 0;
                     !stop && parsing();)
                {
                    if (optionalChar('}'))
                        stop = true;
                    else
                    {
                        auto ctor_id = mystruct->ctor_count++;
                        parseConstructorDef(arena, struct_exp, ctor_id, mystruct->ctors + ctor_id);
                        if (!optionalChar(','))
                        {
                            requireChar(tk, '}', "to end the typedef; or you might want a comma ',' to delimit constructors");
                            stop = true;
                        }
                    }
                }

                if (parsing())
                {
                    assert(mystruct->ctor_count == expected_case_count);
                    assert(lookupNameCurrentFrame(global_bindings, type_name.text).found);
                }
            }
        }
    }

    popContext();
}

internal Expression *
parseProof(MemoryArena *arena, Bindings *bindings, Stack *stack, Expression *goal)
{
    Expression *out = 0;

    unpackGlobals;
    pushContext;

    goal = normalize(temp_arena, stack, 0, goal);

    Token token = nextToken(tk);
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
                    auto subject_struct = castExpression(Form, subject_type);
                    if (subject_struct)
                    {
                        auto ctor_count = subject_struct->ctor_count;
                        allocateArray(arena, ctor_count, myswitch->case_bodies);
                        myswitch->case_count = ctor_count;
                        for (s32 ctor_id = 0;
                             (ctor_id < ctor_count) && parsing(tk);
                             ctor_id++)
                        {
                            if (optionalChar('-'))
                            {
                                // todo: what if we switched over composite expression as subject? the stack wouldn't help at all.
                                Expression *ctor_exp           = subject_struct->ctors + ctor_id;
                                stack->args[subject_var->id]  = ctor_exp;
#if 0
                                Expression *subgoal            = normalize(temp_arena, stack, goal);
#endif

                                Expression *subproof           = parseProof(temp_arena, bindings, stack, goal);
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

    Token define_name = nextToken(tk);
    if ((define_name.cat == TC_Alphanumeric)
        || (define_name.cat == TC_Special))
    {
        auto define_slot = lookupNameCurrentFrame(global_bindings, define_name.text, true);
        if (define_slot.found)
            tokenError("re-definition");
        else if (requireChar(tk, '(', "to begin argument list"))
        {
            Token param_list_token = tk->last_token;
            Scope *scope = newScope(arena, param_list_token.text.chars);

            auto  define_type = newExpression(arena, EC_ArrowType, builtin_Proc);
            auto *define_exp  = newExpression(arena, EC_Procedure, define_type);
            define_slot.slot->value = define_exp;
            auto proc  = &define_exp->Procedure;
            proc->name = define_name.text;

            auto signature = &define_type->ArrowType;
            signature->scope = scope;

            Tokenizer tk_save = *tk;
            s32 expected_arg_count = getCommaSeparatedListLength(tk);
            *tk = tk_save;
            signature->param_count = expected_arg_count;
            allocateArray(arena, expected_arg_count, signature->params);

            Bindings *local_bindings = extendBindings(arena, global_bindings);
            s32 parsed_param_count = 0;
            s32 typeless_run = 0;
            Token typeless_token;
            for (b32 stop = false;
                 !stop && parsing(tk);
                 )
            {// parsing parameters
                Token param_name_token = nextToken(tk);
                if (equals(&param_name_token, ')'))
                    stop = true;

                else if (isIdentifier(&param_name_token))
                {
                    s32 param_id = parsed_param_count++;
                    auto param_lookup = lookupNameCurrentFrame(local_bindings, param_name_token.text, true);
                    auto param = newExpression(arena, EC_Variable, 0);
                    signature->params[param_id] = param;
                    param_lookup.slot->value = param;

                    initVariable(&param->Variable, param_name_token.text, param_id, scope);

                    if (param_lookup.found)
                        tokenError("duplicate parameter name");
                    else if (optionalChar(tk, ':'))
                    {
                        Expression *param_type = parseExpression(arena, local_bindings);
                        param->type            = param_type;
                        if (typeless_run)
                        {
                            for (s32 offset = 1; offset <= typeless_run; offset++)
                                signature->params[param_id - offset]->type = param_type;
                            typeless_run = 0;
                        }

                        Token delimiter = nextToken(tk);
                        if (equals(&delimiter, ')'))
                            stop = true;
                        else if (!equals(&delimiter, ','))
                            tokenError("unexpected token after parameter type");
                    }
                    else if (requireChar(',', "delimit after typeless parameter name"))
                    {
                        typeless_run++;
                        typeless_token = param_name_token;
                    }
                    else
                        stop = true;
                }
                else
                    tokenError("expected parameter name");
            }
            if (parsing(tk))
            {
                assert(parsed_param_count == expected_arg_count);
                if (typeless_run)
                {
                    parseError(&typeless_token, "please provide types for all parameters");
                    // TODO: print out "typeless_token"
                }
            }

            // return type
            if (requireChar(tk, ':', "delimit arg list and return type"))
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
                        stack.scope = scope;
                        stack.count = parsed_param_count;
                        allocateArrayZero(temp_arena, parsed_param_count, stack.args);
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

        Stack empty_stack = {};
        empty_stack.arena = temp_arena;
        empty_stack.scope = newScope(temp_arena, "empty_scope");
        
        Token token = nextToken(); 
        if (equals(&token, '\0'))
        {}
        else if (equals(&token, '#'))
        {// compile directive
            token = nextToken();
            switch (MetaDirective directive = matchMetaDirective(&token))
            {
                case MetaDirective_Load:
                {
                    pushContextName("#load");
                    auto file = nextToken();
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
            Keyword keyword = matchKeyword(&token);
            if (keyword)
            {
                switch (keyword)
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
                        auto exp = parseExpression(arena, global_bindings);

                        if (parsing())
                        {
                            auto buffer = subArena(arena, 256);
                            {
                                if (keyword == Keyword_Print)
                                {
                                    Expression *reduced = normalize(arena, &empty_stack, 0, exp);
                                    printExpression(&buffer, reduced, true);
                                }
                                else
                                    printExpression(&buffer, exp, true);
                            }
                            printf("%s\n", buffer.base);
                        }
                        requireChar(';');
                    } break;

                    case Keyword_Check:
                    {
                        pushContextName("typecheck");
                        auto exp = parseExpression(temp_arena, global_bindings);
                        if (requireChar(':', "delimit expression and type"))
                        {
                            Expression *expected_type = parseExpression(temp_arena, global_bindings);
                            if (parsing())
                            {
                                auto expected_norm = normalize(temp_arena, &empty_stack, 0, expected_type);
                                auto actual_norm = normalize(temp_arena, &empty_stack, 0, exp->type);
                                if (!expressionsIdenticalB32(expected_norm, actual_norm))
                                {
                                    tokenError(&token, "typecheck failed");
                                    pushAttachment("expected type", expected_norm);
                                    pushAttachment("actual type", actual_norm);
                                }
                            }
                        }
                        requireChar(';');
                        popContext();
                    } break;
                }
            }
            else if (isIdentifier(&token))
            {
                pushContextName("global constant definition");
                Token *constant = &token;
                requireChar(':', "syntax: CONSTANT := VALUE;");
                requireChar('=', "syntax: CONSTANT := VALUE;");
                Expression *value = parseExpression(arena, global_bindings);
                Expression *norm = normalize(arena, &empty_stack, 0, value);
                if (parsing())
                {
                    if (!addGlobalName(constant->text, norm))
                        tokenError(constant, "redefinition of global name");
                }
                requireChar(';');
                popContext();
            }
            else
                tokenError("unexpected token to begin top-level form");
        }
        endTemporaryMemory(top_level_temp);
    }

    popContext();
}

internal void
initializeEngine(MemoryArena *arena)
{
    global_temp_arena_ = subArena(arena, megaBytes(2));
    global_temp_arena  = &global_temp_arena_;
    allocate(arena, global_bindings);
    global_bindings->arena = arena;

    addGlobalName("identical", builtin_identical);
    addGlobalName("Set"      , builtin_Set);
    addGlobalName("Prop"     , builtin_Prop);
    addGlobalName("Proc"     , builtin_Proc);
    addGlobalName("="        , builtin_identical_macro);

    const char *true_members[] = {"truth"};
    addBuiltinForm(arena, "True", true_members, 1, builtin_Prop);
    builtin_True = lookupNameCurrentFrame(global_bindings, toString("True"), false).slot->value;
    builtin_truth = lookupNameCurrentFrame(global_bindings, toString("truth"), false).slot->value;

    addBuiltinForm(arena, "False", (const char **)0, 0, builtin_Prop);
    builtin_False = lookupNameCurrentFrame(global_bindings, toString("False"), false).slot->value;
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

    allocate(init_arena, builtin_identical);
    allocate(init_arena, builtin_identical_macro);
    allocate(init_arena, builtin_True);
    allocate(init_arena, builtin_truth);
    allocate(init_arena, builtin_False);
    allocate(init_arena, builtin_Set);
    allocate(init_arena, builtin_Prop);
    allocate(init_arena, builtin_Proc);
    allocate(init_arena, builtin_Type);
    allocate(init_arena, hole_expression);

    builtin_identical->cat       = EC_Builtin_identical;
    builtin_identical_macro->cat = EC_Macro;

    builtin_Set->cat  = EC_Builtin_Set;
    builtin_Prop->cat = EC_Builtin_Prop;
    builtin_Proc->cat = EC_Builtin_Proc;
    builtin_Type->cat = EC_Builtin_Type;

    builtin_Set->type  = builtin_Type;
    builtin_Prop->type = builtin_Type;
    builtin_Proc->type = builtin_Type;

    hole_expression->cat = EC_Hole;

    {
        // Here we give 'identical' a type (A: Set, a:A, b:A) -> Prop
        // TODO: so we can't prove equality between props.
        builtin_identical->type = newExpression(init_arena, EC_ArrowType, 0);
        auto signature = castExpression(ArrowType, builtin_identical->type);
        signature->param_count = 3;
        signature->return_type = builtin_Prop;
        signature->scope       = newScope(init_arena, "bultin-identical scope");

        allocateArray(init_arena, 3, signature->params);
        auto args = signature->params;

        args[0] = newExpression(init_arena, EC_Variable, builtin_Set);
        initVariable(&args[0]->Variable, toString("A"), 0, signature->scope);

        args[1] = newExpression(init_arena, EC_Variable, args[0]);
        initVariable(&args[1]->Variable, toString("a"), 1, signature->scope);

        args[2] = newExpression(init_arena, EC_Variable, args[0]);
        initVariable(&args[2]->Variable, toString("b"), 2, signature->scope);
    }

    auto interp_arena_ = subArena(init_arena, getArenaFree(init_arena));
    auto interp_arena = &interp_arena_;

#if 0
    if (!beginInterpreterSession(interp_arena, "../data/operator.rea"))
        success = false;
    resetZeroArena(interp_arena);
#endif

#if 0
    if (!beginInterpreterSession(interp_arena, "../data/proof.rea"))
        success = false;
    resetZeroArena(interp_arena);
#endif

#if 1
    if (!beginInterpreterSession(interp_arena, "../data/test.rea"))
        success = false;
    resetZeroArena(interp_arena);
#endif

    return success;
}

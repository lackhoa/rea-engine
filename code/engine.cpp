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

struct Atom
{
    s32 stack_depth;
    u32 id;
};

enum ExpCat
{
    ExpCat_Atom,                // reference to something on "the stack"
    ExpCat_Apply,               // operator application
    ExpCat_Switch,              // switch statement
    ExpCat_Type,                // type information
    ExpCat_Procedure,           // holds actual computation (ie body that can be executed)
    ExpCat_ConstructorRef,      // reference to a constructor of a type
};

struct Expression;

struct ExpApply
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

// kind of like an operator, but we don't allow arbitrary expressions in here
// (maybe we need to).
struct Constructor
{
    Atom  op;
    u32   arg_count;
    Type *arg_types;
};

// NOTE: we need the id to arrange the switch body.
struct ConstructorRef
{
    Type *type;
    u32   id;
};

struct Procedure
{
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
    // todo: this should be a pointer.
    union
    {
        Atom            atom;
        ExpApply        apply;
        Switch          switch0;
        Type            type;
        Procedure       procedure;
        ConstructorRef  constructor_ref;
    };
};

#if 0
enum AtomCat
{
    AtomCat_Unknown,
    AtomCat_Type,
    AtomCat_Operator,
    AtomCat_Constructor,
};
#endif

#include "generated/Vector_Atom.h"

typedef u32 AtomId;
struct AtomSlot
{
    String    key;
    AtomId    value;  // note: the stack depth is implicit
    AtomSlot *next;
};

struct Bindings
{
    u32          stack_depth;
    MemoryArena *arena;
    AtomSlot     first[128];
    Bindings    *next;
};

struct Environment
{
    u32          stack_depth;
    MemoryArena *arena;
    u32          cap;  // todo: remove cap
    u32          count;
    Expression  *first;
    Environment *next;  // maybe we could have Environment** here.
};

inline Bindings *
extendBindings(MemoryArena *arena, Bindings *outer)
{
    Bindings *out = pushStruct(arena, Bindings);
    for (int i = 0; i < arrayCount(out->first); i++)
    {// invalidate these slots
        AtomSlot *slot = &out->first[i];
        slot->key.length = 0;
    }
    out->stack_depth = outer->stack_depth+1;
    out->next        = outer;
    out->arena       = arena;
    return out;
}

enum TokenCat
{
    // 0-255 reserved for single-char ASCII types.
    TokenCat_Special         = 256,
    TokenCat_PairingOpen     = 257,
    TokenCat_PairingClose    = 258,
    TokenCat_Alphanumeric    = 259,

    // TODO: Do I really need these? The tokenizer doesn't really produce this
    // information during its tokenization process.
    TokenCat_KeywordsBegin_  = 300,
    TokenCat_KeywordTypedef  = 301,
    TokenCat_KeywordDefine   = 302,
    TokenCat_KeywordSwitch   = 303,
    TokenCat_KeywordPrint    = 304,
    TokenCat_KeywordsEnd_    = 400,
};

const char *keywords[] = {"_ignore_", "typedef", "define", "switch", "print"};

struct Token
{
    String text;
    TokenCat cat;
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
newToken(char *first_char, TokenCat category)
{
    Token out;
    out.text = {first_char, 0};
    out.cat = category;
    return out;
}

internal TokenCat
getCharacterType(char c)
{
    if ((('a' <= c) && (c <= 'z'))
        || (('A' <= c) && (c <= 'Z'))
        || (('0' <= c) && (c <= '9')))
    {
        return TokenCat_Alphanumeric;
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
            case '|':
            case '*':
            case '-':
            case '+':
            case '=':
            {
                return TokenCat_Special;
            } break;

            case '(':
            case '{':
            {
                return TokenCat_PairingOpen;
            } break;

            case ')':
            case '}':
            {
                return TokenCat_PairingClose;
            }
        
            default:
                // NOTE: Self-describing category
                return (TokenCat)c;
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

inline TokenCat
matchKeyword(Token *token)
{
    TokenCat out = (TokenCat)0;
    for (int i = 1;
         i < arrayCount(keywords);
         i++)
    {
        if (equals(token, keywords[i]))
        {
            out = (TokenCat)(TokenCat_KeywordsBegin_ + i);
            break;
        }
    }
    return out;
}

inline b32
isKeyword(Token *token)
{
    return ((token->cat > TokenCat_KeywordsBegin_)
            && (token->cat < TokenCat_KeywordsEnd_));
}

inline Token
advance(Tokenizer *tk)
{
    Token out = {};
    eatAllSpaces(tk);
    out.text.chars = tk->at;
    b32 stop = false;

    TokenCat type = getCharacterType(*tk->at++);
    out.cat = type;
    switch (type)
    {
        case TokenCat_Alphanumeric:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        case TokenCat_Special:
        {
            while (getCharacterType(*tk->at) == type)
                tk->at++;
        } break;

        default: {}
    }

    out.text.length = tk->at - out.text.chars;
    if (out.cat == TokenCat_Alphanumeric)
    {
        if (TokenCat new_type = matchKeyword(&out))
            out.cat = new_type;
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

struct EngineState
{
    MemoryArena scoped_arena;   // used for storing e.g stack frames

    Bindings    global_bindings;
    Environment global_env;
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

struct NameLookup { AtomSlot* slot; b32 found; };

internal NameLookup
lookupNameCurrentFrame(Bindings *bindings, String key, b32 add_if_missing = false)
{
    AtomSlot *slot = 0;
    b32 found = false;
    u32 hash = stringHash(key);
    slot = (bindings->first + (hash % arrayCount(bindings->first)));
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
                    slot->value = 0;
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

    NameLookup out = { slot, found };
    return out;
}

inline NameLookup
lookupNameCurrentFrame(Bindings *bindings, Token *key, b32 add_if_missing = false)
{
    return lookupNameCurrentFrame(bindings, key->text, add_if_missing);
}

struct LookupNameRecursive {Atom value; b32 found;};

inline LookupNameRecursive
lookupNameRecursive(Bindings *bindings, Token *key)
{
    Atom atom = {};
    atom.stack_depth = bindings->stack_depth;
    b32 found = false;

    for (b32 stop = false;
         !stop;
         )
    {
        assert(atom.stack_depth >= 0);
        NameLookup lookup = lookupNameCurrentFrame(bindings, key, false);
        if (lookup.found)
        {
            found = true;
            atom.id = lookup.slot->value;
            stop = true;
        }
        else
        {
            if (bindings->next)
            {
                bindings = bindings->next;
                atom.stack_depth--;
            }
            else
                stop = true;
        }
    }

    LookupNameRecursive out = { atom, found };
    return out;
}

inline b32
atomValid(Atom atom)
{
    return ((atom.stack_depth != 0) && (atom.id != 0));
}

// TODO: we don't handle yet composite cases yet (such as +1(Nat))
internal void
parseConstructorDef(EngineState *state, Tokenizer *tk, Type *type, s32 ctor_id, Constructor *out)
{
    Token ctor = advance(tk);
    switch (ctor.cat)
    {
        case TokenCat_Special:
        case TokenCat_Alphanumeric:
        {
            NameLookup ctor_lookup = lookupNameCurrentFrame(&state->global_bindings, &ctor, true);
            if (ctor_lookup.found)
                todoErrorReport;
            else
            {
                u32 atom_id = state->global_env.count++;
                out->op.stack_depth = 0;
                out->op.id          = atom_id;
                out->arg_count      = 0;
                out->arg_types      = 0;

                ctor_lookup.slot->value = out->op.id;

                Expression *exp           = state->global_env.first + atom_id;
                exp->cat                  = ExpCat_ConstructorRef;
                exp->constructor_ref.type = type;
                exp->constructor_ref.id   = ctor_id;
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
        NameLookup type_lookup = lookupNameCurrentFrame(&state->global_bindings, &type_name, true);
        if (type_lookup.found)
            todoErrorReport;
        else
        {
            assert(state->global_env.count < state->global_env.cap);
            s32         type_atom_id = state->global_env.count++;
            type_lookup.slot->value  = type_atom_id;
            Expression *type_exp     = state->global_env.first + type_atom_id;
            type_exp->cat            = ExpCat_Type;
            Type       *type         = &type_exp->type;

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
                    parseConstructorDef(state, tk, type, constructor_id, type->ctors + constructor_id);
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

struct OptionalU32 { b32 success; u32 value; };

inline b32
equals(Atom atom1, Atom atom2)
{
    return ((atom1.id == atom2.id)
            && (atom1.stack_depth == atom2.stack_depth));
}

internal Expression *
dereferenceAtom(Environment *env, Atom atom)
{
    u32 traverse_count = env->stack_depth - atom.stack_depth;
    for (u32 i = 0; i < traverse_count; i++)
        env = env->next;
    Expression *out = env->first + atom.id;
    return out;
}

internal OptionalU32
matchSwitchCase(EngineState *state, Environment *env, Type *subject_type, Expression *matched_)
{
    OptionalU32 out = {};

    if (matched_->cat == ExpCat_Atom)
    {
        auto atom = matched_->atom;
        Expression *resolved = dereferenceAtom(env, atom);
        assert(resolved->cat != ExpCat_Atom);
        out = matchSwitchCase(state, env, subject_type, resolved);
    }
    else if (matched_->cat == ExpCat_ConstructorRef)
    {
        auto ctor   = matched_->constructor_ref;
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
            case ExpCat_Atom:
            {
                invalidCodePath;  // this should already have the type
            } break;

            case ExpCat_Apply:
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

internal void
parseExp(EngineState *state, MemoryArena *arena, Bindings *bindings, Environment *env, Tokenizer *tk, Expression *out)
{
    assert(env);

    Token first = advance(tk);
    if (isKeyword(&first))
    {
        switch (first.cat)
        {
            case TokenCat_KeywordSwitch:
            {
                out->cat = ExpCat_Switch;
                allocate(arena, out->switch0.subject);
                parseExp(state, arena, bindings, env, tk, out->switch0.subject);
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
                            parseExp(state, arena, bindings, env, tk, &switch_case);
                            requireChar(tk, '{');
                            auto case_match = matchSwitchCase(state, env, subject_type, &switch_case);
                            if (case_match.success)
                            {
                                parseExp(state, arena, bindings, env, tk, out->switch0.case_bodies + case_match.value);
                                requireChar(tk, '}');
                                // todo: type-check the body
                            }
                            else
                                todoErrorReport;
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
                todoErrorReport;  // keyword not part of expression
        }
    }
    else if ((first.cat == TokenCat_Alphanumeric)
             || (first.cat == TokenCat_Special))
    {
        LookupNameRecursive identifier_lookup = lookupNameRecursive(bindings, &first);
        if (identifier_lookup.found)
        {
            out->cat          = ExpCat_Atom;
            out->atom         = identifier_lookup.value;
            Expression *deref = dereferenceAtom(env, out->atom);
            out->type_of_this = deref->type_of_this;
        }
        else
            todoErrorReport;  // Unbound identifier
    }
    else
        todoErrorReport;  // unexpected start of expression
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
            assert(type_lookup.value.stack_depth == 0);
            auto type_expression = state->global_env.first + type_lookup.value.id;
            if (type_expression->cat == ExpCat_Type)
                out = &type_expression->type;
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

internal Environment
extendEnvironment(Environment *outer, u32 arg_count, Expression *reduced_args)
{    
    Environment out = {};

    out.stack_depth = outer->stack_depth+1;
    out.arena       = outer->arena;
    out.cap         = arg_count;
    out.first       = reduced_args;
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
        auto define_slot = lookupNameCurrentFrame(&state->global_bindings, define_name.text, true);
        if (define_slot.found)
            todoErrorReport;
        else
        {
            u32         define_atom_id    = state->global_env.count++;
            define_slot.slot->value       = define_atom_id;
            Expression *define_expression = state->global_env.first + define_atom_id;
            define_expression->cat        = ExpCat_Procedure;
            auto        procedure         = &define_expression->procedure;

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
            Bindings *bindings = extendBindings(&scoped_arena, &state->global_bindings);
            for (s32 arg_id = 0, stop = 0; !stop; arg_id++)
            {// parsing arguments
                Token arg_name_or_end = advance(tk);
                if (equals(&arg_name_or_end, ')'))
                    stop = true;

                else if (arg_name_or_end.cat == TokenCat_Alphanumeric)
                {
                    auto arg_name_lookup = lookupNameCurrentFrame(bindings, &arg_name_or_end, true);
                    if (arg_name_lookup.found)
                        todoErrorReport;  // Duplicate arg name
                    else
                    {
                        arg_name_lookup.slot->value = arg_id;

                        requireChar(tk, ':');

                        procedure->arg_types[arg_id] = parseType(state, bindings, tk);

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
            // TODO: not liking this extension maneuver.
            Expression *expressions_for_types = pushArray(arena, arg_count, Expression);
            for (int arg_id = 0; arg_id < arg_count; arg_id++)
            {
                expressions_for_types[arg_id].type_of_this = procedure->arg_types[arg_id];
            }
            Environment new_env = extendEnvironment(&state->global_env, arg_count, expressions_for_types);

            // return type
            requireChar(tk, ':');
            procedure->return_type = parseType(state, bindings, tk);

            requireChar(tk, '{');
            allocate(arena, procedure->body);
            parseExp(state, arena, bindings, &new_env, tk, procedure->body);
            requireChar(tk, '}');

            endTemporaryArena(&state->scoped_arena, &scoped_arena);
        }
    }
    else
        todoErrorReport;
}

internal void
reduce(EngineState *state, MemoryArena *arena, Environment *env, Expression *in, Expression *out)
{
    out->cat = in->cat;  // assume that we can't reduce this.
    out->type_of_this = in->type_of_this;

    switch (in->cat)
    {
        case ExpCat_Atom:
        {
            *out = *dereferenceAtom(env, in->atom);
        } break;

        case ExpCat_Apply:
        {
            auto apply = &in->apply;
            Expression *reduced_args = pushArray(arena, apply->arg_count, Expression);
            for (auto arg_id = 0;
                 arg_id < apply->arg_count;
                 arg_id++)
            {
                auto in_arg      = apply->args + arg_id;
                auto reduced_arg = reduced_args + arg_id;
                reduce(state, arena, env, in_arg, reduced_arg);
            }

            Expression *reduced_op = pushStruct(arena, Expression);
            reduce(state, arena, env, apply->op, reduced_op);

            if (reduced_op->cat == ExpCat_Procedure)
            {
                Environment new_env = extendEnvironment(env, apply->arg_count, reduced_args);
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
            reduce(state, arena, env, switch0->subject, reduced_subject);
            Type *subject_type = reduced_subject->type_of_this;
            auto ctor_id = matchSwitchCase(state, env, subject_type, reduced_subject);
            if (ctor_id.success)
                reduce(state, arena, env, switch0->case_bodies + ctor_id.value, out);
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
        case ExpCat_Atom:
        {
            printf("atom(%d, %d)\n", out->atom.stack_depth, out->atom.id);
        } break;

        case ExpCat_Apply:
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
            printf("ctor which is atom (%d, %d)\n", ctor->op.stack_depth, out->constructor_ref.id);
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
                    exp->cat = ExpCat_Apply;
                    exp->apply.arg_count = 2;
                    allocate(arena, exp->apply.op);
                    allocateArray(arena, 2, exp->apply.args);

                    // Hacking the expression since we can't parse operators yet.
                    Expression *op   = exp->apply.op;
                    Expression *arg1 = exp->apply.args;
                    Expression *arg2 = exp->apply.args + 1;
                    parseExp(state, arena, &state->global_bindings, &state->global_env, tk, arg1);
                    parseExp(state, arena, &state->global_bindings, &state->global_env, tk, op);
                    parseExp(state, arena, &state->global_bindings, &state->global_env, tk, arg2);

                    requireChar(tk, ')');

                    Expression *out = pushStruct(arena, Expression);
                    reduce(state, arena, &state->global_env, exp, out);
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

        state->global_env.arena = arena;
        state->global_env.cap   = 1024;
        allocateArray(arena, state->global_env.cap, state->global_env.first);
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

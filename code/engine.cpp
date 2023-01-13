/*
  General Todos: 
  - #cleanup Replace all token <-> string comparison with keyword checks.
  - #tool something that cleans up when it goes out of scope
  - Try to remove recursion, we pass a bunch of things in the signature and it's annoying to change.
  - #speed evaluating functions by substituting the body is really bad in case of "let"
  - make "computation" be a builtin
  - debug serial situation
  - clean up the data tree containing constructors
  - we're printing terms every time we encounter an error, but the error might be recoverable so it's just wasted work. Either pass the intention down, or abandon the recoveriy route.
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"
#include "tokenization.cpp"
#include "debug_config.h"

global_variable Builtins builtins;
global_variable Term dummy_function_being_built;
global_variable Term  holev_ = {.cat = Term_Hole};
global_variable Term *holev = &holev_;

global_variable EngineState global_state;

#define DEBUG_ON  {DEBUG_MODE = true; setvbuf(stdout, NULL, _IONBF, 0);}
#define DEBUG_OFF {DEBUG_MODE = false; setvbuf(stdout, NULL, _IONBF, BUFSIZ);}

inline void attach(char *key, String value, Tokenizer *tk=global_tokenizer)
{
  ParseError *error = tk->error;
  assert(error->attachment_count < arrayCount(error->attachments));
  error->attachments[error->attachment_count++] = {key, value};
}

inline void
attach(char *key, i32 count, Term **terms, PrintOptions print_options={})
{
  StartString start = startString(error_buffer);
  for (i32 id=0; id < count; id++)
  {
    print(error_buffer, "\n");
    print(error_buffer, terms[id], print_options);
  }
  attach(key, endString(start));
}

inline void attach(char *key, Token *token, Tokenizer *tk=global_tokenizer)
{
  attach(key, token->string, tk);
}

inline void attach(char *key, Ast *ast, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, ast);
  attach(key, endString(start), tk);
}

inline void
attach(char *key, Term *value, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, value);
  attach(key, endString(start), tk);
}

inline void attach(char *key, i32 n, Tokenizer *tk=global_tokenizer)
{
  StartString start = startString(error_buffer);
  print(error_buffer, "%d", n);
  attach(key, endString(start), tk);
}

inline Token *
lastToken()
{
  return &global_tokenizer->last_token;
}

inline String
globalNameOf(Term *term)
{
  if (term->global_name)
    return term->global_name->string;
  else
    return {};
}

inline Term *
newVariable(MemoryArena *arena, Typer *typer, String name, i32 delta, i32 id)
{
  Variable *out = newTerm(arena, Variable, 0);
  out->name  = name;
  out->delta = delta;
  out->id    = id;
  computeType(arena, typer, &out->t);
  return &out->t;
}

inline Term *
newComposite(MemoryArena *arena, Term *op, i32 arg_count, Term **args)
{
  // todo typecheck the arguments too maybe?
  Composite *out = newTerm(arena, Composite, 0);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;

  // todo cutnpaste
  if (Constructor *ctor = castTerm(op, Constructor))
  {
    assert(ctor->uni);
    out->type = &ctor->uni->t;  // todo this makes me nervous!
  }
  else
  {
    Arrow *op_type = castTerm(getType(op), Arrow);
    out->type = evaluate(arena, args, op_type->output_type);
  }

  return &out->t;
}

inline Term *
newComposite(MemoryArena *arena, Term *op, i32 arg_count, Term **args, Term *type)
{
  // todo typecheck the arguments too maybe?
  Composite *out = newTerm(arena, Composite, type);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;
  return &out->t;
}

inline Term *
newEquality(MemoryArena *arena, Term *type, Term *lhs, Term *rhs)
{
  assert(type);
  Composite *eq = newTerm(arena, Composite, &builtins.Set->t);
  allocateArray(arena, 3, eq->args);
  eq->op        = &builtins.equal->t;
  eq->arg_count = 3;
  eq->args[0]   = type;
  eq->args[1]   = lhs;
  eq->args[2]   = rhs;
  return &eq->t;
}

forward_declare inline Term *
newComputation(MemoryArena *arena, Typer *typer, Term *lhs, Term *rhs)
{
  Computation *out = newTerm(arena, Computation, 0);
  out->lhs = lhs;
  out->rhs = rhs;
  computeType(arena, typer, &out->t);

#if REA_DIAGNOSTICS
  assert(equal(normalize(temp_arena, typer, lhs), normalize(temp_arena, typer, rhs)));
#endif

  return &out->t;
}

inline b32
isEquality(Term *eq0)
{
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == &builtins.equal->t)
      return true;
  }
  return false;
}

inline TermPair
getEqualitySides(Term *eq0, b32 must_succeed=true)
{
  TermPair out = {};
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == &builtins.equal->t)
      out = TermPair{eq->args[1], eq->args[2]};
  }
  assert(!must_succeed || out)
  return out;
}

inline b32
isSequenced(Ast *ast)
{
  b32 out = false;
  switch (ast->cat)
  {
    case Ast_RewriteAst:
    case Ast_Let:
    case Ast_ForkAst:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

inline b32
isSequenced(Term *term)
{
  b32 out = false;
  switch (term->cat)
  {
    case Term_Rewrite:
    case Term_Fork:
    {out = true;} break;
    default: out = false;
  }
  return out;
}

// todo removeme don't need this anymore now that we put the type in the constructor
inline Arrow *
computeType(Constructor *ctor)
{
  if (ctor->type)
    return castTerm(ctor->type, Arrow);
  else
  {
    Arrow *signature = ctor->uni->structs[ctor->id];
    ctor->type = &signature->t;
    return signature;
  }
}

inline Constructor *
newConstructor(MemoryArena *arena, Union *uni, i32 id)
{
  Constructor *ctor = newTerm(arena, Constructor, 0);
  ctor->uni = uni;
  ctor->id  = id;
  computeType(ctor);
  return ctor;
}

inline Term **
synthesizeMembers(MemoryArena *arena, Term *parent, i32 ctor_id)
{
  Union *uni = castTerm(parent->type, Union);
  Arrow *struc = uni->structs[ctor_id];
  i32 param_count = struc->param_count;
  Term **args = pushArray(temp_arena, param_count, Term *);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = struc->param_names[field_id];
    Term *type = evaluate(arena, args, struc->param_types[field_id]);
    Accessor *accessor = newTerm(arena, Accessor, type);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    args[field_id] = &accessor->t;
  }
  return args;
}

inline Term *
synthesizeTree(MemoryArena *arena, Term *parent, DataTree *tree)
{
  Composite *record = 0;
  Union *uni   = castTerm(parent->type, Union);
  Arrow *struc = uni->structs[tree->ctor_id];
  Constructor *ctor = newConstructor(arena, tree->uni, tree->ctor_id);
  i32 param_count = struc->param_count;
  record = newTerm(arena, Composite, parent->type);
  record->op        = &ctor->t;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term *);
  Term **members = synthesizeMembers(arena, parent, tree->ctor_id);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    DataTree *member_tree = tree->members[field_id];
    if (member_tree)
      record->args[field_id] = synthesizeTree(arena, members[field_id], member_tree);
    else
      record->args[field_id] = members[field_id];
  }
  return &record->t;
}

inline String
getVarNameInScope(Typer *env, DataMap *map)
{
  String out = {};
  for (Scope *scope = env->scope; scope; scope=scope->outer)
  {
    if (scope->depth == map->depth)
    {
      out = scope->first->param_names[map->index];
      break;
    }
  }
  return out;
}

internal void
print(MemoryArena *buffer, DataTree *tree)
{
  if (tree)
  {
    print(buffer, tree->uni->ctor_names[tree->ctor_id]);
    if (tree->member_count)
    {
      print(buffer, "(");
      for (i32 id=0; id < tree->member_count; id++)
      {
        print(buffer, tree->members[id]);
        if (id != tree->member_count-1)
          print(buffer, ", ");
      }
      print(buffer, ")");
    }
  }
  else
    print(buffer, "?");
}

internal void
printDataMap(MemoryArena *buffer, Typer *env)
{
  for (DataMap *map = env->map; map; map=map->next)
  {
    String var = getVarNameInScope(env, map);
    print(buffer, var);
    print(buffer, ": ");
    print(buffer, &map->tree);
    if (map->next)
      print(buffer, ", ");
  }
}

inline Composite *
castRecord(Term *term)
{
  Composite *out = 0;
  if (Composite *composite = castTerm(term, Composite))
    if (Constructor *ctor = castTerm(composite->op, Constructor))
      out = composite;
  return out;
}

internal Term *
rewriteTerm(MemoryArena *arena, Term *rhs, TreePath *path, Term *in0)
{
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyStruct(arena, in);
    if (path->first == -1)
    {
      out->op = rewriteTerm(arena, rhs, path->next, in->op);
    }
    else
    {
      assert(path->first >= 0 && path->first < out->arg_count);
      allocateArray(arena, out->arg_count, out->args);
      for (i32 arg_id=0; arg_id < out->arg_count; arg_id++)
      {
        if (arg_id == (i32)path->first)
        {
          out->args[arg_id] = rewriteTerm(arena, rhs, path->next, in->args[arg_id]);
        }
        else
          out->args[arg_id] = in->args[arg_id];
      }
    }
    return &out->t;
  }
  else
  {
#if 0
    if (!equalB32(in0, lhs))
    {
      dump("actual:   "); dump(in0); dump();
      dump("expected: "); dump(lhs); dump();
      invalidCodePath;
    }
#endif
    return rhs;
  }
}

inline void
initDataTree(MemoryArena *arena, DataTree *tree, Union *uni, i32 ctor_id)
{
  i32 ctor_arg_count = uni->structs[ctor_id]->param_count;
  tree->uni          = uni;
  tree->ctor_id      = ctor_id;
  tree->member_count = ctor_arg_count;
  tree->members      = pushArray(arena, ctor_arg_count, DataTree*, true);
}

inline i32 getScopeDepth(Scope *scope) {return scope ? scope->depth : 0;}
inline i32 getScopeDepth(Typer *env)   {return (env && env->scope) ? env->scope->depth : 0;}

internal AddDataTree
getOrAddDataTree(MemoryArena *arena, Typer *env, Term *in0, i32 ctor_id)
{
  DataTree *tree = 0;
  b32 added = false;
  i32 scope_depth = getScopeDepth(env);

  Variable *in_root = 0;
  i32    path_length = 0;
  Union *reverse_unions[32];
  u8     reverse_path[32];
  Term *iter0 = in0;
  b32 stop = false;
  Union *root_union = 0;
  for (;!stop;)
  {
    Union *uni = castTerm(getType(iter0), Union);
    switch (iter0->cat)
    {
      case Term_Variable:
      {
        in_root = castTerm(iter0, Variable);
        root_union = uni;
        stop = true;
      } break;

      case Term_Accessor:
      {
        Accessor *iter = castTerm(iter0, Accessor);
        i32 path_id = path_length++;
        assert(path_length < arrayCount(reverse_path));
        reverse_unions[path_id] = uni;
        reverse_path[path_id]   = iter->field_id;
        iter0 = iter->record;
      } break;

      default:
      {
        stop = true;
      } break;
    }
  }

  i32 in_root_depth = scope_depth - in_root->delta;
  for (DataMap *map = env->map; map; map=map->next)
  {
    if (map->depth == in_root_depth && map->index == in_root->id)
    {
      tree = &map->tree;
      break;
    }
  }
  if (!tree)
  {
    if (path_length == 0)
    {
      if (ctor_id != -1)
      {
        DataMap *map = pushStruct(arena, DataMap, true);
        map->depth   = in_root_depth;
        map->index   = in_root->id;
        initDataTree(arena, &map->tree, root_union, ctor_id);
        tree = &map->tree;
        map->next    = env->map;
        env->map     = map;

        DataMapAddHistory *history = pushStruct(temp_arena, DataMapAddHistory, true);
        history->previous_map = map->next;
        history->previous     = env->add_history;
        env->add_history = history;
        added = true;
      }
    }
    else 
    {
      assert(root_union->ctor_count == 1);
      DataMap *map = pushStruct(arena, DataMap, true);
      map->depth   = in_root_depth;
      map->index   = in_root->id;
      initDataTree(arena, &map->tree, root_union, 0);
      tree = &map->tree;
      map->next = env->map;
      env->map = map;
    }
  }

  for (i32 path_index=0; path_index < path_length; path_index++)
  {
    i32 reverse_index = path_length-1-path_index;
    i32    field_index = reverse_path[reverse_index];
    Union *uni         = reverse_unions[reverse_index];
    DataTree *parent = tree;
    tree = tree->members[field_index];
    if (!tree)
    {
      if (path_index == path_length-1)
      {
        if (ctor_id != -1)
        {
          DataTree *new_tree = pushStruct(arena, DataTree, true);
          initDataTree(arena, new_tree, uni, ctor_id);
          parent->members[field_index] = new_tree;
          tree = new_tree;

          DataMapAddHistory *history = pushStruct(temp_arena, DataMapAddHistory, true);
          history->parent      = parent;
          history->field_index = field_index;
          history->previous = env->add_history;
          env->add_history = history;
          added = true;
        }
      }
      else
      {
        assert(uni->ctor_count == 1);
        DataTree *new_tree = pushStruct(arena, DataTree, true);
        initDataTree(arena, new_tree, uni, 0);
        parent->members[field_index] = new_tree;
        tree = new_tree;
      }
    }
  }
  
  return AddDataTree{.tree=tree, .added=added};
}

internal DataTree *
getDataTree(Typer *env, Term *in0)
{
  return getOrAddDataTree(0, env, in0, -1).tree;
}

inline void
undoDataMap(Typer *env)
{
  DataMapAddHistory *history = env->add_history;
  if (history->parent)
    history->parent->members[history->field_index] = 0;
  else
    env->map = history->previous_map;

  env->add_history = history->previous;
}

internal Constructor
getConstructor(Typer *env, Term *in0)
{
  // todo cleanup
  Constructor out = {};
  b32 is_record = false;
  if (Composite *in = castTerm(in0, Composite))
  {
    if (Constructor *ctor = castTerm(in->op, Constructor))
    {
      is_record = true;
      out = *ctor;
    }
  }
  if (!is_record)
  {
    if (Union *uni = castTerm(todoGetType(temp_arena, env, in0), Union))
    {
      if (uni->ctor_count == 1)
        out = *newConstructor(temp_arena, uni, 0);
      else
      {
        if (DataTree *tree = getDataTree(env, in0))
          out = *newConstructor(temp_arena, tree->uni, tree->ctor_id);
      }
    }
  }
  return out;
}

forward_declare inline Term *
computeType(MemoryArena *arena, Typer *env, Term *in0)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  Term *out0 = 0;
  if (in0->type)
    out0 = in0->type;
  else
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        Scope *scope = env->scope;
        for (i32 id=0; id < in->delta; id++)
          scope=scope->outer;
        
        assert(scope->depth == env->scope->depth - in->delta);
        out0 = scope->first->param_types[in->id];
        out0 = rebase(arena, out0, in->delta);

        assert(out0);
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        if (Constructor *ctor = castTerm(in->op, Constructor))
        {
          assert(ctor->uni);
          out0 = &ctor->uni->t;  // todo this makes me nervous!
        }
        else
        {
          Term *op_type0 = computeType(arena, env, in->op);
          Arrow *op_type = castTerm(op_type0, Arrow);
          out0 = evaluate(arena, in->args, op_type->output_type);
        }
      } break;

      case Term_Arrow:
      {
        out0 = &builtins.Type->t;
      } break;

      case Term_Function:
      {
        invalidCodePath;
      } break;

      case Term_Computation:
      {
        Computation *in = castTerm(in0, Computation);
        out0 = newEquality(arena, computeType(arena, env, in->lhs), in->lhs, in->rhs);
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Term  **args  = 0;
        if (Composite *record = castTerm(in->record, Composite))
        {
          if (Constructor *ctor = castTerm(record->op, Constructor))
          {
            args  = record->args;
          }
        }
        if (!args)
        {
          Constructor ctor = getConstructor(env, in->record);
          args = synthesizeMembers(arena, in->record, ctor.id);
        }

        out0 = args[in->field_id]->type;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        auto [lhs, rhs] = getEqualitySides(computeType(arena, env, in->eq_proof));
        Term *rewrite_to = in->right_to_left ? rhs : lhs;
        out0 = rewriteTerm(arena, rewrite_to, in->path, todoGetType(arena, env, in->body));
      } break;

      case Term_Constructor:
      {
        Constructor *ctor = castTerm(in0, Constructor);
        out0 = &computeType(ctor)->t;
      } break;

      default:
      {
        DUMP("The term is: ", in0);
        todoIncomplete;
      }
    }

    in0->type = out0;
  }
  assert(out0);
  return out0;
}

// todo this function is just a stub for direct type retrieval, until we can
// transition fully to all-terms-have-types kinda deal thing.
forward_declare inline Term *
todoGetType(MemoryArena *arena, Typer *env, Term *in0)
{
  return computeType(arena, env, in0);
}

forward_declare inline Arrow *
getType(Constructor *ctor)
{
  return castTerm(ctor->type, Arrow);
}

// NOTE: this is how I want to aim at for the type architecture: just one pointer deref.
forward_declare inline Term *
getType(Term *in0)
{
  return in0->type;
}

forward_declare inline Term *
getTypeGlobal(Term *in0)
{
  return in0->type;
}

inline void setType(Term *term, Term *type) {term->type = type;}

inline LocalBindings *
extendBindings(MemoryArena *arena, Typer *env)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->next     = env->bindings;
  out->arena    = arena;
  env->bindings = out;
  return out;
}

inline LocalBindings * extendBindings(Typer *env) {return extendBindings(temp_arena, env);}

forward_declare inline void
dump(Trinary trinary)
{
  if (trinary == Trinary_True) dump("True");
  else if (trinary == Trinary_False) dump("False");
  else dump("Unknown");
}

forward_declare inline void unwindScope(Typer *env) {env->scope = env->scope->outer;}

forward_declare inline void
unwindBindingsAndScope(Typer *env)
{
  env->bindings = env->bindings->next;
  unwindScope(env);
}

forward_declare inline void dump(Term *in0) {print(0, in0, {});}
forward_declare inline void dump(Ast *in0)  {print(0, in0, {});}

i32 global_variable DEBUG_INDENTATION;
forward_declare inline void DEBUG_INDENT()
{
  DEBUG_INDENTATION++;
  for (i32 id = 0; id < DEBUG_INDENTATION; id++)
    dump(" ");
}

forward_declare inline void DEBUG_DEDENT()
{
  for (i32 id = 0; id < DEBUG_INDENTATION; id++)
    dump(" ");
  DEBUG_INDENTATION--;
}

#define NULL_WHEN_ERROR(name) if (noError()) {assert(name);} else {name = {};}

inline b32
isHiddenParameter(ArrowAst *arrow, i32 param_id)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_id], ParameterFlag_Hidden);
  return false;
}

inline b32
isHiddenParameter(Arrow *arrow, i32 param_id)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_id], ParameterFlag_Hidden);
  return false;
}

inline i32
precedenceOf(String op)
{
  int out = 0;

  // TODO: implement for real
  if (equal(op, "->"))
    out = 40;
  else if (equal(op, "=") || equal(op, "!="))
    out = 50;
  else if (equal(op, "<") || equal(op, ">") || equal(op, "=?") || equal(op, "=="))
    out = 55;
  else if (equal(op, "+") || equal(op, "-"))
    out = 60;
  else if (equal(op, "|"))
    out = 65;
  else if (equal(op, "&")
           || equal(op, "*"))
    out = 70;
  else
    out = 100;

  return out;
}

inline char *
printComposite(MemoryArena *buffer, void *in0, b32 is_term, PrintOptions opt)
{
  char *out = buffer ? (char *)getNext(buffer) : 0;
  int    precedence = 0;        // todo: no idea what the default should be
  void  *op         = 0;
  i32    arg_count  = 0;
  void **raw_args   = 0;

  Ast  *ast   = (Ast *)in0;
  Term *value = (Term *)in0;
  Arrow *op_signature = 0;
  b32 op_is_constructor = false;
  if (is_term)
  {
    Composite *in = castTerm(value, Composite);
    op           = in->op;
    op_signature = 0;
    raw_args     = (void **)in->args;
    arg_count    = in->arg_count;

    if (in->op && in->op->cat != Term_Variable)
    {
      op_signature = castTerm((getTypeGlobal(in->op)), Arrow);
      assert(op_signature);
      if (Token *global_name = in->op->global_name)
        precedence = precedenceOf(global_name->string);
      if (in->op->cat == Term_Constructor)
        op_is_constructor = true;
    }
  }
  else
  {
    CompositeAst *in = castAst(ast, CompositeAst);
    op       = in->op;
    raw_args = (void **)in->args;
    arg_count = in->arg_count;

    precedence = precedenceOf(in->op->token.string);
  }

  void **printed_args;
  if (op_signature)
  {// print out explicit args only
    arg_count = 0;
    printed_args = pushArray(temp_arena, op_signature->param_count, void*);
    for (i32 param_id = 0; param_id < op_signature->param_count; param_id++)
    {
      b32 print_all_arguments = DEBUG_MODE && DEBUG_print_all_arguments;
      if (print_all_arguments || !isHiddenParameter(op_signature, param_id))
        printed_args[arg_count++] = raw_args[param_id];
    }
  }
  else
    printed_args = raw_args;

  if (arg_count == 2)
  {// special path for infix operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    arg_opt.no_paren_precedence = precedence+1;
    print(buffer, printed_args[0], is_term, arg_opt);

    print(buffer, " ");
    print(buffer, op, is_term, opt);
    print(buffer, " ");

    arg_opt.no_paren_precedence = precedence;
    print(buffer, printed_args[1], is_term, arg_opt);
    if (precedence < opt.no_paren_precedence)
      print(buffer, ")");
  }
  else
  {// normal prefix path
    print(buffer, op, is_term, opt);
    if (!(op_is_constructor && arg_count == 0))
    {
      print(buffer, "(");
      PrintOptions arg_opt        = opt;
      arg_opt.no_paren_precedence = 0;
      for (i32 arg_id = 0; arg_id < arg_count; arg_id++)
      {
        print(buffer, printed_args[arg_id], is_term, arg_opt);
        if (arg_id < arg_count-1)
          print(buffer, ", ");
      }
      print(buffer, ")");
    }
  }
  return out;
}

inline void
print(MemoryArena *buffer, TreePath *tree_path)
{
  print(buffer, "[");
  for (TreePath *path=tree_path; path; path=path->next)
  {
    print(buffer, "%d", path->first);
    if (path->next)
    {
      print(buffer, ", ");
    }
  }
  print(buffer, "]");
}

inline void
dump(TreePath *tree_path)
{
  print(0, tree_path);
}

inline void indent(MemoryArena *buffer, i32 indentation)
{
  for (int id=0; id < indentation; id++)
    print(buffer, " ");
}

inline void newlineAndIndent(MemoryArena *buffer, i32 indentation)
{
  print(buffer, "\n");
  indent(buffer, indentation);
}

forward_declare internal void
print(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{// printAst
  if (in0)
  {
    PrintOptions new_opt = opt;
    unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    new_opt.indentation += 1;

    switch (in0->cat)
    {
      case Ast_Hole:
      {print(buffer, "_");} break;

      case Ast_SyntheticAst:
      {
        SyntheticAst *in = castAst(in0, SyntheticAst);
        print(buffer, in->term);
      } break;

      case Ast_Identifier:
      {print(buffer, in0->token.string);} break;

      case Ast_RewriteAst:
      {
        RewriteAst *in = castAst(in0, RewriteAst);
        print(buffer, "rewrite");
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof, new_opt);
      } break;

      case Ast_CompositeAst:
      {
        printComposite(buffer, in0, false, new_opt);
      } break;

      case Ast_ForkAst:
      {
        ForkAst *in = castAst(in0, ForkAst);
        print(buffer, "fork ");
        print(buffer, in->subject, new_opt);
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, "{");
        i32 case_count = in->case_count;
        for (i32 ctor_id = 0;
             ctor_id < case_count;
             ctor_id++)
        {
          Token *ctor = in->ctors + ctor_id;
          print(buffer, ctor->string);
          print(buffer, ": ");
          print(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != case_count)
          {
            print(buffer, ", ");
            newlineAndIndent(buffer, opt.indentation+1);
          }
        }
        print(buffer, "}");
      } break;

      case Ast_ArrowAst:
      {
        ArrowAst *in = castAst(in0, ArrowAst);
        print(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          print(buffer, in->param_names[param_id]);
          print(buffer, ": ");
          print(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ") -> ");

        print(buffer, in->output_type, new_opt);
      } break;

      case Ast_AccessorAst:
      {
        AccessorAst *in = castAst(in0, AccessorAst);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name.string);
      } break;

      case Ast_FunctionDecl: {print(buffer, "function decl");} break;

      case Ast_Lambda: {print(buffer, "lambda");} break;

      case Ast_Let:
      {
        Let *in = castAst(in0, Let);
        print(buffer, in->lhs);
        if (in->type)
        {
          print(buffer, " : ");
          print(buffer, in->type, new_opt);
        }
        print(buffer, " := ");
        print(buffer, in->rhs, new_opt);
        print(buffer, "; ");
        print(buffer, in->body, new_opt);
      } break;

      case Ast_ComputationAst:
      {
        ComputationAst *computation = castAst(in0, ComputationAst);
        print(buffer, "computation: (");
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, ")");
      } break;

      case Ast_UnionAst:
      {
        print(buffer, "<some union>");
      } break;

      case Ast_CtorAst:
      {
        print(buffer, "<some ctor>");
      } break;

      case Ast_SeekAst:
      {
        print(buffer, "<some seek>");
      } break;
    }
  }
  else
    print(buffer, "<NULL>");
}

forward_declare internal void
print(MemoryArena *buffer, Ast *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal void
print(MemoryArena *buffer, Term *in0, PrintOptions opt)
{// mark: printTerm
  if (in0)
  {
    PrintOptions new_opt = opt;
    if (!checkFlag(opt.flags, PrintFlag_LockDetailed))
      unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    unsetFlag(&new_opt.flags, PrintFlag_PrintType);
    new_opt.indentation = opt.indentation + 1;
    b32 skip_print_type = false;

    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->name.chars)
          print(buffer, in->name);
        else
          print(buffer, "anon");

        if (!in->name.chars || DEBUG_MODE)
          print(buffer, "[%d:%d]", in->delta, in->id);
      } break;

      case Term_Hole:
      {print(buffer, "_");} break;

      case Term_Composite:
      {printComposite(buffer, in0, true, new_opt);} break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        if (in0->global_name)
        {
          print(buffer, in0->global_name->string);
        }
        if (!in->global_name || checkFlag(opt.flags, PrintFlag_Detailed))
        {
          if (in->ctor_count)
          {
            print(buffer, "union {");
            unsetFlag(&new_opt.flags, PrintFlag_Detailed);
            for (i32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
            {
              print(buffer, in->ctor_names[ctor_id]);
              print(buffer, ": ");
              print(buffer, &in->structs[ctor_id]->t, new_opt);
              if (ctor_id != in->ctor_count-1)
                print(buffer, ", ");
            }
            print(buffer, "}");
          }
        }
      } break;

      case Term_Function:
      {
        Function *in = castTerm(in0, Function);
        b32 is_anonymous = false;
        String name = globalNameOf(in0);
        if (name.chars)
          print(buffer, name);
        else
          is_anonymous = true;

        if (checkFlag(opt.flags, PrintFlag_Detailed) || is_anonymous)
        {
          skip_print_type = true;
          if (in->type) print(buffer, in->type, new_opt);

          newlineAndIndent(buffer, opt.indentation);
          print(buffer, "{");
          print(buffer, in->body, new_opt);
          print(buffer, "}");
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in = castTerm(in0, Arrow);
        print(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          String param_name = in->param_names[param_id];
          if (param_name.chars)
          {
            print(buffer, param_name);
            print(buffer, ": ");
          }
          print(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ")");
        if (in->output_type)
        {
          print(buffer, " -> ");
          print(buffer, in->output_type, new_opt);
        }
      } break;

      case Term_Builtin:
      {
        if (in0 == &builtins.equal->t)
          print(buffer, "=");
        else if (in0 == &builtins.Set->t)
          print(buffer, "Set");
        else if (in0 == &builtins.Type->t)
          print(buffer, "Type");
      } break;

      case Term_Constructor:
      {
        Constructor *in = castTerm(in0, Constructor);
        print(buffer, in->uni->ctor_names[in->id]);
      } break;

      case Term_Rewrite:
      {
        Rewrite *rewrite = castTerm(in0, Rewrite);
        // print(buffer, getTypeNoEnv(temp_arena, &rewrite->t), new_opt);
        skip_print_type = true;
        print(buffer, " <=>");
        newlineAndIndent(buffer, opt.indentation);
        // print(buffer, getTypeNoEnv(temp_arena, rewrite->body), new_opt);
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "rewrite");
        if (rewrite->right_to_left) print(buffer, "<-");
        print(buffer, rewrite->path);
        if (rewrite->eq_proof->cat != Term_Computation)
        {
          print(buffer, " justification: ");
          newlineAndIndent(buffer, new_opt.indentation);
          print(buffer, rewrite->eq_proof, new_opt);
        }
        newlineAndIndent(buffer, opt.indentation);

        print(buffer, "body: ");
        // print(buffer, getTypeNoEnv(temp_arena, rewrite->body), new_opt);
        newlineAndIndent(buffer, new_opt.indentation);
        print(buffer, rewrite->body, new_opt);
      } break;

      case Term_Computation:
      {
        print(buffer, "computation: (");
        Computation *computation = castTerm(in0, Computation);
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, ")");
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name);
      } break;

      case Term_Fork:
      {
        Fork *in = castTerm(in0, Fork);
        print(buffer, "fork ");
        print(buffer, in->subject, new_opt);
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, "{");
        Union *uni = in->uni;
        for (i32 ctor_id = 0;
             ctor_id < uni->ctor_count;
             ctor_id++)
        {
          print(buffer, uni->ctor_names[ctor_id]);
          print(buffer, ": ");
          print(buffer, in->bodies[ctor_id], new_opt);
          if (ctor_id != uni->ctor_count-1)
          {
            print(buffer, ", ");
            newlineAndIndent(buffer, opt.indentation+1);
          }
        }
        print(buffer, "}");
      } break;
    }

    if (checkFlag(opt.flags, PrintFlag_PrintType) && !skip_print_type)
    {
      print(buffer, ": ");
      print(buffer, getTypeGlobal(in0), new_opt);
    }
  }
  else
    print(buffer, "<NULL>");
}

inline void
print(MemoryArena *buffer, Scope *scopes)
{
  print(buffer, "[");
  while (scopes)
  {
    auto scope = scopes->first;
    print(buffer, "(");
    for (int param_id = 0;
         param_id < scope->param_count;
         param_id++)
    {
      print(buffer, scope->param_names[param_id]);
      print(buffer, ": ");
      print(buffer, scope->param_types[param_id], {});
      if (param_id < scope->param_count-1)
        print(buffer, ", ");
    }
    print(buffer, ")");

    scopes = scopes->outer;
    if (scopes)
      print(buffer, ",\n ");
  }
  print(buffer, "]");
}

inline void dump(Scope *stack) {print(0, stack);}
inline void dump(Typer *env) {dump("stack: "); dump(env->scope);}

forward_declare internal void
print(MemoryArena *buffer, Term *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal void
print(MemoryArena *buffer, void *in0, b32 is_absolute, PrintOptions opt)
{
  if (is_absolute)
    return print(buffer, (Term*)in0, opt);
  else
    return print(buffer, (Ast*)in0, opt);
}

forward_declare inline Scope *
newScope(Scope *outer, Arrow *signature)
{
  Scope *scope = pushStruct(temp_arena, Scope, true);
  scope->outer = outer;
  scope->first = signature;
  scope->depth = outer ? outer->depth+1 : 1;
  return scope;
}

forward_declare inline b32
equal(Term *lhs, Term *rhs)
{
  return equalTrinary(lhs, rhs) == Trinary_True;
}

inline b32
isCompositeConstructor(Term *in0)
{
  if (Composite *in = castTerm(in0, Composite))
    return in->op->cat == Term_Constructor;
  else
    return false;
}

inline b32
isGlobalValue(Term *in0)
{
  return (b32)in0->global_name;
}

inline b32
isGround(Term *in0)
{
  if (isGlobalValue(in0))
    return true;

  switch (in0->cat)
  {
    case Term_Composite:
    {
      Composite *composite = castTerm(in0, Composite);
      if (!isGround(composite->op))
        return false;

      for (int id=0; id < composite->arg_count; id++)
      {
        if (!isGround(composite->args[id]))
          return false;
      }

      return true;
    } break;

    case Term_Builtin:
    {return true;} break;

    case Term_Hole:
    case Term_Variable:
    case Term_Arrow:
    case Term_Function:
    case Term_Fork:
    case Term_Accessor:
    case Term_Rewrite:
    case Term_Computation:
    case Term_Union:
    case Term_Constructor:
    {return false;} break;
  }
}

// todo make this an inline mutation
internal Term *
rebaseMain(MemoryArena *arena, Term *in0, i32 delta, i32 offset)
{
  assert(delta >= 0);
  Term *out0 = 0;
  if (!isGround(in0) && (delta > 0))
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in  = castTerm(in0, Variable);
        if (in->delta >= offset)
        {
          Variable *out = copyStruct(arena, in);
          out->delta += delta;
          out0 = &out->t;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in  = castTerm(in0, Composite);
        Composite *out = copyStruct(arena, in);
        allocateArray(arena, out->arg_count, out->args);
        out->op = rebaseMain(arena, out->op, delta, offset);
        for (i32 id = 0; id < out->arg_count; id++)
          out->args[id] = rebaseMain(arena, in->args[id], delta, offset);
        out0 = &out->t;
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);
        allocateArray(arena, in->param_count, out->param_types);
        for (i32 id=0; id < in->param_count; id++)
          out->param_types[id] = rebaseMain(arena, in->param_types[id], delta, offset+1);
        if (in->output_type)
        {
          out->output_type = rebaseMain(arena, in->output_type, delta, offset+1);
        }
        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Accessor *out = copyStruct(arena, in);
        out->record = rebaseMain(arena, in->record, delta, offset);
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in  = castTerm(in0, Rewrite);
        Rewrite *out = copyStruct(arena, in);
        out->eq_proof = rebaseMain(arena, in->eq_proof, delta, offset);
        out->body     = rebaseMain(arena, in->body, delta, offset);
        out0 = &out->t;
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = copyStruct(arena, in);
        out->lhs = rebaseMain(arena, in->lhs, delta, offset);
        out->rhs = rebaseMain(arena, in->rhs, delta, offset);
        out0 = &out->t;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyStruct(arena, in);
        out->body = rebaseMain(arena, in->body, delta, offset+1);
        out0 = &out->t;
      } break;

      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyStruct(arena, in);
        allocateArray(arena, in->ctor_count, out->structs);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *rebased = rebaseMain(arena, &in->structs[id]->t, delta, offset);
          out->structs[id] = castTerm(rebased, Arrow);
        }
        out0 = &out->t;
      } break;

      case Term_Constructor:
      {
        Constructor *in  = castTerm(in0, Constructor);
        // todo kinda nasty that we have to rebase the whole union. But what can
        // we really do? Since direct mutation is out of question atm.
        Union *uni = castTerm(rebaseMain(arena, &in->uni->t, delta, offset), Union);
        if (uni == in->uni)
          out0 = in0;
        else
        {
          Constructor *out = copyStruct(arena, in);
          out->uni = uni;
          out0 = &out->t;
        }
      } break;

      default:
        todoIncomplete;
    }
  }
  else
    out0 = in0;
  assert(out0);
  return out0;
}

forward_declare internal Term *
rebase(MemoryArena *arena, Term *in0, i32 delta)
{
  return rebaseMain(arena, in0, delta, 0);
}

internal Term *
apply(MemoryArena *arena, Term *op, i32 arg_count, Term **args, Term *type)
{
  Term *out0 = 0;

#if DEBUG_LOG_apply
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {debugIndent(); DUMP("apply(", serial, "): ", op, "(...)\n");}
#endif

  if (Function *fun = castTerm(op, Function))
  {// Function application
    if (fun->body != &dummy_function_being_built)
      out0 = evaluate(arena, args, fun->body, EvaluationFlag_ApplyMode);
  }
  else if (op == &builtins.equal->t)
  {// special case for equality
    Term *l0 = args[1];
    Term *r0 = args[2];

    if (Composite *l = castTerm(l0, Composite))
    {
      if (Constructor *lctor = castTerm(l->op, Constructor))
      {
        if (Composite *r = castTerm(r0, Composite))
        {
          if (Constructor *rctor = castTerm(r->op, Constructor))
          {
            if (lctor->id == rctor->id)
            {
              if (l->arg_count == 0)
              {
                // we can't do anything here
              }
              else if (l->arg_count == 1)
              {
                Term *larg = l->args[0];
                Term *rarg = r->args[0];
                Term **args = pushArray(arena, 3, Term*);
                args[0] = getType(larg);
                args[1] = larg;
                args[2] = rarg;
                out0 = apply(arena, &builtins.equal->t, 3, args, type);
                if (!out0)
                  out0 = newEquality(arena, getType(larg), larg, rarg);
              }
              else
                todoIncomplete;  // need conjunction
            }
          }
        }
      }
    }

    Trinary compare = equalTrinary(l0, r0);
    // #hack to handle inconsistency
    if (compare == Trinary_False)
      out0 = &builtins.False->t;
  }
  else if (op->cat == Term_Constructor)
  {
    out0 = newComposite(arena, op, arg_count, args, type);
  }

#if DEBUG_LOG_apply
  if (DEBUG_MODE) {debugDedent(); DUMP("=> ", out0, "\n");}
#endif
  return out0;
}

internal Term *
evaluateMain(EvaluationContext *ctx, Term *in0)
{
  Term *out0 = 0;
  assert(ctx->offset >= 0);
  MemoryArena *arena = ctx->arena;

#if DEBUG_LOG_evaluate
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {DEBUG_INDENT(); DUMP("evaluate(", serial, "): ", in0, "\n");}
#endif

  if (isGlobalValue(in0))
    out0 = in0;
  else
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->delta == ctx->offset)
        {
          out0 = ctx->args[in->id];
          out0 = rebase(arena, out0, ctx->offset);
        }
        else if (in->delta > ctx->offset)
        {
          Variable *out = copyStruct(arena, in);
          out->delta--;  // TODO this is rocket science in here...
          out0 = &out->t;
        }
        else
          out0 = in0;
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        Term **args = pushArray(arena, in->arg_count, Term *);

        Term *op = evaluateMain(ctx, in->op);
        for (i32 id=0; id < in->arg_count; id++)
        {
          args[id] = evaluateMain(ctx, in->args[id]);
          assert(args[id]);
        }

        if (checkFlag(ctx->flags, EvaluationFlag_ApplyMode))
        {
          out0 = apply(arena, op, in->arg_count, args, getType(in0));
        }

        if (!out0)
        {
          Composite *out = copyStruct(arena, in);
          out->op   = op;
          out->args = args;
          out0 = &out->t;
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);

        allocateArray(arena, out->param_count, out->param_types);
        ctx->offset++;
        for (i32 id=0; id < out->param_count; id++)
        {
          out->param_types[id] = evaluateMain(ctx, in->param_types[id]);
        }
        if (in->output_type)
          out->output_type = evaluateMain(ctx, in->output_type);
        ctx->offset--;

        out0 = &out->t;
      } break;

      case Term_Function:
      {
        Function *in  = castTerm(in0, Function);
        Function *out = copyStruct(arena, in);
        out->type = evaluateMain(ctx, in->type);

        u32 old_flags = ctx->flags;
        unsetFlag(&ctx->flags, EvaluationFlag_ApplyMode);
        ctx->offset++;
        out->body = evaluateMain(ctx, in->body);
        ctx->offset--;
        ctx->flags = old_flags;

        out0 = &out->t;
      } break;

      case Term_Accessor:
      {
        Accessor *in  = castTerm(in0, Accessor);
        Term *record0 = evaluateMain(ctx, in->record);
        if (Composite *record = castRecord(record0))
          // note: we could honor "ctx->normalize" but idk who would actually want that.
          out0 = record->args[in->field_id];
        else
        {
          Accessor *out = copyStruct(arena, in);
          out->record = record0;
          out0 = &out->t;
        }
      } break;

      case Term_Computation:
      {
        Computation *in  = castTerm(in0, Computation);
        Computation *out = copyStruct(arena, in);
        // NOTE: semi-hack so it doesn't normalize our propositions.
        u32 old_flags = ctx->flags;
        unsetFlag(&ctx->flags, EvaluationFlag_ApplyMode);
        out->lhs = evaluateMain(ctx, in->lhs);
        out->rhs = evaluateMain(ctx, in->rhs);
        ctx->flags = old_flags;
        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        if (Term *eq_proof = evaluateMain(ctx, in->eq_proof))
        {
          if (Term *body = evaluateMain(ctx, in->body))
          {
            Rewrite *out = copyStruct(arena, in);
            out->eq_proof = eq_proof;
            out->body     = body;
            out0 = &out->t;
          }
        }
      } break;

      case Term_Fork:
      {
        Fork *in = castTerm(in0, Fork);
        Term *subject0 = evaluateMain(ctx, in->subject);
        if (checkFlag(ctx->flags, EvaluationFlag_ApplyMode))
        {
          if (Composite *subject = castTerm(subject0, Composite))
          {
            if (Constructor *ctor = castTerm(subject->op, Constructor))
              out0 = evaluateMain(ctx, in->bodies[ctor->id]);
          }
        }
        else
        {
          Fork *out = copyStruct(arena, in);
          out->subject = subject0;
          allocateArray(arena, in->case_count, out->bodies);
          for (i32 id=0; id < in->case_count; id++)
            out->bodies[id] = evaluateMain(ctx, in->bodies[id]);
          out0 = &out->t;
        }
      } break;

      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyStruct(arena, in);
        allocateArray(arena, in->ctor_count, out->structs);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *struc = evaluateMain(ctx, &in->structs[id]->t);
          out->structs[id] = castTerm(struc, Arrow);
        }
        out0 = &out->t;
      } break;

      case Term_Builtin:
      case Term_Constructor:
      case Term_Hole:
      {out0=in0;} break;
    }
  }

#if DEBUG_LOG_evaluate
  if (DEBUG_MODE) {DEBUG_DEDENT(); DUMP("=> ", out0, "\n");}
#endif

  assert(checkFlag(ctx->flags, EvaluationFlag_ApplyMode) || out0);
  return out0;
}

forward_declare inline Term *
evaluate(MemoryArena *arena, Term **args, Term *in0)
{
  EvaluationContext ctx = {.arena=arena, .args=args};
  return evaluateMain(&ctx, in0);
}

forward_declare inline Term *
evaluate(MemoryArena *arena, Term **args, Term *in0, u32 flags)
{
  EvaluationContext ctx = {.arena=arena, .args=args, .flags=flags};
  return evaluateMain(&ctx, in0);
}

// NOTE: we can't guarantee that compare would be of the same type, because the
// tree search needs it.
forward_declare internal CompareTerms
compareTerms(MemoryArena *arena, Term *lhs0, Term *rhs0)
{
  CompareTerms out = {};
  out.result = Trinary_Unknown;

#if DEBUG_LOG_compare
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {
    debugIndent(); DUMP("comparing(", serial, "): ", lhs0, " and ", rhs0, "\n");
  }
#endif

  if (lhs0 == rhs0)
    out.result = {Trinary_True};
  else if (lhs0->cat == rhs0->cat)
  {
    switch (lhs0->cat)
    {
      case Term_Variable:
      {
        Variable *lhs = castTerm(lhs0, Variable);
        Variable *rhs = castTerm(rhs0, Variable);
        if ((lhs->delta == rhs->delta) && (lhs->id == rhs->id))
          out.result = Trinary_True;
      } break;

      case Term_Arrow:
      {
        Arrow* lhs = castTerm(lhs0, Arrow);
        Arrow* rhs = castTerm(rhs0, Arrow);
        i32 param_count = lhs->param_count;
        if (rhs->param_count == param_count)
        {
          b32 type_mismatch = false;
          for (i32 id = 0; id < param_count; id++)
          {
            if (!equal(lhs->param_types[id], rhs->param_types[id]))
            {
              type_mismatch = true;
              break;
            }
          }
          if (!type_mismatch)
          {
            if (lhs->output_type && rhs->output_type)
              out.result = equalTrinary(lhs->output_type, rhs->output_type);
            else if (!rhs->output_type && !rhs->output_type)
              out.result = Trinary_True;
            else
              out.result = Trinary_False;
          }
        }
        else
          out.result = Trinary_False;
      } break;

      case Term_Composite:
      {
        Composite *lhs = castTerm(lhs0, Composite);
        Composite *rhs = castTerm(rhs0, Composite);

        Trinary op_compare = equalTrinary(lhs->op, rhs->op);
        if ((op_compare == Trinary_False) &&
            (lhs->op->cat == Term_Constructor) &&
            (rhs->op->cat == Term_Constructor))
        {
          out.result = Trinary_False;
        }
        else if (op_compare == Trinary_True)
        {
          i32 count = lhs->arg_count;
          assert(lhs->arg_count == rhs->arg_count);

          i32 mismatch_count = 0;
          i32 false_count = 0;
          int       unique_diff_id   = 0;
          TreePath *unique_diff_path = 0;
          out.result = Trinary_True;
          for (i32 id=0; id < count; id++)
          {
            CompareTerms recurse = compareTerms(arena,lhs->args[id], rhs->args[id]);
            if (recurse.result != Trinary_True)
            {
              mismatch_count++;
              if (mismatch_count == 1)
              {
                unique_diff_id   = id;
                unique_diff_path = recurse.diff_path;
              }
              if (recurse.result == Trinary_False)
                false_count++;
            }
          }
          if (mismatch_count > 0)
          {
            out.result = Trinary_Unknown;
            if ((lhs->op->cat == Term_Constructor) &&
                (rhs->op->cat == Term_Constructor) &&
                (false_count > 0))
            {
              out.result = Trinary_False;
            }
          }
          if (out.result == Trinary_Unknown && (mismatch_count == 1) && arena)
          {
            allocate(arena, out.diff_path);
            out.diff_path->first = unique_diff_id;
            out.diff_path->next  = unique_diff_path;
          }
        }
      } break;

      case Term_Constructor:
      {
        Constructor *lhs = castTerm(lhs0, Constructor);
        Constructor *rhs = castTerm(rhs0, Constructor);
        out.result = toTrinary(equal(&lhs->uni->t, &rhs->uni->t) &&
                               (lhs->id == rhs->id));
      } break;

      case Term_Accessor:
      {
        Accessor *lhs = castTerm(lhs0, Accessor);
        Accessor *rhs = castTerm(rhs0, Accessor);
        out.result = compareTerms(arena,lhs->record, rhs->record).result;
      } break;

      case Term_Builtin:
      {
        out.result = toTrinary(lhs0 == rhs0);
      } break;

      case Term_Union:
      {
        if (!isGlobalValue(lhs0) && !isGlobalValue(rhs0))  // only support anonymous union compare rn, to avoid dealing with recursive structs
        {
          Union *lhs = castTerm(lhs0, Union);
          Union *rhs = castTerm(rhs0, Union);
          i32 ctor_count = lhs->ctor_count;
          if (rhs->ctor_count == ctor_count)
          {
            b32 found_mismatch = false;
            for (i32 id=0; id < ctor_count; id++)
            {
              if (!equal(&lhs->structs[id]->t,
                         &rhs->structs[id]->t))
              {
                found_mismatch = true;
              }
            }
            if (!found_mismatch)
              out.result = Trinary_True;
          }
        }
      } break;

      case Term_Function:
      case Term_Hole:
      case Term_Rewrite:
      case Term_Computation:
      case Term_Fork:
      {} break;
    }
  }

#if DEBUG_LOG_compare
  if (DEBUG_MODE)
  {debugDedent(); dump("=> "); dump(out.result); dump();}
#endif

  return out;
}

forward_declare internal Trinary
equalTrinary(Term *lhs0, Term *rhs0)
{
  return compareTerms(0, lhs0, rhs0).result;
}

internal GlobalBinding *
lookupGlobalNameSlot(String key, b32 add_new)
{
  // :global-bindings-zero-at-startup
  GlobalBinding *slot = 0;
  u32 hash = stringHash(key) % arrayCount(global_state.bindings->table);
  slot = global_state.bindings->table + hash;
  b32 first_slot_valid = slot->key.length == 0;
  if (first_slot_valid)
  {
    while (true)
    {
      if (equal(slot->key, key))
        break;
      else if (slot->next_hash_slot)
        slot = slot->next_hash_slot;
      else
      {
        if (add_new)
        {
          slot->next_hash_slot = pushStruct(global_state.top_level_arena, GlobalBinding, true);
          slot = slot->next_hash_slot;
          slot->key = key;
        }
        else slot = 0;
        break;
      }
    }
  }
  else if (add_new) slot->key = key;
  else slot = 0;

  if (slot && !add_new) assert(slot->count != 0);

  return slot;
}

internal GlobalBinding *
lookupGlobalNameSlot(Identifier *ident, b32 add_new)
{
  return lookupGlobalNameSlot(ident->token.string, add_new);
}

struct LookupCurrentFrame { LocalBinding* slot; b32 found; };

internal LookupCurrentFrame
lookupCurrentFrame(LocalBindings *bindings, String key, b32 add_if_missing)
{
  LocalBinding *slot = 0;
  b32 found = false;
  u32 hash = stringHash(key) % arrayCount(bindings->table);
  slot = bindings->table + hash;
  b32 first_slot_valid = slot->key.length;
  if (first_slot_valid)
  {
    b32 stop = false;
    while (!stop)
    {
      if (equal(slot->key, key))
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
  }

  LookupCurrentFrame out = { slot, found };
  return out;
}

struct NormalizeContext {
  MemoryArena *arena;
  DataMap     *map;
  i32          depth;
};

// todo #cleanup #mem don't allocate without progress
internal Term *
normalizeMain(NormalizeContext *ctx, Term *in0) 
{
  Term *out0 = in0;
  MemoryArena *arena = ctx->arena;

#if DEBUG_LOG_normalize
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {DEBUG_INDENT(); DUMP("normalize(", serial, "): ", in0, "\n");}
#endif

  if (!isGlobalValue(in0))
  {
    switch (in0->cat)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        b32 progressed = false;

        Term **norm_args = pushArray(arena, in->arg_count, Term*);
        for (auto arg_id = 0;
             arg_id < in->arg_count;
             arg_id++)
        {
          norm_args[arg_id] = normalizeMain(ctx, in->args[arg_id]);
          progressed = progressed || (norm_args[arg_id] != in->args[arg_id]);
        }

        Term *norm_op = normalizeMain(ctx, in->op);
        progressed = progressed || (norm_op != in->op);

        out0 = apply(arena, norm_op, in->arg_count, norm_args, getType(in0));

        if (!out0)
        {
          Composite *out = copyStruct(arena, in);
          out->op   = norm_op;
          out->args = norm_args;
          out0 = &out->t;
        }
      } break;

      case Term_Arrow:
      {
        Arrow *in  = castTerm(in0, Arrow);
        Arrow *out = copyStruct(arena, in);

        allocateArray(arena, out->param_count, out->param_types);
        ctx->depth++;
        for (i32 id=0; id < out->param_count; id++)
          out->param_types[id] = normalizeMain(ctx, in->param_types[id]);
        if (in->output_type)
          out->output_type = normalizeMain(ctx, in->output_type);
        ctx->depth--;

        out0 = &out->t;
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        Term *body     = normalizeMain(ctx, in->body);
        Term *eq_proof = normalizeMain(ctx, in->eq_proof);
        if ((body != in->body) || (eq_proof != in->eq_proof))
        {
          Rewrite *out = copyStruct(arena, in);
          out->eq_proof = eq_proof;
          out->body     = body;
          out0 = &out->t;
        }
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Term *record0 = normalizeMain(ctx, in->record);
        if (Composite *record = castRecord(record0))
          out0 = record->args[in->field_id];
        else if (record0 != in->record)
        {
          Accessor *out = copyStruct(arena, in);
          out->record = record0;
          out0 = &out->t;
        }
      } break;

      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        i32 var_depth = ctx->depth - in->delta;
        DataTree *tree = 0;
        for (DataMap *map = ctx->map; map; map=map->next)
        {
          if (map->depth == var_depth && map->index == in->id)
          {
            tree = &map->tree;
            break;
          }
        }
        if (tree)
          out0 = synthesizeTree(arena, in0, tree);
      } break;

      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyStruct(arena, in);
        allocateArray(arena, in->ctor_count, out->structs);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *signature = &in->structs[id]->t;
          signature = normalizeMain(ctx, signature);
          out->structs[id] = castTerm(signature, Arrow);
        }
        out0 = &out->t;
      } break;

      case Term_Fork:
      case Term_Hole:
      {invalidCodePath;} break;

      case Term_Constructor:
      case Term_Builtin:
      case Term_Function:
      case Term_Computation:
      {} break;
    }
  }

#if DEBUG_LOG_normalize
  if (DEBUG_MODE)
  {DEBUG_DEDENT(); dump("=> "); dump(out0); dump();}
#endif

  // assert(isSequenced(in0) || out0);
  assert(out0);
  return out0;
}

forward_declare internal Term *
normalize(MemoryArena *arena, DataMap *map, i32 depth, Term *in0)
{
  NormalizeContext ctx = {.arena=arena, .map=map, .depth=depth};
  return normalizeMain(&ctx, in0);
}

forward_declare internal Term *
normalize(MemoryArena *arena, Typer *env, Term *in0)
{
  NormalizeContext ctx = {.arena=arena, .map=(env ? env->map : 0), .depth=getScopeDepth(env)};
  return normalizeMain(&ctx, in0);
}

inline void
addLocalBinding(Typer *env, String key, i32 var_id)
{
  auto lookup = lookupCurrentFrame(env->bindings, key, true);
  lookup.slot->var_id = var_id;
}

forward_declare inline void
introduceSignature(Typer *env, Arrow *signature, b32 add_bindings)
{
  i32 param_count = signature->param_count;
  env->scope = newScope(env->scope, signature);
  if (add_bindings)
  {
    extendBindings(temp_arena, env);
    for (i32 index=0; index < param_count; index++)
    {
      String name = signature->param_names[index];
      addLocalBinding(env, name, index);
    }
  }
  assert(noError());
}

inline GlobalBinding *
lookupGlobalName(Token *token)
{
  if (GlobalBinding *slot = lookupGlobalNameSlot(token->string, false))
    return slot;
  else
  {
    // note: assume that if the code gets here, then the identifier isn't in
    // local scope either.
    tokenError(token, "identifier not found");
    attach("identifier", token);
    return 0;
  }
}

inline Term *
lookupBuiltinGlobalName(char *name)
{
  Token token = newToken(name);
  GlobalBinding *slot = lookupGlobalName(&token);
  assert(slot->count == 1);
  return slot->items[0];
}

inline void
addGlobalBinding(Token *name, Term *value)
{
  GlobalBinding *slot = lookupGlobalNameSlot(name->string, true);
  // TODO #cleanup check for type conflict
  slot->items[slot->count++] = value;
  assert(slot->count < arrayCount(slot->items));
  Token *name_copy = copyStruct(global_state.top_level_arena, name);
  value->global_name = name_copy;
}

inline void
addBuiltinGlobalBinding(char *key, Term *value)
{
  Token token = newToken(key);
  addGlobalBinding(&token, value);
}

inline LookupLocalName
lookupLocalName(Typer *env, Token *token)
{
  LocalBindings *bindings = env->bindings;
  LookupLocalName out = {};
  for (i32 stack_delta = 0;
       bindings;
       stack_delta++)
  {
    LookupCurrentFrame lookup = lookupCurrentFrame(bindings, token->string, false);
    if (lookup.found)
    {
      out.found       = true;
      out.var_id   = lookup.slot->var_id;
      out.stack_delta = stack_delta;
      break;
    }
    else
      bindings = bindings->next;
  }

  return out;
}

inline b32
requireChar(char c, char *reason = 0, Tokenizer *tk=global_tokenizer)
{
  auto out = false;
  if (!reason)
    reason = "";
  if (hasMore(tk))
  {
    Token token = nextToken(tk);
    if (token.string.length == 1 && token.string.chars[0] == c)
      out = true;
    else
    {
      parseError(tk, &token, "expected character '%c' (%s)", c, reason);
    }
  }
  return out;
}

inline b32
requireCategory(TokenCategory tc, char *message=0, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    if (nextToken(tk).cat == tc) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
requireIdentifier(char *message, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = nextToken(tk);
    if (isIdentifier(&token)) out = true;
    else tokenError(message, tk);
  }
  return out;
}

inline b32
optionalCategory(TokenCategory tc, Tokenizer *tk = global_tokenizer)
{
  b32 out = false;
  if (hasMore())
    if (peekToken(tk).cat == tc)
    {
      out = true;
      nextToken();
    }

  return out;
}

inline b32
optionalChar(char c, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken(tk);
    if (equal(&token, c))
    {
      out = true;
      nextToken(tk);
    }
  }
  return out;
}

inline b32
optionalString(char *str, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  if (hasMore())
  {
    Token token = peekToken(tk);
    if (equal(&token, str))
    {
      out = true;
      nextToken(tk);
    }
  }
  return out;
}

struct OptionalU32 { b32 success; u32 value; };

// builtin expession end markers for now
inline b32
isExpressionEndMarker(Token *token)
{
  if (inString("{},);:", token))
    return true;

  if (token->cat > Token_Directive_START && token->cat < Token_Directive_END)
    return true;

  switch (token->cat)
  {
    case Token_DoubleColon:
    case Token_ColonEqual:
    case Token_DoubleDash:
    case Token_StrongArrow:
      return true;
    default: {}
  }

  return false;
}

inline b32
seesExpressionEndMarker()
{
  Token token = peekToken();
  return isExpressionEndMarker(&token);
}

// todo remove recursion.
internal Term *
subExpressionAtPath(Term *in, TreePath *path)
{
  if (path)
  {
    switch (in->cat)
    {
      case Term_Composite:
      {
        Composite *composite = castTerm(in, Composite);
        Term *arg = composite->args[path->first];
        return subExpressionAtPath(arg, path->next); 
      } break;

      invalidDefaultCase;
    }
  }
  else
    return in;
}

#if 0
internal TreePath *
treePathFromAccessor(MemoryArena *arena, Accessor *accessor)
{
  TreePath *out = 0;
  for (Accessor *iter = accessor; iter; iter = castTerm(iter->record, Accessor))
  {
    TreePath *new_path = pushStruct(arena, TreePath);
    new_path->first = accessor->field_id;
    new_path->next = out;
    out = new_path;
  }
  return out;
}
#endif

inline i32
getExplicitParamCount(ArrowAst *in)
{
  i32 out = 0;
  for (i32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!isHiddenParameter(in, param_id))
      out++;
  }
  return out;
}

inline i32
getExplicitParamCount(Arrow *in)
{
  i32 out = 0;
  for (i32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!isHiddenParameter(in, param_id))
      out++;
  }
  return out;
}

inline b32
matchType(Term *actual, Term *goal)
{
  b32 out = false;
  if (goal->cat == Term_Hole)
    out = true;
  else
  {
    if (equal(actual, goal))
      out = true;
  }
  return out;
}

inline Stack *
newStack(MemoryArena *arena, Stack *outer, i32 count)
{
  Stack *stack = pushStruct(arena, Stack);
  stack->outer = outer;
  allocateArray(arena, count, stack->items, true);
  return stack;
}

// todo we don't even need the scope, since type is in term now.
internal b32
unify(Stack *stack, Term *l0, Term *goal0)
{
  b32 success = false;

  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
#if DEBUG_LOG_unify
  if (DEBUG_MODE)
  {debugIndent(); DUMP("unify(", serial, ") ", lhs0, " with ", goal0, "\n");}
#endif

  switch (l0->cat)
  {
    case Term_Variable:
    {
      Variable *lhs = castTerm(l0, Variable);
      Stack *lookup_stack = stack;
      for (i32 delta=0; delta < lhs->delta; delta++)
      {
        lookup_stack = lookup_stack->outer;
      }
      if (Term *lookup = lookup_stack->items[lhs->id])
      {
        if (equal(lookup, goal0))
          success = true;
      }
      else if (unify(stack, getType(l0), getType(goal0)))
      {
        stack->items[lhs->id] = goal0;
        success = true;
      }
    } break;

    case Term_Composite:
    {
      Composite *lhs = castTerm(l0, Composite);
      if (Composite *goal = castTerm(goal0, Composite))
      {
        if (unify(stack, lhs->op, goal->op))
        {
          success = true;
          for (int id=0; id < lhs->arg_count; id++)
          {
            if (!unify(stack, lhs->args[id], goal->args[id]))
            {
              success = false;
              break;
            }
          }
        }
      }
    } break;

    case Term_Arrow:
    {
      Arrow *lhs = castTerm(l0, Arrow);
      if (Arrow *goal = castTerm(goal0, Arrow))
      {
        if (lhs->param_count == goal->param_count)
        {
          b32 failed = false;
          Stack *new_stack = newStack(temp_arena, stack, lhs->param_count);
          for (i32 id=0; id < lhs->param_count; id++)
          {
            if (!unify(new_stack, lhs->param_types[id], goal->param_types[id]))
            {
              failed = true;
              break;
            }
          }
          if (!failed)
            success = true;
        }
      }
    } break;

    case Term_Function:
    case Term_Union:
    case Term_Constructor:
    case Term_Builtin:
    {
      success = equal(l0, goal0);
    } break;

    default:
    {
      todoIncomplete;
    } break;
  }

#if DEBUG_LOG_unify
  if (DEBUG_MODE)
  {debugDedent(); DUMP("=>(", serial, ") ", ((char *)(success ? "true\n" : "false\n")));}
#endif

  return success;
}

inline SolveArgs
solveArgs(Solver *solver, Term *op, Term *goal)
{
  b32    matches   = false;
  i32    arg_count = 0;
  Term **args      = 0;
  if (Constructor *ctor = castTerm(op, Constructor))
  {
    if (equal(&ctor->uni->t, goal))
      matches = true;  // we don't know what the members are in the constructor case.
  }
  else if (Arrow *signature = castTerm(getType(op), Arrow))
  {
    Stack *stack = newStack(solver->arena, 0, signature->param_count);
    if (unify(stack, signature->output_type, goal))
    {
      matches   = true;
      arg_count = signature->param_count;
      args      = stack->items;
      for (i32 i=0; i < signature->param_count; i++)
      {
        // solving loop
        if (!args[i])
        {
          // todo #leak the type could be referenced
          Term *type = evaluate(solver->arena, args, signature->param_types[i]);
          if (!(args[i] = solveForGoal(solver, type)))
          {
            args = 0;
            break;
          }
        }
      }
    }
  }
  return SolveArgs{matches, arg_count, args};
}

inline SolveArgs
solveArgs(Solver solver, Term *op, Term *goal)
{
  return solveArgs(&solver, op, goal);
}

forward_declare internal Term *
solveForGoal(Solver *solver, Term *goal)
{
  Term *out = 0;
  solver->depth++;

  b32 should_attempt_inference = true;
  if (solver->depth > MAX_SOLVE_DEPTH ||
      goal == &builtins.Set->t ||
      goal->cat == Term_Hole)
  {
    should_attempt_inference = false;
  }
  else if (Union *uni = castTerm(goal, Union))
  {
    if (uni->global_name)
      should_attempt_inference = false;
  }

  if (should_attempt_inference)
  {
#if DEBUG_LOG_solve
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {DEBUG_INDENT(); DUMP("solve(", serial, "): ", goal, "\n");}
#endif

    if (auto [l,r] = getEqualitySides(goal, false))
    {
      if (equal(normalize(temp_arena, solver->env, l),
                normalize(temp_arena, solver->env, r)))
      {
        out = newComputation(solver->arena, solver->env, l, r);
      }
    }

    if (!out)
    {
      b32 tried_global_hints = false;
      for (HintDatabase *hints = solver->local_hints;
           !out;
           hints = hints->next)
      {
        if (!hints)
        {
          if (!tried_global_hints && solver->use_global_hints)
          {
            hints = global_state.hints;
            tried_global_hints = true;
          }
        }

        if (hints)
        {
          Term *hint = hints->first;
          if (getType(hint)->cat == Term_Arrow)
          {
            SolveArgs solution = solveArgs(solver, hint, goal);
            if (solution.args)
            {
              MemoryArena *arena = solver->arena;
              Term **args = copyArray(arena, solution.arg_count, solution.args);
              out = newComposite(arena, hint, solution.arg_count, args, goal);
            }
          }
          else if (equal(getType(hint), goal))
            out = hint;
        }
        else
          break;
      }
    }

    if (out)
      assert(equal(getType(out), goal));

#if DEBUG_LOG_solve
  if (DEBUG_MODE) {DEBUG_DEDENT(); DUMP("=> ", out, "\n");}
#endif
  }

  solver->depth--;
  return out;
}

internal Term *
solveForGoal(Solver solver, Term *goal)
{
  return solveForGoal(&solver, goal);
}

inline TermArray
getFunctionOverloads(Identifier *ident, Term *output_type_goal)
{
  TermArray out = {};
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
  {
    if (output_type_goal->cat == Term_Hole)
    {
      out.items = slot->items;
      out.count = slot->count;
    }
    else
    {
      allocateArray(temp_arena, slot->count, out.items);
      for (int slot_id=0; slot_id < slot->count; slot_id++)
      {
        Term *item = slot->items[slot_id];
        if (solveArgs(Solver{.arena=temp_arena}, item, output_type_goal).matches)
          out.items[out.count++] = slot->items[slot_id];
      }
      if (out.count == 0)
      {
        parseError(&ident->a, "found no matching overload");
        attach("function", ident->token.string);
        attach("output_type_goal", output_type_goal);
        attach("available_overloads", slot->count, slot->items, printOptionPrintType());
      }
    }
  }
  else
  {
    parseError(&ident->a, "identifier not found");
    attach("identifier", ident->token.string);
  }
  return out;
}

inline Term *
getMatchingFunctionCall(MemoryArena *arena, Typer *env, Identifier *ident, Term *goal)
{
  // NOTE: This routine is different from "solveForGoal" in that the top-level
  // operator is fixed.
  Term *out = 0;
  pushContext(__func__);

  if (goal->cat == Term_Hole)
  {
    parseError(&ident->a, "cannot infer arguments since we do know what the output type of this function should be");
  }
  else if (lookupLocalName(env, &ident->token))
  {
    todoIncomplete;
  }
  else if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
  {
    for (int slot_i=0;
         slot_i < slot->count && noError() && !out;
         slot_i++)
    {
      Term *item = slot->items[slot_i];
      SolveArgs solution = solveArgs(Solver{.arena=temp_arena}, item, goal);
      if (solution.matches)
      {
        if (solution.args)
        {
          Term **args = copyArray(arena, solution.arg_count, solution.args);
          out = newComposite(arena, slot->items[slot_i], solution.arg_count, args);
          assert(equal(getType(out), goal));
          // NOTE: we don't care which function matches, just grab whichever
          // matches first.
        }
        else
        {
          parseError(&ident->token, "cannot automatically fill in some arguments");
          attach("function", item);
          attach("goal", goal);
        }
      }
    }
    if (!out && noError())
    {
      parseError(&ident->a, "found no matching overload");
      attach("available_overloads", slot->count, slot->items, printOptionPrintType());
    }
  }
  else
  {
    parseError(&ident->a, "identifier not found");
    attach("identifier", ident->token.string);
  }
  
  popContext();
  return out;
}

internal SearchOutput
searchExpression(MemoryArena *arena, Typer *env, Term *lhs, Term* in0)
{
  SearchOutput out = {};
  if (equal(in0, lhs))
    out.found = true;
  else
  {
    switch (in0->cat)
    {
      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        SearchOutput op = searchExpression(arena, env, lhs, in->op);
        if (op.found)
        {
          allocate(arena, out.path);
          out.found       = true;
          out.path->first = -1;
          out.path->next  = op.path;
        }
        else
        {
          for (int arg_id=0; arg_id < in->arg_count; arg_id++)
          {
            SearchOutput arg = searchExpression(arena, env, lhs, in->args[arg_id]);
            if (arg.found)
            {
              allocate(arena, out.path);
              out.found     = true;
              out.path->first = arg_id;
              out.path->next  = arg.path;
            }
          }
        }
      } break;

      case Term_Accessor:
      {
        Accessor* in = castTerm(in0, Accessor);
        out = searchExpression(arena, env, lhs, in->record);
      } break;

      case Term_Hole:
      case Term_Computation:
      case Term_Builtin:
      case Term_Union:
      case Term_Function:
      case Term_Constructor:
      case Term_Variable:
      case Term_Arrow:
      case Term_Rewrite:
      case Term_Fork:
      {} break;
    }
  }
  return out;
}

inline Ast *
parseSequence(MemoryArena *arena, b32 require_braces=true)
{
  Ast *out = 0;
  i32 count = 0;
  AstList *list = 0;

  b32 brace_opened = false;
  if (require_braces)
    brace_opened = requireChar('{');
  else
    brace_opened = optionalChar('{');

  for (b32 reached_end_of_sequence = false;
       noError() && !reached_end_of_sequence;
       )
  {
    Tokenizer tk_save = *global_tokenizer;
    Token token = nextToken();
    Ast *ast0 = 0;
    switch (token.cat)
    {
      case Token_Keyword_norm:
      {
        pushContext("norm [EXPRESSION]");
        if (seesExpressionEndMarker())
        {// normalize goal
          GoalTransform *ast = newAst(arena, GoalTransform, &token);
          ast0 = &ast->a;
        }
        else if (Ast *expression = parseExpressionToAst(arena))
        {// normalize with let.
          Let *let = newAst(arena, Let, &token);
          let->rhs  = expression;
          let->type = LET_TYPE_NORMALIZE;
          ast0 = &let->a;
          if (expression->cat == Ast_Identifier)
          {
            // borrow the name if the expression is an identifier 
            let->lhs  = expression->token.string;
          }
        }
        popContext();
      } break;

      case Token_Keyword_rewrite:
      {
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);

        rewrite->right_to_left = false;
        Token next = peekToken();
        if (equal(next.string, "<-"))
        {
          nextToken();
          rewrite->right_to_left = true;
        }

        rewrite->eq_proof = parseExpressionToAst(arena);
        ast0 = &rewrite->a;
      } break;

      case Token_StrongArrow:
      {
        pushContext("Goal transform: => [NEW_GOAL] [{ EQ_PROOF_HINT }]; ...");
        GoalTransform *ast = newAst(arena, GoalTransform, &token);
        ast0 = &ast->a;
        if (!optionalCategory(Token_Keyword_norm))
        {
          ast->new_goal = parseExpressionToAst(arena);
          if (optionalChar('{'))
          {
            if (optionalChar('}'))
            {
              // no hint provided, this case is just for editing convenience.
            }
            else
            {
              ast->hint = parseExpressionToAst(arena);
              requireChar('}');
            }
          }
        }
        popContext();
      } break;

      default:
      {
        if (isIdentifier(&token))
        {
          Token *name = &token;
          Token after_name = nextToken();
          switch (after_name.cat)
          {
            case Token_ColonEqual:
            {
              pushContext("let: NAME := VALUE");
              if (Ast *rhs = parseExpressionToAst(arena))
              {
                Let *let = newAst(arena, Let, name);
                ast0 = &let->a;
                let->lhs = name->string;
                let->rhs = rhs;
              }
              popContext();
            } break;

            case Token_Colon:
            {
              pushContext("typed let: NAME : TYPE := VALUE");
              if (Ast *type = parseExpressionToAst(arena))
              {
                if (requireCategory(Token_ColonEqual, ""))
                {
                  if (Ast *rhs = parseExpressionToAst(arena))
                  {
                    Let *let = newAst(arena, Let, name);
                    let->lhs  = name->string;
                    let->rhs  = rhs;
                    let->type = type;
                    ast0 = &let->a;
                  }
                }
              }
              popContext();
            } break;

            default: {};
          }
        }
        else if (isExpressionEndMarker(&token))
        {// synthetic hole
          *global_tokenizer = tk_save;
          ast0  = newAst(arena, Hole, &token);
          reached_end_of_sequence = true;
        }
      } break;

      case Token_Keyword_prove:
      {
        pushContext("prove PROPOSITION {SEQUENCE}");
        if (Ast *proposition = parseExpressionToAst(arena))
        {
          if (Ast *proof = parseSequence(arena, true))
          {
            Let *let = newAst(arena, Let, &token);
            let->lhs  = toString("anon");
            let->rhs  = proof;
            let->type = proposition;
            ast0 = &let->a;
          }
        }
        popContext();
      } break;
    }

    if (noError() && !ast0)
    {
      *global_tokenizer = tk_save;
      if (optionalCategory(Token_Keyword_fork))
        ast0 = parseFork(arena);
      else
        ast0 = parseExpressionToAst(arena);
      reached_end_of_sequence = true;
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->first = ast0;
      new_list->next  = list;
      list = new_list;
      // f.ex function definitions doesn't need to end with ';'
      optionalChar(';');
    }
  }

  if (brace_opened)
    requireChar('}');

  if (noError())
  {
    assert(count > 0);
    Ast *previous = 0;
    for (i32 id = 0; id < count; id++)
    {
      Ast *item0 = list->first;
      if (id > 0)
      {
        if (Let *let = castAst(item0, Let))
          let->body = previous;
        else if (RewriteAst *rewrite = castAst(item0, RewriteAst))
          rewrite->body = previous;
        else if (GoalTransform *item = castAst(item0, GoalTransform))
          item->body = previous;
        else
          invalidCodePath;
      }
      previous = item0;
      if (id != count-1)
        list = list->next;
    }
    out = list->first;
  }

  return out;
}

inline Ast *
synthesizeAst(MemoryArena *arena, Term *term, Token *token)
{
  SyntheticAst *out = newAst(arena, SyntheticAst, token);
  out->term = term;
  return &out->a;
}

internal Arrow *
copyArrow(MemoryArena *arena, Arrow *in)
{
  Arrow *out = copyStruct(arena, in);
  return out;
}

inline Constructor *
buildCtorAst(MemoryArena *arena, CtorAst *in, Term *output_type)
{
  Constructor *out = 0;
  if (Union *uni = castTerm(output_type, Union))
  {
    if (in->ctor_id < uni->ctor_count)
      out = newConstructor(arena, uni, in->ctor_id);
    else
      parseError(&in->a, "union only has %d constructors", uni->ctor_count);
  }
  else
  {
    parseError(&in->a, "cannot guess union");
  }
  return out;
}

inline HintDatabase *
addHint(MemoryArena *arena, HintDatabase *hint_db, Term *term)
{
  HintDatabase *new_hints = pushStruct(arena, HintDatabase, true);
  new_hints->first = term;
  new_hints->next  = hint_db;
  return new_hints;
}

forward_declare internal BuildTerm
buildTerm(MemoryArena *arena, Typer *env, Ast *in0, Term *goal)
{
  // todo #cleanup #mem: sort out what we need and what we don't need to persist
  // todo #cleanup #speed: returning the value is just a waste of time most of the time. Just call evaluate whenever you need the value.
  // todo return the type, since we typecheck it anyway.
  // todo print out the goal whenever we fail
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  BuildTerm out0 = {};
  assert(goal);
  b32 should_check_type = true;
  b32 recursed = false;

  switch (in0->cat)
  {
    case Ast_Hole:
    {
      if (Term *solution = solveForGoal(Solver{.arena=arena, .env=env, .use_global_hints=true}, goal))
        out0.term = solution;
      else
        parseError(in0, "please provide an expression here");
    } break;

    case Ast_SyntheticAst:
    {
      SyntheticAst *in = castAst(in0, SyntheticAst);
      out0.term = in->term;
    } break;

    case Ast_Identifier:
    {
      // Identifier *in = castAst(in0, Identifier);
      Token *name = &in0->token;
      if (LookupLocalName local = lookupLocalName(env, name))
      {
        Variable *var = newTerm(arena, Variable, 0);
        var->name  = in0->token.string;
        var->id    = local.var_id;
        var->delta = local.stack_delta;
        out0.term  = &var->t;
      }
      else
      {
        Term *value = 0;
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (i32 value_id = 0; value_id < globals->count; value_id++)
          {
            Term *slot_value = globals->items[value_id];
            if (matchType(todoGetType(arena, env, slot_value), goal))
            {
              if (value)
              {// ambiguous
                tokenError(name, "not enough type information to disambiguate global name");
                setErrorFlag(ErrorAmbiguousName);
                break;
              }
              else
                value = slot_value;
            }
          }
          if (!value)
          {
            tokenError(name, "global name does not match expected type");
            attach("name", name);
            attach("expected_type", goal);
            if (globals->count == 1)
              attach("actual_type", getTypeGlobal(globals->items[0]));
          }
        }

        if (value)
        {
          should_check_type = false;
          out0.term = value;
        }
      }
    } break;

    case Ast_CompositeAst:
    {
      CompositeAst *in  = castAst(in0, CompositeAst);

      if (in->arg_count == 1 &&
          in->args[0]->cat == Ast_Ellipsis)
      {
        // Infer all arguments.
        if (Identifier *op_ident = castAst(in->op, Identifier))
        {
          out0.term = getMatchingFunctionCall(arena, env, op_ident, goal);
        }
        else
          parseError(in->args[0], "todo: ellipsis only works with identifier atm");
      }
      else
      {
        Composite *out = newTerm(arena, Composite, 0);
        TermArray op_list = {};
        b32 should_build_op = true;
        if (Identifier *op_ident = castAst(in->op, Identifier))
        {
          if (!lookupLocalName(env, &in->op->token))
          {
            should_build_op = false;
            op_list = getFunctionOverloads(op_ident, goal);
          }
        }
        else if (CtorAst *op_ctor = castAst(in->op, CtorAst))
        {
          if (Constructor *ctor = buildCtorAst(arena, op_ctor, goal))
          {
            should_build_op = false;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.count    = 1;
            op_list.items[0] = &ctor->t;
          }
        }

        if (noError() && should_build_op)
        {
          if (BuildTerm build_op = buildTerm(arena, env, in->op, holev))
          {
            op_list.count = 1;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.items[0] = build_op.term;
          }
        }

        for (i32 attempt=0;
             (attempt < op_list.count) && !(out0.term) && noError();
             attempt++)
        {
          Term *op = op_list.items[attempt];
          if (Arrow *signature = castTerm(todoGetType(temp_arena, env, op), Arrow))
          {
            i32 param_count = signature->param_count;
            Ast **expanded_args = in->args;
            if (param_count != in->arg_count)
            {
              i32 explicit_param_count = getExplicitParamCount(signature);
              if (in->arg_count == explicit_param_count)
              {
                allocateArray(arena, param_count, expanded_args);
                for (i32 param_id = 0, arg_id = 0;
                     param_id < param_count;
                     param_id++)
                {
                  if (isHiddenParameter(signature, param_id))
                  {
                    // NOTE: We fill the missing argument with synthetic holes,
                    // because the user input might also have actual holes, so
                    // we want the code to be more uniform.
                    expanded_args[param_id] = newAst(arena, Hole, &in->op->token);
                  }
                  else
                  {
                    assert(arg_id < explicit_param_count);
                    expanded_args[param_id] = in->args[arg_id++];
                  }
                }
              }
              else
              {
                parseError(&in0->token, "argument count does not match the number of explicit parameters (expected: %d, got: %d)", explicit_param_count, in->arg_count);
              }
            }

            if (noError())
            {
              Term **args = pushArray(temp_arena, param_count, Term *);
              for (int arg_id = 0;
                   (arg_id < param_count) && noError();
                   arg_id++)
              {
                Term *param_type0 = signature->param_types[arg_id];
                Term *expected_arg_type = evaluate(arena, args, param_type0);

                // Typecheck & Inference for the arguments.
                if (expanded_args[arg_id]->cat == Ast_Hole)
                {
                  if (Term *fill = solveForGoal(Solver{.arena=arena, .env=env}, expected_arg_type))
                    args[arg_id] = fill;
                  else
                  {
                    Term *placeholder_arg = copyStruct(temp_arena, holev);
                    setType(placeholder_arg, expected_arg_type);
                    args[arg_id] = placeholder_arg;
                  }
                }
                else if (BuildTerm arg = buildTerm(arena, env, expanded_args[arg_id], expected_arg_type))
                {
                  args[arg_id] = arg.term;
                  if (expected_arg_type->cat == Term_Hole)
                  {
                    Variable *param_type = castTerm(param_type0, Variable);
                    assert(param_type->delta == 0);
                    Term *placeholder_arg = args[param_type->id];
                    assert(placeholder_arg->cat == Term_Hole);
                    Term *arg_type = todoGetType(arena, env, arg.term);
                    Term *arg_type_type = todoGetType(arena, env, arg_type);
                    if (equal(placeholder_arg->type, arg_type_type))
                      args[param_type->id] = arg_type;
                    else
                    {
                      parseError(expanded_args[arg_id], "type of argument has wrong type");
                      attach("expected", placeholder_arg->type);
                      attach("got", arg_type_type);
                    }
                  }
                }
              }

              if (noError())
              {
                for (i32 arg_id = 0; (arg_id < param_count); arg_id++)
                {
                  if (args[arg_id]->cat == Term_Hole)
                  {
                    parseError(in0, "cannot fill hole for argument %d", arg_id);
                    break;
                  }
                }
              }

              if (noError())
              {
                out->op        = op;
                out->arg_count = param_count;
                out->args      = copyArray(arena, param_count, args);
                out0.term  = &out->t;
              }
            }
          }
          else
          {
            parseError(in->op, "operator must have an arrow type");
            attach("operator type", todoGetType(temp_arena, env, op));
          }

          if (op_list.count > 1)
          {
            if (hasError() && !checkErrorFlag(ErrorUnrecoverable))
            {
              wipeError();
              if (attempt == op_list.count-1)
              {
                parseError(in->op, "found no suitable overload");
                attach("available_overloads", op_list.count, op_list.items, printOptionPrintType());
              }
            }
            else
              break;
          }
        }
      }
    } break;

    case Ast_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      Arrow *out = newTerm(arena, Arrow, &builtins.Type->t);
      i32 param_count = in->param_count;
      out->param_count   = param_count;
      out->param_names   = copyArray(arena, param_count, in->param_names);  // todo copy festival
      out->param_flags   = copyArray(arena, param_count, in->param_flags);
      {
        env->scope = newScope(env->scope, out);
        extendBindings(temp_arena, env);
        allocateArray(arena, param_count, out->param_types);
        for (i32 index=0; index < param_count && noError(); index++)
        {
          BuildTerm param_type = buildTerm(arena, env, in->param_types[index], holev);
          if (param_type)
          {
            out->param_types[index] = param_type.term;
            String name = in->param_names[index];
            addLocalBinding(env, name, index);
          }
        }

        if (noError())
        {
          out0.term = &out->t;
          if (in->output_type)
          {
            if (BuildTerm output_type = buildTerm(arena, env, in->output_type, holev))
              out->output_type = output_type.term;
          }
        }
        unwindBindingsAndScope(env);
      }
    } break;

    case Ast_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      Accessor *out = newTerm(arena, Accessor, 0);
      out->field_name = in->field_name.string;
      if (BuildTerm build_record = buildTerm(arena, env, in->record, holev))
      {
        Constructor ctor = getConstructor(env, build_record.term);
        if (ctor.uni)
        {
          out->record = build_record.term;
          Arrow *op_type = getType(&ctor);
          i32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          for (i32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->field_name.string, op_type->param_names[param_id]))
            {
              out->field_id  = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
            out0.term = &out->t;
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", ctor.uni->ctor_names[ctor.id]);
            setErrorFlag(ErrorUnrecoverable);
          }
        }
        else
        {
          parseError(in->record, "cannot access a non-record");
          setErrorFlag(ErrorUnrecoverable);
        }
      }
    } break;

    case Ast_Lambda:
    {
      Lambda   *in  = castAst(in0, Lambda);
      Term *type = goal;
      if (in->signature)
      {
        if (BuildTerm build = buildTerm(arena, env, in->signature, holev))
          type = build.term;
      }

      if (noError())
      {
        if (Arrow *signature = castTerm(type, Arrow))
        {
          Function *fun = newTerm(arena, Function, 0);
          fun->type = &signature->t;

          introduceSignature(env, signature, true);
          if (BuildTerm body = buildTerm(arena, env, in->body, signature->output_type))
            fun->body = body.term;
          unwindBindingsAndScope(env);
          if (noError())
            out0.term  = &fun->t;
        }
        else
        {
          parseError(in0, "lambda has to have an arrow type");
          attach("goal", goal);
        }
      }
    } break;

    case Ast_RewriteAst:
    {
      should_check_type = false;
      RewriteAst *in  = castAst(in0, RewriteAst);
      Term *new_goal = 0;
      if (BuildTerm eq_proof = buildTerm(arena, env, in->eq_proof, holev))
      {
        Term *proof_type = todoGetType(temp_arena, env, eq_proof.term);
        if (auto [lhs, rhs] = getEqualitySides(proof_type, false))
        {
          Term *from = in->right_to_left ? rhs : lhs;
          Term *to   = in->right_to_left ? lhs : rhs;
          SearchOutput search = searchExpression(arena, env, from, goal);
          if (search.found)
          {
            new_goal = rewriteTerm(arena, to, search.path, goal);
            if (BuildTerm body = buildTerm(arena, env, in->body, new_goal))
              out0.term = newRewrite(arena, eq_proof.term, body.term, search.path, in->right_to_left);
          }
          else
          {
            parseError(in0, "rewrite has no effect");
            attach("substitution", proof_type);
          }
        }
        else
        {
          parseError(in->eq_proof, "please provide a proof of equality for rewrite");
          attach("got", proof_type);
        }
      }
    } break;

    case Ast_GoalTransform:
    {
      GoalTransform *in = castAst(in0, GoalTransform);
      Term     *new_goal      = 0;
      Term     *eq_proof      = 0;
      TreePath *rewrite_path  = 0;
      b32       right_to_left = false;

      if (!in->new_goal)
      {// just normalize the goal, no need for tactics (for now).
        Term *norm_goal = normalize(arena, env, goal);
        if (checkFlag(in->flags, AstFlag_Generated) &&
            equal(goal, norm_goal))
        {// superfluous auto-generated transforms.
          recursed = true;
          out0 = buildTerm(arena, env, in->body, goal);
        }
        else
        {
          new_goal = norm_goal;
          eq_proof = newComputation(arena, env, goal, new_goal);
          rewrite_path = 0;
        }
      }
      else if ((new_goal = buildTerm(arena, env, in->new_goal, holev)))
      {
        CompareTerms compare = compareTerms(arena, goal, new_goal);
        if (compare.result == Trinary_True)
          parseError(in0, "new goal is exactly the same as current goal");
        else
        {
          rewrite_path = compare.diff_path;
          Term *from = subExpressionAtPath(goal, compare.diff_path);
          Term *to   = subExpressionAtPath(new_goal, compare.diff_path);

          b32 is_global_identifier = false;
          HintDatabase *hints = 0;
          if (in->hint)
          {
            if (Identifier *ident = castAst(in->hint, Identifier))
            {
              // NOTE: If the identifier is global, we treat it as an operator, if
              // it's local then treat it as the entire proof -> pretty janky.
              if (!lookupLocalName(env, &ident->token))
              {
                if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
                {
                  is_global_identifier = true;
                  for (i32 i=0; i < slot->count; i++)
                  {
                    hints = addHint(temp_arena, hints, slot->items[i]);
                  }
                }
                else
                {
                  parseError(&ident->a, "identifier not found");
                  attach("identifier", ident->token.string);
                }
              }
            }
          }

          if (!is_global_identifier)
          {
            if (in->hint)
            {
              if ((eq_proof = buildTerm(arena, env, in->hint, holev).term))
              {
                hints = addHint(temp_arena, hints, eq_proof);
              }
            }
          }

          Term *from_type = getType(from);
          Term *lr_eq = newEquality(temp_arena, from_type, from, to);
          Term *rl_eq = newEquality(temp_arena, from_type, to, from);

          Solver solver = Solver{.arena=arena, .env=env, .local_hints=hints, .use_global_hints=true};
          if (!(eq_proof = solveForGoal(&solver, lr_eq)))
          {
            if ((eq_proof = solveForGoal(&solver, rl_eq)))
            {
              right_to_left = true;
            }
            else
            {
              parseError(in0, "cannot solve for equality proof");
              attach("equality", lr_eq);
            }
          }
        }
      }

      if (noError() && !recursed)
      {
        if (Term *body = buildTerm(arena, env, in->body, new_goal))
        {
          out0.term = newRewrite(arena, eq_proof, body, rewrite_path, right_to_left);
        }
      }
    } break;

    case Ast_Let:
    {
      Let  *in = castAst(in0, Let);
      Term *type_hint = holev;
      if (in->type && in->type != LET_TYPE_NORMALIZE)
      {
        if (BuildTerm type = buildTerm(arena, env, in->type, holev))
          type_hint = type.term;
      }
      if (noError())
      {
        if (BuildTerm build_rhs = buildTerm(arena, env, in->rhs, type_hint))
        {
          Term *rhs = build_rhs.term;
          Term *rhs_type = type_hint;
          if (type_hint->cat == Term_Hole)
            rhs_type = todoGetType(arena, env, build_rhs.term);
            
          if (in->type == LET_TYPE_NORMALIZE)
          {// type coercion
            Term *norm_rhs_type = normalize(arena, env, rhs_type);
            Term *computation = newComputation(arena, env, norm_rhs_type, rhs_type);
            rhs_type = norm_rhs_type;
            rhs = newRewrite(arena, computation, build_rhs.term, 0, false);
            assert(equal(todoGetType(temp_arena, env, rhs), rhs_type));
          }

          Token *token = &in0->token;
          Lambda *lambda = newAst(temp_arena, Lambda, token);
          lambda->body = in->body;
          ArrowAst *signature = newAst(temp_arena, ArrowAst, token);
          i32 param_count = 1;
          allocateArray(temp_arena, param_count, signature->param_names);
          allocateArray(temp_arena, param_count, signature->param_types);
          allocateArray(temp_arena, param_count, signature->param_flags, true);
          signature->param_count    = param_count;
          signature->param_names[0] = in->lhs;

          Term *rhs_type_rebased = rebase(arena, rhs_type, 1);
          signature->param_types[0] = synthesizeAst(temp_arena, rhs_type_rebased, token);
          signature->output_type    = synthesizeAst(temp_arena, rebase(arena, goal, 1), token);
          lambda->signature = &signature->a;

          Ast *rhs_ast = synthesizeAst(arena, rhs, token);

          CompositeAst *com = newAst(arena, CompositeAst, token);
          allocateArray(temp_arena, param_count, com->args);
          com->op        = &lambda->a;
          com->arg_count = param_count;
          com->args[0]   = rhs_ast;

          recursed = true;
          out0 = buildTerm(arena, env, &com->a, goal);
        }
      }
    } break;

    case Ast_ForkAst:
    {// no need to return value since nobody uses the value of a fork
      ForkAst *fork = castAst(in0, ForkAst);
      out0.term = buildFork(arena, env, fork, goal);
      recursed = true;
    } break;

    case Ast_UnionAst:
    {
      UnionAst *uni = castAst(in0, UnionAst);
      out0.term = &buildUnion(arena, env, uni, 0)->t;
    } break;

    case Ast_CtorAst:
    {
      parseError(in0, "please use this constructor syntax as an operator");
    } break;

    case Ast_SeekAst:
    {
      SeekAst *in = castAst(in0, SeekAst);
      Term *proposition = goal;
      if (in->proposition)
        proposition = buildTerm(temp_arena, env, in->proposition, holev).term;

      if (noError())
      {
        i32 delta = 0;
        for (Scope *scope = env->scope; scope; scope=scope->outer)
        {
          Arrow *arrow = scope->first;
          for (i32 param_id=0; param_id < arrow->param_count; param_id++)
          {
            // todo #speed we're having to rebase everything, which sucks but
            // unless we store position-independent types, that's what we gotta do.
            Term *type = rebase(temp_arena, arrow->param_types[param_id], delta);
            if (equal(type, proposition))
            {
              Variable *var = newTerm(arena, Variable, 0);
              var->name  = arrow->param_names[param_id];
              var->delta = delta;
              var->id    = param_id;
              out0.term = &var->t;
            }
          }
          delta++;
        }
        if (!out0.term)
          parseError(in0, "cannot find a matching proof on the stack");
      }
    } break;

    case Ast_OverloadAst:
    {
      OverloadAst *in = castAst(in0, OverloadAst);
      if (GlobalBinding *lookup = lookupGlobalName(&in->function_name))
      {
        if (Term *distinguisher = buildTerm(temp_arena, env, in->distinguisher, holev).term)
        {
          for (i32 slot_i=0;
               slot_i < lookup->count && !out0.term;
               slot_i++)
          {
            Term *item = lookup->items[slot_i];
            if (Arrow *signature = castTerm(getType(item), Arrow))
            {
              b32 matches = false;
              if (distinguisher->cat == Term_Union)
                matches = equal(signature->param_types[0], distinguisher);
              else
                todoIncomplete;

              if (matches)
                out0.term = item;
            }
          }
        }
      }
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// typecheck if needed
    Term *actual = computeType(arena, env, out0.term);
    if (should_check_type && !recursed)
    {
      if (!matchType(actual, goal))
      {
        parseError(in0, "actual type differs from expected type");
        attach("got", actual);
      }
    }
  }

  if (ParseError *error = getError())
  {
    setErrorFlag(ErrorTypecheck);
    out0 = {};
    if (!checkErrorFlag(ErrorGoalAttached))
    {
      attach("goal", goal);

      StartString start = startString(error_buffer);
      print(error_buffer, "\n");
      print(error_buffer, env->scope);
      attach("scope", endString(start));

      start = startString(error_buffer);
      printDataMap(error_buffer, env);
      attach("data_map", endString(start));

      setErrorFlag(ErrorGoalAttached);
    }
  }
  else
  {
    assert(out0);
  }
  return out0;
}

forward_declare internal Term *
buildFork(MemoryArena *arena, Typer *env, ForkAst *in, Term *goal)
{
  if (goal->cat == Term_Hole)
  {
    parseError(&in->a, "fork expressions require a goal, please provide one (f.ex instead of writing \"a := b\", write \"a: A := b\")");
  }
  Fork *out = newTerm(arena, Fork, goal);
  out->case_count = in->case_count;
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  if (BuildTerm subject = buildTerm(arena, env, in->subject, holev))
  {
    out->subject = subject.term;
    i32 case_count = in->case_count;

    Term *subject_type = todoGetType(arena, env, subject.term);
    if (Union *uni = castTerm(subject_type, Union))
    {
      if (uni->ctor_count == case_count)
      {
        Term **ordered_bodies = pushArray(arena, case_count, Term *, true);

        for (i32 input_case_id = 0;
             input_case_id < case_count && noError();
             input_case_id++)
        {
          Token *ctor_name = in->ctors + input_case_id;

          i32 ctor_id = -1;
          for (i32 id = 0; id < uni->ctor_count; id++)
          {
            if (equal(uni->ctor_names[id], ctor_name->string))
            {
              ctor_id = id;
              break;
            }
          }

          if (ctor_id != -1)
          {
            if (getOrAddDataTree(temp_arena, env, subject.term, ctor_id).added)
            {
              if (ordered_bodies[ctor_id])
              {
                parseError(in->bodies[input_case_id], "fork case handled twice");
                attach("constructor", uni->ctor_names[ctor_id]);  // todo cleanup attach string
              }
              else
              {
                if (BuildTerm body = buildTerm(arena, env, in->bodies[input_case_id], goal))
                {
                  ordered_bodies[ctor_id] = body.term;
                }
              }
              undoDataMap(env);
            }
            else
            {
              parseError(in->subject, "cannot fork this term");
              attach("serial", serial);
            }
          }
          else
          {
            tokenError(ctor_name, "not a valid constructor");  // todo print them out
            attach("type", &uni->t);

            StartString ctor_names = startString(error_buffer);
            for (i32 id=0; id < uni->ctor_count; id++)
            {
              print(error_buffer, uni->ctor_names[id]);
              if (id != uni->ctor_count-1)
                print(error_buffer, ", ");
            }
            attach("valid constructors", endString(ctor_names));
          }
        }

        if (noError())
        {
          out->uni    = uni;
          out->bodies = ordered_bodies;
        }
      }
      else
        parseError(&in->a, "wrong number of cases, expected: %d, got: %d",
                   uni->ctor_count, in->case_count);
    }
    else
    {
      parseError(in->subject, "cannot fork expression of type");
      attach("type", subject_type);
    }
  }
  if (noError())
  {
    for (i32 id=0; id < in->case_count; id++)
      assert(in->bodies[id]);
  }
  NULL_WHEN_ERROR(out);
  return &out->t;
}

forward_declare inline Term *
newRewrite(MemoryArena *arena, Term *eq_proof, Term *body, TreePath *path, b32 right_to_left)
{
  auto [lhs, rhs] = getEqualitySides(getType(eq_proof));
  Term *rewrite_to = right_to_left ? rhs : lhs;
  Term *type = rewriteTerm(arena, rewrite_to, path, getType(body));

  Rewrite *out = newTerm(arena, Rewrite, type);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return &out->t;
}

inline BuildTerm
parseExpression(MemoryArena *arena, LocalBindings *bindings, Term *expected_type)
{
  BuildTerm out = {};
  if (Ast *ast = parseExpressionToAst(arena))
  {
    Typer env = {};
    env.bindings = bindings;
    out = buildTerm(arena, &env, ast, expected_type);
  }
  NULL_WHEN_ERROR(out);
  return out;
}

inline BuildTerm
parseExpressionFull(MemoryArena *arena)
{
  return parseExpression(arena, 0, holev);
}

struct NormList {
  i32          count;
  Identifier **items;
};

inline void
insertAutoNormalizations(MemoryArena *arena, NormList norm_list, Ast *in0)
{
  switch (in0->cat)
  {
    case Ast_ForkAst:
    {
      ForkAst *in = castAst(in0, ForkAst);
      for (i32 case_id=0; case_id < in->case_count; case_id++)
      {
        Ast *body = in->bodies[case_id];
        insertAutoNormalizations(arena, norm_list, body);
        for (i32 norm_id=0; norm_id < norm_list.count; norm_id++)
        {
          Identifier *item = norm_list.items[norm_id];
          // todo cleanup: we'll need to clean useless let-normalization too!
          Let *new_body = newAst(arena, Let, &item->token);
          new_body->lhs   = item->token.string;
          new_body->rhs   = &item->a;
          new_body->type  = LET_TYPE_NORMALIZE;
          new_body->body  = body;
          setFlag(&new_body->flags, AstFlag_Generated);
          body = &new_body->a;
        }
        GoalTransform *new_body = newAst(arena, GoalTransform, &body->token);
        setFlag(&new_body->flags, AstFlag_Generated);
        new_body->body = body;
        in->bodies[case_id] = &new_body->a;
      }
    } break;

    case Ast_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      assert(in->body);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    case Ast_Let:
    {
      Let *in = castAst(in0, Let);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    default:
    {} break;
  }
}

internal FunctionDecl *
parseGlobalFunction(MemoryArena *arena, Token *name, b32 is_theorem)
{
  FunctionDecl *out = newAst(arena, FunctionDecl, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpressionToAst(arena))
  {
    NormList norm_list = {};
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      while (true)
      {
        if (optionalCategory(Token_Directive_norm))
        {
          pushContext("auto normalization: #norm(IDENTIFIER...)");
          if (requireChar('('))
          {
            Tokenizer tk_copy = *global_tokenizer;
            i32 norm_count = getCommaSeparatedListLength(&tk_copy);
            if (noError(&tk_copy))
            {
              norm_list.items = pushArray(temp_arena, norm_count, Identifier*);
              for (; noError(); )
              {
                if (optionalChar(')'))
                  break;
                else if (requireIdentifier("expect auto-normalized parameter"))
                {
                  // todo handle unbound identifier: all names in the norm list
                  // should be in the function signature.
                  Token *name = &global_tokenizer->last_token;
                  i32 norm_id = norm_list.count++;
                  assert(norm_id < norm_count);
                  norm_list.items[norm_id] = newAst(arena, Identifier, name);
                  if (!optionalChar(','))
                  {
                    requireChar(')');
                    break;
                  }
                }
              }
            }
          }
          popContext();
        }
        else if (optionalCategory(Token_Directive_hint))
          out->add_to_global_hints = true;
        else
          break;
      }

      if (Ast *body = parseSequence(arena))
      {
        if (is_theorem)
          insertAutoNormalizations(arena, norm_list, body);
        out->body      = body;
        out->signature = signature;
      }
    }
    else
      parseError(signature0, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare internal Ast *
parseFork(MemoryArena *arena)
{
  ForkAst *out = 0;
  Token token = global_tokenizer->last_token;
  Ast *subject = parseExpressionToAst(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Tokenizer tk_copy = *global_tokenizer;
    i32 case_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      Token *ctors = pushArray(temp_arena, case_count, Token);
      Ast **bodies = pushArray(temp_arena, case_count, Ast*);

      i32 actual_case_count = 0;
      for (b32 stop = false;
           !stop && hasMore();)
      {
        if (optionalChar('}'))
          stop = true;
        else
        {
          pushContext("fork case: CASE: BODY");
          i32 input_case_id = actual_case_count++;
          Token ctor = nextToken();
          if (isIdentifier(&ctor))
            ctors[input_case_id] = ctor;
          else
            tokenError(&ctor, "expected a constructor name");

          optionalChar(':');  // just decoration
          if (Ast *body = parseSequence(arena, false))
          {
            bodies[input_case_id] = body;
            if (!optionalChar(','))
            {
              requireChar('}', "to end fork expression; or use ',' to end the fork case");
              stop = true;
            }
          }
          popContext();
        }
      }

      if (noError())
      {
        assert(case_count == actual_case_count);
        out = newAst(arena, ForkAst, &token);
        out->a.token    = token;
        out->subject    = subject;
        out->case_count = case_count;
        out->bodies     = bodies;
        out->ctors      = ctors;
      }
    }
  }

  return &out->a;
}

internal ArrowAst *
parseArrowType(MemoryArena *arena, b32 is_struct)
{
  ArrowAst *out = 0;

  i32      param_count;
  String  *param_names;
  Ast    **param_types;
  u32     *param_flags;
  Token marking_token = peekToken();
  char begin_arg_char = '(';
  char end_arg_char   = ')';
  if (requireChar(begin_arg_char))
  {
    Tokenizer tk_copy = *global_tokenizer;
    param_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      allocateArray(arena, param_count, param_names, true);
      allocateArray(arena, param_count, param_types, true);
      allocateArray(arena, param_count, param_flags, true);

      i32 parsed_param_count = 0;
      i32 typeless_run = 0;
      Token typeless_token;
      for (b32 stop = false;
           !stop && hasMore();
           )
      {
        if (optionalChar(end_arg_char))
          stop = true;
        else
        {
          i32 param_id = parsed_param_count++;
          if (optionalCategory(Token_Directive_hidden))
          {
            setFlag(&param_flags[param_id], ParameterFlag_Hidden);
          }

          Tokenizer tk_save = *global_tokenizer;
          String param_name = {};
          Token maybe_param_name_token = nextToken();
          if (isIdentifier(&maybe_param_name_token))
          {
            Token after_name = peekToken();
            if (equal(&after_name, ':'))
            {
              eatToken();
              param_name = maybe_param_name_token.string;
              pushContext("parameter type");
              if (Ast *param_type = parseExpressionToAst(arena))
              {
                param_types[param_id] = param_type;
                if (typeless_run)
                {
                  for (i32 offset = 1; offset <= typeless_run; offset++)
                    param_types[param_id - offset] = param_type;
                  typeless_run = 0;
                }
              }
              popContext();
            }
            else if (equal(&after_name, ','))
            {
              param_name = maybe_param_name_token.string;
              typeless_run++;
              typeless_token = maybe_param_name_token;
            }
          }

          if (param_name.chars)
            param_names[param_id] = param_name;
          else
          {
            *global_tokenizer = tk_save;
            pushContext("anonymous parameter");
            Token anonymous_parameter_token = global_tokenizer->last_token;
            if (Ast *param_type = parseExpressionToAst(arena))
            {
              param_types[param_id] = param_type;
              if (typeless_run)
                tokenError(&anonymous_parameter_token, "cannot follow a typeless parameter with an anonymous parameter");
            }
            popContext();
          }

          if (hasMore())
          {
            Token delimiter = nextToken();
            if (equal(&delimiter, end_arg_char))
              stop = true;
            else if (!equal(&delimiter, ','))
              tokenError("unexpected token");
          }
        }
      }

      if (noError())
      {
        assert(parsed_param_count == param_count);
        if (typeless_run)
        {
          tokenError(&typeless_token, "please provide types for all parameters");
        }
      }
    }
  }

  if (noError())
  {
    out = newAst(arena, ArrowAst, &marking_token);
    out->param_count = param_count;
    out->param_names = param_names;
    out->param_types = param_types;
    out->param_flags = param_flags;
    if (!is_struct)  // structs don't need return type
    {
      if (requireCategory(Token_Arrow, "syntax: (param: type, ...) -> ReturnType"))
      {
        if (Ast *return_type = parseExpressionToAst(arena))
          out->output_type = return_type;
      }
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

inline b32
areSequential(Token *first, Token *next)
{
  return next->string.chars == first->string.chars + first->string.length;
}

internal void
parseConstructor(MemoryArena *arena, UnionAst *uni, i32 ctor_id)
{
  Token ctor_name = nextToken();
  uni->ctor_names[ctor_id] = ctor_name;

  if (isIdentifier(&ctor_name))
  {
    Token maybe_paren = peekToken();
    if (equal(maybe_paren.string, "("))
    {// subtype
      pushContext("constructor(FIELD: TYPE ...)");
      {
        if (ArrowAst *arrow_ast = parseArrowType(arena, true))
          uni->ctor_signatures[ctor_id] = arrow_ast;
      }
      popContext();
    }
    else
    {// atomic constructor
      ArrowAst *signature = newAst(arena, ArrowAst, &ctor_name);
      uni->ctor_signatures[ctor_id] = signature;  // empty arrow: no parameter, no output.
    }
  }
  else
    tokenError("expected an identifier as constructor name");
}

internal UnionAst *
parseUnion(MemoryArena *arena)
{
  UnionAst *uni = 0;
  Token *token = &global_tokenizer->last_token;

  if (requireChar('{'))
  {
    uni = newAst(arena, UnionAst, token);

    Tokenizer tk_copy = *global_tokenizer;
    i32 ctor_count = getCommaSeparatedListLength(&tk_copy);
    // NOTE: init here for recursive definition
    if (noError(&tk_copy))
    {
      allocateArray(arena, ctor_count, uni->ctor_signatures);
      allocateArray(arena, ctor_count, uni->ctor_names);
      while (noError())
      {
        if (optionalChar('}'))
          break;
        else
        {
          parseConstructor(arena, uni, uni->ctor_count++);
          if (!optionalChar(','))
          {
            requireChar('}');
            break;
          }
        }
      }

      if (noError())
        assert(uni->ctor_count == ctor_count);
    }
  }
  
  return uni;
}

forward_declare internal Union *
buildUnion(MemoryArena *arena, Typer *env, UnionAst *in, Token *global_name)
{
  Union *uni = newTerm(arena, Union, &builtins.Set->t);
  uni->ctor_count = in->ctor_count;
  allocateArray(arena, in->ctor_count, uni->ctor_names);
  allocateArray(arena, in->ctor_count, uni->structs);
  // note: bind the type first to support recursive data structure.
  if (global_name)
    addGlobalBinding(global_name, &uni->t);
  Constructor **constructors = pushArray(temp_arena, in->ctor_count, Constructor *);
  for (i32 ctor_id=0; noError() && (ctor_id < in->ctor_count); ctor_id++)
  {
    Constructor *ctor = newTerm(arena, Constructor, 0);
    ctor->uni = uni;
    ctor->id  = ctor_id;
    constructors[ctor_id] = ctor;

    Token *ctor_name = in->ctor_names + ctor_id;
    uni->ctor_names[ctor_id] = ctor_name->string;
    if (BuildTerm build_type = buildTerm(arena, env, &in->ctor_signatures[ctor_id]->a, holev))
    {
      Arrow *signature = castTerm(build_type.term, Arrow);
      uni->structs[ctor_id] = signature;
      ctor->type                    = &signature->t;

      if (global_name)
      {
        if (signature->param_count > 0)
        {
          addGlobalBinding(ctor_name, &ctor->t);
        }
        else
        {
          Composite *record = newTerm(arena, Composite, 0);
          record->op = &ctor->t;
          addGlobalBinding(ctor_name, &record->t);
        }
      }
    }
  }

  NULL_WHEN_ERROR(uni);
  return uni;
}

inline CtorAst *
parseCtor(MemoryArena *arena)
{
  CtorAst *out = newAst(arena, CtorAst, &global_tokenizer->last_token);
  if (requireChar('['))
  {
    out->ctor_id = parseInt32();
    requireChar(']');
  }
  return out;
}

inline SeekAst *
parseSeek(MemoryArena *arena)
{
  SeekAst *seek = newAst(arena, SeekAst, &global_tokenizer->last_token);
  if (!seesExpressionEndMarker())
  {
    seek->proposition = parseExpressionToAst(arena);
  }
  return seek;
}

inline Ast *
parseOverload(MemoryArena *arena)
{
  OverloadAst *out = newAst(arena, OverloadAst, lastToken());
  if (requireChar('('))
  {
    if (requireIdentifier("require a function name"))
    {
      out->function_name = *lastToken();
      if (requireChar(','))
      {
        out->distinguisher = parseExpressionToAst(arena);
      }
    }
    requireChar(')');
  }
  if (hasError()) out = 0;
  return &out->a;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  Ast *operand = 0;
  Token token = nextToken();
  if (equal(&token, '_'))
  {
    operand = newAst(arena, Hole, &token);
  }
  else
  {
    switch (token.cat)
    {
      case '(':
      {
        operand = parseExpressionToAst(arena);
        requireChar(')');
      } break;

      case Token_Keyword_seq:
      {
        operand = parseSequence(arena);
      } break;

      case Token_Alphanumeric:
      case Token_Special:
      {
        operand = &newAst(arena, Identifier, &token)->a;
      } break;

      case Token_Keyword_union:
      {
        operand = &parseUnion(arena)->a;
      } break;

      case Token_Keyword_ctor:
      {
        operand = &parseCtor(arena)->a;
      } break;

      case Token_Keyword_seek:
      {
        operand = &parseSeek(arena)->a;
      } break;

      case Token_Keyword_auto:
      {
        operand = newAst(arena, Auto, &token);
      } break;

      case Token_Keyword_overload:
      {
        operand = parseOverload(arena);
      } break;

      default:
      {
        tokenError("expected start of expression");
      }
    }
  }

  while (hasMore())
  {
    if (optionalChar('('))
    {// function call syntax, let's keep going
      Ast *op = operand;

      Tokenizer tk_copy = *global_tokenizer;
      i32 expected_arg_count = getCommaSeparatedListLength(&tk_copy);
      if (noError(&tk_copy))
      {
        Ast **args = pushArray(arena, expected_arg_count, Ast*);
        CompositeAst *branch = newAst(arena, CompositeAst, &op->token);
        branch->op        = op;
        branch->arg_count = expected_arg_count;
        branch->args      = args;
        operand = &branch->a;
        i32 parsed_arg_count = 0;
        while (hasMore())
        {
          if (optionalChar(')'))
            break;
          else
          {
            i32 arg_id = parsed_arg_count++;
            if (optionalCategory(Token_Ellipsis))
            {
              if (arg_id == 0)
                args[0] = newAst(arena, Ellipsis, &global_tokenizer->last_token);
              else
                parseError("ellipsis must be the only argument");

              requireChar(')', "ellipsis must be the only argument");
              break;
            }
            else
            {
              if ((args[arg_id] = parseExpressionToAst(arena)))
              {
                if (!optionalChar(','))
                {
                  requireChar(')', "expected ',' or ')'");
                  break;
                }
              }
            }
          }
        }
        if (noError())
        {
          assert(parsed_arg_count == expected_arg_count);
        }
      }
    }
    else if (optionalChar('.'))
    {// member accessor
      AccessorAst *accessor = newAst(arena, AccessorAst, &global_tokenizer->last_token);
      accessor->record      = operand;
      if (requireIdentifier("expected identifier as field name"))
      {
        accessor->field_name = global_tokenizer->last_token;
        operand              = &accessor->a;
      }
    }
    else break;
  }
  NULL_WHEN_ERROR(operand);
  return operand;
}

inline b32
seesArrowExpression()
{
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (requireChar('(', "", tk))
    if (eatUntilMatchingPair(tk))
      out = nextToken(tk).cat == Token_Arrow;
  return out;
}

inline b32 seesLambda()
{// todo we don't allow naming parameters in here yet
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (requireChar('_', 0, tk))
  {
    if (requireCategory(Token_StrongArrow, 0, tk))
      out = true;
  }
  return out;
}

internal Lambda *
parseLambda(MemoryArena *arena)
{
  pushContext("lambda: _ => {SEQUENCE}");
  nextToken(); nextToken();
  Lambda *out = newAst(arena, Lambda, &global_tokenizer->last_token);
  out->body = parseSequence(arena);
  popContext();
  return out;
}

internal Ast *
parseExpressionToAstMain(MemoryArena *arena, ParseExpressionOptions opt)
{
  Ast *out = 0;
  if (seesArrowExpression())
    out = &parseArrowType(arena, false)->a;
  else if (seesLambda())
    out = &parseLambda(arena)->a;
  else
  {
    if (Ast *operand = parseOperand(arena))
    {
      // (a+b) * c
      //     ^
      for (b32 stop = false; !stop && hasMore();)
      {
        Token op_token = peekToken();
        if (isIdentifier(&op_token))
        {// infix operator syntax
          // (a+b) * c
          //        ^
          Identifier *op = newAst(arena, Identifier, &op_token);
          i32 precedence = precedenceOf(op_token.string);
          if (precedence >= opt.min_precedence)
          {
            // recurse
            nextToken();
            // a + b * c
            //      ^
            ParseExpressionOptions opt1 = opt;
            opt1.min_precedence = precedence;
            if (Ast *recurse = parseExpressionToAstMain(arena, opt1))
            {
              i32 arg_count = 2;
              Ast **args    = pushArray(arena, arg_count, Ast*);
              args[0] = operand;
              args[1] = recurse;

              CompositeAst *new_operand = newAst(arena, CompositeAst, &op_token);
              new_operand->op        = &op->a;
              new_operand->arg_count = arg_count;
              new_operand->args      = args;
              operand = &new_operand->a;
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
        else if (isExpressionEndMarker(&op_token))
          stop = true;
        else
          tokenError(&op_token, "expected operator token");
      }
      if (noError())
        out = operand;
    }
  }

  NULL_WHEN_ERROR(out);
  return out;
}

forward_declare inline Ast *
parseExpressionToAst(MemoryArena *arena)
{
  return parseExpressionToAstMain(arena, ParseExpressionOptions{});
}

inline void
addGlobalHint(Function *fun)
{
  HintDatabase *new_hint = pushStruct(global_state.top_level_arena, HintDatabase);
  new_hint->first = &fun->t;
  new_hint->next  = global_state.hints;
  global_state.hints = new_hint;
}

internal Function *
buildGlobalFunction(MemoryArena *arena, FunctionDecl *in)
{
  pushContext(in->token.string, true);
  Function *out = 0;
  Typer typer_ = {};
  auto  typer  = &typer_;

  if (BuildTerm build_signature = buildTerm(arena, typer, &in->signature->a, holev))
  {
    Arrow *signature = castTerm(build_signature.term, Arrow);
    out = newTerm(arena, Function, build_signature.term);
    out->body = &dummy_function_being_built;

    // NOTE: add binding first to support recursion
    addGlobalBinding(&in->a.token, &out->t);

    if (noError())
    {
      introduceSignature(typer, signature, true);
      if (BuildTerm body = buildTerm(arena, typer, in->body, signature->output_type))
      {
        out->body = body.term;
        if (in->add_to_global_hints)
          addGlobalHint(out);
      }
      unwindBindingsAndScope(typer);
    }
  }

  popContext();
  return out;
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  MemoryArena *arena = state->top_level_arena;
  b32 should_fail_active = false;

  Token token = nextToken(); 
  while (hasMore())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
    error_buffer_ = subArena(temp_arena, 1024);
#endif

    Typer  empty_env_ = {};
    Typer *empty_env  = &empty_env_;

    switch (token.cat)
    {
      case Token_Directive_load:
      {
        pushContext("load");
        Token file = nextToken();
        if (file.cat != Token_StringLiteral)
          tokenError("expect \"FILENAME\"");
        else
        {
          String load_path = print(arena, global_tokenizer->directory);
          load_path.length += print(arena, file.string).length;
          arena->used++;

          // note: this could be made more efficient but we don't care.
          FilePath full_path = platformGetFileFullPath(arena, load_path.chars);

          b32 already_loaded = false;
          for (auto file_list = state->file_list;
               file_list && !already_loaded;
               file_list = file_list->next)
          {
            if (equal(file_list->first_path, load_path))
              already_loaded = true;
          }

          if (!already_loaded)
          {
            auto interp_result = interpretFile(state, full_path, false);
            if (!interp_result)
              tokenError("failed loading file");
          }
        }
        popContext();
      } break;

      case Token_Directive_should_fail:
      {
        if (optionalString("off"))
          should_fail_active = false;
        else
        {
          should_fail_active = true;
          tokenError(&token, "#should_fail activated");
          setErrorFlag(ErrorTypecheck);
        }
      } break;

      case Token_Directive_debug:
      {
        if (optionalString("off"))
        {
          DEBUG_OFF;
        }
        else
        {
          DEBUG_ON;
        }
      } break;

      case Token_Keyword_test_eval:
      {
        if (BuildTerm expr = parseExpressionFull(temp_arena))
          normalize(arena, empty_env, expr.term);
      } break;

      case Token_Keyword_print:
      {
        u32 flags = PrintFlag_Detailed|PrintFlag_PrintType;
        if (optionalString("lock_detailed"))
          setFlag(&flags, PrintFlag_LockDetailed);
        if (BuildTerm expr = parseExpressionFull(temp_arena))
        {
          Term *norm = normalize(arena, 0, expr.term);
          print(0, norm, {.flags=flags});
          print(0, "\n");
        }
      } break;

      case Token_Keyword_print_raw:
      {
        if (auto parsing = parseExpressionFull(temp_arena))
          print(0, parsing.term, {.flags = (PrintFlag_Detailed     |
                                            PrintFlag_LockDetailed |
                                            PrintFlag_PrintType)});
        print(0, "\n");
      } break;

      case Token_Keyword_print_ast:
      {
        if (Ast *exp = parseExpressionToAst(temp_arena))
          print(0, exp, {.flags = PrintFlag_Detailed});
        print(0, "\n");
      } break;

      case Token_Keyword_check:
      {
        pushContext("check TERM: TYPE");
        Term *expected_type = holev;
        if (Ast *ast = parseExpressionToAst(temp_arena))
        {
          if (optionalChar(':'))
          {
            if (BuildTerm type = parseExpressionFull(temp_arena))
              expected_type = type.term;
          }
          if (noError())
            buildTerm(temp_arena, empty_env, ast, expected_type);
        }
        popContext();
      } break;

      case Token_Keyword_check_truth:
      {
        pushContext("check_truth EQUALITY");
        if (Term *goal = parseExpressionFull(temp_arena).term)
        {
          if (Composite *eq = castTerm(goal, Composite))
          {
            b32 goal_valid = false;
            if (eq->op == &builtins.equal->t)
            {
              goal_valid = true;
              Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
              Term *rhs = normalize(temp_arena, empty_env, eq->args[2]);
              if (!equal(lhs, rhs))
              {
                tokenError(&token, "equality cannot be proven by computation");
                Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
                attach("lhs", lhs);
                attach("rhs", rhs);
              }
            }
            if (!goal_valid)
            {
              tokenError(&token, "computation can only prove equality");
              attach("got", goal);
            }
          }
        }
        popContext();
      } break;

      default:
      {
        if (isIdentifier(&token))
        {
          Token after_name = nextToken();
          if (isIdentifier(&after_name) &&
              areSequential(&token, &after_name))
          {// token combination
            token.string.length += after_name.string.length;
            after_name = nextToken();
          }

          switch (after_name.cat)
          {
            case Token_ColonEqual:
            {
              pushContext("constant definition: CONSTANT := VALUE;");
              if (BuildTerm rhs = parseExpressionFull(arena))
              {
                addGlobalBinding(&token, rhs.term);
                requireChar(';');
              }
              popContext();
            } break;

            case Token_DoubleColon:
            {
              Token after_dcolon = peekToken();
              if (after_dcolon.cat == Token_Keyword_union)
              {
                nextToken();
                if (UnionAst *ast = parseUnion(arena))
                  buildUnion(arena, empty_env, ast, &token);
              }
              else
              {
                b32 is_theorem;
                if (after_dcolon.cat == Token_Keyword_fn)
                {
                  is_theorem = false;
                  nextToken();
                }
                else is_theorem = true;
                if (FunctionDecl *fun = parseGlobalFunction(arena, &token, is_theorem))
                  buildGlobalFunction(arena, fun);
              }
            } break;

            case ':':
            {
              if (BuildTerm type = parseExpressionFull(arena))
              {
                if (requireCategory(Token_ColonEqual, "require :=, syntax: name : type := value"))
                {
                  if (BuildTerm rhs = parseExpression(arena, 0, type.term))
                    addGlobalBinding(&token, rhs.term);
                }
              }
            } break;

            default:
            {
              tokenError("unexpected token after identifier");
            } break;
          }
        }
        else tokenError("unexpected token to begin top-level form");
      } break;
    }

#if CLEAN_TEMPORARY_MEMORY
    endTemporaryMemory(top_level_temp);
#endif

    if (should_fail_active)
    {
      if (noError())
        tokenError(&token, "#should_fail active but didn't fail");
      else if (checkErrorFlag(ErrorTypecheck))
        wipeError();
    }

    if (hasMore())
    {
      token = nextToken();
      while (equal(token.string, ";"))
      {// todo: should we do "eat all semicolons after the first one?"
        token = nextToken();
      }
    }
  }
}

forward_declare internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  MemoryArena *arena = state->top_level_arena;
  b32 success = true;
#define REA_PROFILE 0
#if REA_PROFILE
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

    Tokenizer  tk_ = newTokenizer(input_path.directory, read.content);
    Tokenizer *tk  = &tk_;

    Tokenizer *old_tokenizer = global_tokenizer;
    global_tokenizer         = tk;

    if (is_root_file)
    {
      printf("> Interpreting file: %s\n", input_path.file);
    }
    parseTopLevel(state);
    if (ParseError *error = tk->error)
    {
      success = false;
      printf("%s:%d:%d: ", input_path.path, error->line, error->column);
      if (error->context)
      {
        print(0, "[");
        for (ParseContext *context = error->context;
             context;
             context=context->next)
        {
          if (context->is_important || !context->next)
          {
            print(0, context->first);
            if (context->next)
              print(0, " / ");
          }
        }
        print(0, "] ");
      }
      print(0, error->message);

      if (error->attachment_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attachment_count;
             attached_id++)
        {
          auto attachment = error->attachments[attached_id];
          print(0, "%s: ", attachment.key);
          print(0, attachment.value);
          if (attached_id != error->attachment_count-1) 
            printf("\n");
        }
      }
      printf("\n");
    }

    if (is_root_file)
    {
#if REA_PROFILE
      auto compile_time = platformGetSecondsElapsed(begin_time, platformGetWallClock(arena));
      printf("Compile time for file %s: %fs\n", input_path.file, compile_time);
#endif
      for (i32 i=0; i < 80; i++) printf("-");
      printf("\n");
    }

    global_tokenizer = old_tokenizer;
  }
  else
  {
    if (is_root_file)
      printf("Failed to read input file %s\n", input_path.file);
    success = false;
  }

  if (is_root_file)
    checkArena(temp_arena);

  fflush(stdout);
  return success;
}

internal b32
beginInterpreterSession(MemoryArena *arena, char *initial_file)
{
  DEBUG_OFF;
  // :global_state_cleared_at_startup Clear global state as we might run the
  // interpreter multiple times.
  global_state       = {};
  global_state.top_level_arena = arena;

  {
    global_state.bindings = pushStruct(arena, GlobalBindings);  // :global-bindings-zero-at-startup

    builtins = {};
    {// Type and Set
      // Token superset_name = newToken("Type");
      builtins.Type = newTerm(arena, Builtin, 0);
      builtins.Type->type = &builtins.Type->t; // NOTE: circular types
      addBuiltinGlobalBinding("Type", &builtins.Type->t);

      builtins.Set = newTerm(arena, Builtin, &builtins.Type->t);
      addBuiltinGlobalBinding("Set", &builtins.Set->t);
    }

    {// more builtins
      Tokenizer builtin_tk = newTokenizer(toString("<builtin>"), 0);
      global_tokenizer = &builtin_tk;
      builtin_tk.at = "(#hidden A: Set, a,b: A) -> Set";
      BuildTerm equal_type = parseExpressionFull(arena); 
      assert(noError());
      builtins.equal = newTerm(arena, Builtin, equal_type.term);
      addBuiltinGlobalBinding("=", &builtins.equal->t);

      EngineState builtin_engine_state = EngineState{.top_level_arena=arena};
      builtin_tk.at = "True :: union { truth }";
      parseTopLevel(&builtin_engine_state);
      assert(noError());
      builtins.True  = castTerm(lookupBuiltinGlobalName("True"), Union);
      builtins.truth = castTerm(lookupBuiltinGlobalName("truth"), Constructor);
      builtin_tk.at = "False :: union { }";
      parseTopLevel(&builtin_engine_state);
      builtins.False = castTerm(lookupBuiltinGlobalName("False"), Union);
    }
    resetArena(temp_arena);
  }

  FilePath input_path = platformGetFileFullPath(arena, initial_file);
  b32 success = interpretFile(&global_state, input_path, true);

  for (FileList *file_list = global_state.file_list;
       file_list;
       file_list = file_list->next)
  {
    platformFreeFileMemory(file_list->first_content);
  }
    
  checkArena(arena);
  return success;
}

int engineMain()
{
  int success = true;

#if 0
  // for printf debugging: when it crashes you can still see the prints
  setvbuf(stdout, NULL, _IONBF, 0);
#endif

  assert(arrayCount(keywords)       == Token_Keyword_END - Token_Keyword_START);
  assert(arrayCount(metaDirectives) == Token_Directive_END - Token_Directive_START);

  void   *permanent_memory_base = (void*)teraBytes(2);
  size_t  permanent_memory_size = megaBytes(256);
  permanent_memory_base = platformVirtualAlloc(permanent_memory_base, permanent_memory_size);
  MemoryArena permanent_arena_ = newArena(permanent_memory_size, permanent_memory_base);
  MemoryArena *permanent_arena = &permanent_arena_;

  void   *temp_memory_base = (void*)teraBytes(3);
  size_t  temp_memory_size = megaBytes(2);
  temp_memory_base = platformVirtualAlloc(temp_memory_base, permanent_memory_size);
  temp_arena_ = newArena(temp_memory_size, temp_memory_base);

  char *files[] = {
    // "../data/z-normalize-experiment.rea",
    // "../data/natp-experiment.rea",
    "../data/z-slider-experiment.rea",
    "../data/z.rea",
    "../data/test.rea",
  };
  for (i32 file_id=0; file_id < arrayCount(files); file_id++)
  {
    if (!beginInterpreterSession(permanent_arena, files[file_id]))
      success = false;
    resetArena(permanent_arena, true);
  }
  return success;
}

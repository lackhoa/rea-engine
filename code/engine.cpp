/*
  General Todos: 
  - #cleanup Replace all token <-> string comparison with keyword checks.
  - #tool something that cleans up when it goes out of scope
  - #speed evaluating functions by substituting the body is really bad in case of "let"
  - make "computation" be a builtin
  - debug serial situation
  - clean up the data tree containing constructors
  - we're printing terms every time we encounter an error, but the error might be recoverable so it's just wasted work. Either pass the intention down, or abandon the recoveriy route.
  - #speed Clean up the "pointer everywhere" approach
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"
#include "tokenization.cpp"
#include "debug_config.h"

global_variable Term *builtin_Type;
global_variable Term *builtin_Set;
global_variable Term *builtin_equal;
global_variable Term *builtin_type_equal;
global_variable Term *builtin_False;
global_variable Term *builtin_eqChain;

global_variable Term dummy_function_being_built;
global_variable Term  holev_ = {.cat = Term_Hole};
global_variable Term *holev = &holev_;

global_variable EngineState global_state;

#define DEBUG_ON  {DEBUG_MODE = true; setvbuf(stdout, NULL, _IONBF, 0);}
#define DEBUG_OFF {DEBUG_MODE = false; setvbuf(stdout, NULL, _IONBF, BUFSIZ);}

inline void
attach(char *key, String value, Tokenizer *tk=global_tokenizer)
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

inline void
attach(char *key, Ast *ast, Tokenizer *tk=global_tokenizer)
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

inline void
attach(char *key, i32 n, Tokenizer *tk=global_tokenizer)
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
newVariable(MemoryArena *arena, Typer *typer, i32 id, i32 delta)
{
  Scope *scope = typer->scope;
  for (i32 id=0; id < delta; id++)
    scope=scope->outer;
  assert(scope->depth == typer->scope->depth - delta);
  Term *type = scope->head->param_types[id];
  type = rebase(arena, type, delta);

  Variable *var = newTerm(arena, Variable, type);
  var->name  = scope->head->param_names[id];
  var->index    = id;
  var->delta = delta;

  return &var->t;
}

inline Arrow *
getParameterTypes(Term *op)
{
  Arrow *out = 0;
  if (Constructor *ctor = castTerm(op, Constructor))
    out = ctor->uni->structs[ctor->index];
  else
    out = castTerm(getType(op), Arrow);
  return out;
}

inline Term *
getOutputType(MemoryArena *arena, Term *op, Term **args)
{
  Term *out = 0;
  if (Constructor *ctor = castTerm(op, Constructor))
    out = &ctor->uni->t;
  else
    out = evaluate(arena, args, castTerm(getType(op), Arrow)->output_type);
  return out;
}

inline Term *
newComposite(MemoryArena *arena, Term *op, i32 arg_count, Term **args)
{
  Term *type = getOutputType(arena, op, args);
  Arrow *signature = getParameterTypes(op);

  assert(signature->param_count == arg_count);
  for (i32 i=0; i < arg_count; i++)
  {
    Term *actual_type   = getType(args[i]);
    Term *expected_type = evaluate(arena, args, signature->param_types[i]);
    assert(equal(actual_type, expected_type));
  }

  Composite *out = newTerm(arena, Composite, type);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;

  return &out->t;
}

inline Term *
newComposite1(MemoryArena *arena, Term *op, Term *arg0)
{
  Term **args = pushArray(arena, 1, Term*);
  args[0] = arg0;
  return newComposite(arena, op, 1, args);
}

inline Term *
newComposite2(MemoryArena *arena, Term *op, Term *arg0, Term *arg1)
{
  Term **args = pushArray(arena, 2, Term*);
  args[0] = arg0;
  args[1] = arg1;
  return newComposite(arena, op, 2, args);
}

inline Term *
newComposite3(MemoryArena *arena, Term *op, Term *arg0, Term *arg1, Term *arg2)
{
  Term **args = pushArray(arena, 3, Term*);
  args[0] = arg0;
  args[1] = arg1;
  args[2] = arg2;
  return newComposite(arena, op, 3, args);
}

inline Term *
newCompositeN(MemoryArena *arena, Term *op, i32 arg_count, ...)
{
  va_list arg_list;
  Term **args = pushArray(arena, arg_count, Term*);
  __crt_va_start(arg_list, arg_count);
  for (i32 i = 0; i < arg_count; i++)
  {
    args[i] = __crt_va_arg(arg_list, Term*);
  }
  __crt_va_end(arg_list);
  return newComposite(arena, op, arg_count, args);
}

inline Term *
newEquality(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Term *type_of_type = getType(getType(lhs));
  Term *op = (type_of_type == builtin_Set) ? builtin_equal : builtin_type_equal;
  return newComposite3(arena, op, getType(lhs), lhs, rhs);
}

inline Term *
newIdentity(MemoryArena *arena, Term *term)
{
  Term *eq = newEquality(arena, term, term);
  Computation *out = newTerm(arena, Computation, eq);
  return out;
}

inline b32
isEquality(Term *eq0)
{
  if (Composite *eq = castTerm(eq0, Composite))
  {
    if (eq->op == builtin_equal)
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
    if (eq->op == builtin_equal || eq->op == builtin_type_equal)
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

inline Term *
newConstructor(MemoryArena *arena, Union *uni, i32 index)
{
  // Yes, you don't want type in the constructor (see note #why_constructors_dont_have_types)
  Constructor *ctor = newTerm(arena, Constructor, 0);
  ctor->uni   = uni;
  ctor->index = index;
  return &ctor->t;
}

inline Stack *
newStack(MemoryArena *arena, Stack *outer, i32 count)
{
  Stack *stack = pushStruct(arena, Stack);
  stack->outer = outer;
  stack->count = count;
  allocateArray(arena, count, stack->items, true);
  return stack;
}

// todo hack hack hack
inline Term *
replaceUnionParameters(MemoryArena *arena, Term **args, Term *in0, i32 offset)
{
  Term *out0 = in0;
  if (!in0->global_name)
  {
    switch (in0->cat)
    {
      case Term_Variable:
      {
        Variable *in = castTerm(in0, Variable);
        if (in->delta == offset+1)
          out0 = args[in->index];
      } break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        if (in->punion)
        {
          Union *out = copyStruct(arena, in);
          out->punion_args = args;
          out0 = &out->t;
        }
        else
          todoIncomplete;
      } break;

      default:
        todoIncomplete;
    }
  }
  return out0;
}

inline Term **
synthesizeMembers(MemoryArena *arena, Term *parent, i32 ctor_id)
{
  Union *uni = castTerm(parent->type, Union);
  Arrow *struc = uni->structs[ctor_id];
  i32 param_count = struc->param_count;
  Term **members = pushArray(temp_arena, param_count, Term *);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = struc->param_names[field_id];
    Term *type = struc->param_types[field_id];
    if (uni->punion)
    {
      // :replaceUnionParameters_is_called_beforehand
      type = replaceUnionParameters(arena, uni->punion_args, type, 0);
    }
    type = evaluate(arena, members, type);
    Accessor *accessor = newTerm(arena, Accessor, type);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    members[field_id] = &accessor->t;
  }
  return members;
}

inline Term *
synthesizeTree(MemoryArena *arena, Term *parent, DataTree *tree)
{
  Composite *record = 0;
  Union *uni   = castTerm(parent->type, Union);
  Arrow *struc = uni->structs[tree->ctor_i];
  Term *ctor = newConstructor(arena, uni, tree->ctor_i);
  i32 param_count = struc->param_count;
  record = newTerm(arena, Composite, parent->type);
  record->op        = ctor;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term *);
  Term **members = synthesizeMembers(arena, parent, tree->ctor_i);
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
      out = scope->head->param_names[map->index];
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
    print(buffer, tree->ctor_names[tree->ctor_i]);
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
  for (DataMap *map = env->map; map; map=map->tail)
  {
    String var = getVarNameInScope(env, map);
    print(buffer, var);
    print(buffer, ": ");
    print(buffer, &map->tree);
    if (map->tail)
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
rewriteTerm(MemoryArena *arena, Term *from, Term *to, TreePath *path, Term *in0)
{
  Term *out0 = 0;
  if (path)
  {
    Composite *in  = castTerm(in0, Composite);
    Composite *out = copyStruct(arena, in);
    if (path->head == -1)
      out->op = rewriteTerm(arena, from, to, path->tail, in->op);
    else
    {
      assert((path->head >= 0) && (path->head < out->arg_count));
      allocateArray(arena, out->arg_count, out->args);
      for (i32 arg_id=0; arg_id < out->arg_count; arg_id++)
      {
        if (arg_id == (i32)path->head)
          out->args[arg_id] = rewriteTerm(arena, from, to, path->tail, in->args[arg_id]);
        else
          out->args[arg_id] = in->args[arg_id];
      }
    }
    out0 = &out->t;
  }
  else
  {
    if (!equal(in0, from))
    {
      DUMP("\nin0: ", in0, "\n", "from: ", from, "\n");
      invalidCodePath;
    }
    out0 = to;
  }
  return out0;
}

inline void
initDataTree(MemoryArena *arena, DataTree *tree, Union *uni, i32 ctor_id)
{
  i32 ctor_arg_count = uni->structs[ctor_id]->param_count;
  tree->ctor_names   = uni->ctor_names;
  tree->ctor_i       = ctor_id;
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
  for (DataMap *map = env->map; map; map=map->tail)
  {
    if (map->depth == in_root_depth && map->index == in_root->index)
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
        map->index   = in_root->index;
        initDataTree(arena, &map->tree, root_union, ctor_id);
        tree = &map->tree;
        map->tail    = env->map;
        env->map     = map;

        DataMapAddHistory *history = pushStruct(temp_arena, DataMapAddHistory, true);
        history->previous_map = map->tail;
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
      map->index   = in_root->index;
      initDataTree(arena, &map->tree, root_union, 0);
      tree = &map->tree;
      map->tail = env->map;
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

internal i32
getConstructorIndex(Typer *typer, Term *in0)
{
  i32 out = -1;
  b32 is_record = false;
  if (Composite *in = castTerm(in0, Composite))
  {
    if (Constructor *ctor = castTerm(in->op, Constructor))
    {
      is_record = true;
      out = ctor->index;
    }
  }
  if (!is_record)
  {
    if (Union *uni = castTerm(getType(in0), Union))
    {
      if (uni->ctor_count == 1)
        out = 0;
      else
      {
        if (DataTree *tree = getDataTree(typer, in0))
          out = tree->ctor_i;
      }
    }
  }
  return out;
}

forward_declare inline Term *
getType(Term *in0)
{
  Term *out = in0->type;
  return out;
}

inline void setType(Term *term, Term *type) {term->type = type;}

inline LocalBindings *
extendBindings(MemoryArena *arena, Typer *env)
{
  LocalBindings *out = pushStruct(arena, LocalBindings, true);
  out->tail     = env->bindings;
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
  env->bindings = env->bindings->tail;
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
isInferredParameter(ArrowAst *arrow, i32 param_id)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_id], ParameterFlag_Inferred);
  return false;
}

inline b32
isInferredParameter(Arrow *arrow, i32 param_id)
{
  if (arrow->param_flags)
    return checkFlag(arrow->param_flags[param_id], ParameterFlag_Inferred);
  return false;
}

inline i32
precedenceOf(String op)
{
  int out = 0;
  const i32 eq_precedence = 50;

  // TODO: implement for real
  if (equal(op, "->"))
    out = eq_precedence - 10;
  else if (equal(op, "=") || equal(op, "!="))
    out = eq_precedence;
  else if (equal(op, "<") || equal(op, ">") || equal(op, "=?") || equal(op, "=="))
    out = eq_precedence + 5;
  else if (equal(op, "+") || equal(op, "-"))
    out = eq_precedence + 10;
  else if (equal(op, "|"))
    out = eq_precedence + 15;
  else if (equal(op, "&") || equal(op, "*"))
    out = eq_precedence + 20;
  else
    out = eq_precedence + 2;

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
  b32 no_print_as_binop = false;
  if (is_term)
  {
    Composite *in = castTerm(value, Composite);
    op           = in->op;
    op_signature = 0;
    raw_args     = (void **)in->args;
    arg_count    = in->arg_count;

    if (in->op)
    {
      if (in->op->cat == Term_Constructor)
        op_is_constructor = true;

      if (Function *fun = castTerm(in->op, Function))
        no_print_as_binop = checkFlag(fun->function_flags, FunctionFlag_no_print_as_binop);

      op_signature = getParameterTypes(in->op);
      assert(op_signature);

      String op_name = {};
      if (Token *global_name = in->op->global_name)
        op_name = global_name->string;
      else if (Variable *var = castTerm(in->op, Variable))
        op_name = var->name;
      precedence = precedenceOf(op_name);
    }
    else
      breakhere; // nocheckin what's this case?
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
      if (print_all_arguments || !isInferredParameter(op_signature, param_id))
        printed_args[arg_count++] = raw_args[param_id];
    }
  }
  else
    printed_args = raw_args;

  if (arg_count == 2 && !no_print_as_binop)
  {// special path for infix binary operator
    if (precedence < opt.no_paren_precedence)
      print(buffer, "(");

    PrintOptions arg_opt = opt;
    // #hack to force printing parentheses when the precedence is the same (a+b)+c.
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
  for (TreePath *path=tree_path; path; path=path->tail)
  {
    print(buffer, "%d", path->head);
    if (path->tail)
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

      case Ast_FunctionAst: {print(buffer, "lambda");} break;

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
          print(buffer, "[%d:%d]", in->delta, in->index);
      } break;

      case Term_Hole:
      {print(buffer, "_");} break;

      case Term_Composite:
      {printComposite(buffer, in0, true, new_opt);} break;

      case Term_Union:
      {
        Union *in = castTerm(in0, Union);
        if (in->punion)
        {
          print(buffer, in->punion->global_name->string);
          Arrow *signature = castTerm(getType(&in->punion->t), Arrow);
          print(buffer, "(");
          for (i32 arg_i=0; arg_i < signature->param_count; arg_i++)
          {
            print(buffer, in->punion_args[arg_i]);
            if (arg_i != signature->param_count-1)
              print(buffer, ", ");
          }
          print(buffer, ")");
        }
        else
        {
          if (in0->global_name && !checkFlag(opt.flags, PrintFlag_Detailed))
          {
            print(buffer, in0->global_name->string);
          }
          else
          {
            print(buffer, "union {");
            if (in->ctor_count)
            {
              unsetFlag(&new_opt.flags, PrintFlag_Detailed);
              for (i32 ctor_id = 0; ctor_id < in->ctor_count; ctor_id++)
              {
                print(buffer, in->ctor_names[ctor_id]);
                print(buffer, ": ");
                print(buffer, &in->structs[ctor_id]->t, new_opt);
                if (ctor_id != in->ctor_count-1)
                  print(buffer, ", ");
              }
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
        if (in0 == builtin_equal)
          print(buffer, "=");
        else if (in0 == builtin_type_equal)
          print(buffer, "=");
        else if (in0 == builtin_Set)
          print(buffer, "Set");
        else if (in0 == builtin_Type)
          print(buffer, "Type");
        else
          todoIncomplete;
      } break;

      case Term_Constructor:
      {
        Constructor *in = castTerm(in0, Constructor);
        print(buffer, in->uni->ctor_names[in->index]);
      } break;

      case Term_Rewrite:
      {
        Rewrite *rewrite = castTerm(in0, Rewrite);
        print(buffer, getType(&rewrite->t), new_opt);
        skip_print_type = true;
        print(buffer, " <=>");
        newlineAndIndent(buffer, opt.indentation);
        print(buffer, getType(rewrite->body), new_opt);
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
        print(buffer, "computation");
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

    if ((checkFlag(opt.flags, PrintFlag_PrintType) ||
         in0->cat == Term_Computation) &&
        !skip_print_type)
    {
      print(buffer, ": ");
      print(buffer, getType(in0), new_opt);
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
    auto scope = scopes->head;
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
  scope->head = signature;
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

    case Term_ParameterizedConstructor:
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

    case Term_ParameterizedUnion:
      invalidCodePath;
  }
}

// todo make this an inline mutation
// TODO handle type!
// TODO handle type!
// TODO handle type!
internal Term *
rebaseMain(MemoryArena *arena, Term *in0, i32 delta, i32 offset)
{
  Term *out0 = 0;
  if (!isGround(in0) && (delta != 0))
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
        out0 = out;
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
apply(MemoryArena *arena, Term *op, i32 arg_count, Term **args, Term *type, String name_to_unfold)
{
  Term *out0 = 0;

#if DEBUG_LOG_apply
  i32 serial = DEBUG_SERIAL++;
  if (DEBUG_MODE)
  {DEBUG_INDENT(); DUMP("apply(", serial, "): ", op, "(...)\n");}
#endif

  if (Function *fun = castTerm(op, Function))
  {// Function application
    b32 should_apply_function = true;
    if (fun->body == &dummy_function_being_built)
      should_apply_function = false;
    if (checkFlag(fun->function_flags, FunctionFlag_no_apply))
    {
      should_apply_function = (name_to_unfold.chars &&
                               equal(fun->global_name->string, name_to_unfold));
    }

    if (should_apply_function)
      out0 = evaluate(EvaluationContext{.arena=arena, .args=args, .flags=EvaluationFlag_ApplyMode},
                      fun->body);
  }
  else if (op == builtin_equal)
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
            if (lctor->index == rctor->index)
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
                out0 = apply(arena, builtin_equal, 3, args, type, {});
                if (!out0)
                  out0 = newEquality(arena, larg, rarg);
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
      out0 = builtin_False;
  }
  else if (op->cat == Term_Constructor)
  {
    Composite *out = newTerm(arena, Composite, type);
    out->op        = op;
    out->arg_count = arg_count;
    out->args      = args;
    out0 = &out->t;
  }

#if DEBUG_LOG_apply
  if (DEBUG_MODE) {DEBUG_DEDENT(); DUMP("=> ", out0, "\n");}
#endif
  return out0;
}

// TODO handle type!
// TODO handle type!
// TODO handle type!
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
          out0 = ctx->args[in->index];
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
          // bookmark
          b32 recursion_match = false;
          if (ctx->punion_op && equal(ctx->punion_op, op))
          {
            recursion_match = true;
            assert(ctx->punion_arg_count == in->arg_count);
            for (i32 arg_i=0; arg_i < in->arg_count && recursion_match; arg_i++)
            {
              if (!equal(ctx->punion_args[arg_i], args[arg_i]))
              {
                recursion_match = false;
              }
            }
            if (recursion_match)
              out0 = ctx->punion_result;
          }
          if (!recursion_match)
            out0 = apply(arena, op, in->arg_count, args, getType(in0), {});
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
        // TODO need to evaluate the type too!
#if 0
        // NOTE: semi-hack so it doesn't normalize our propositions.
        u32 old_flags = ctx->flags;
        unsetFlag(&ctx->flags, EvaluationFlag_ApplyMode);
        out->lhs = evaluateMain(ctx, in->lhs);
        out->rhs = evaluateMain(ctx, in->rhs);
        ctx->flags = old_flags;
#endif
        out0 = out;
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
              out0 = evaluateMain(ctx, in->bodies[ctor->index]);
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
        if (in->punion)
        {
          // todo: I don't have the slightest idea what to do here
          out0 = in0;  // :replaceUnionParameters_is_called_beforehand
        }
        else
        {
          Union *out = copyStruct(arena, in);
          // :recursion_result_set_later
          if (ctx->punion_op && !ctx->punion_result)
          {
            ctx->punion_result = &out->t;
          }
          allocateArray(arena, in->ctor_count, out->structs);
          for (i32 id=0; id < in->ctor_count; id++)
          {
            Term *struc = evaluateMain(ctx, &in->structs[id]->t);
            out->structs[id] = castTerm(struc, Arrow);
          }
          out0 = &out->t;
        }
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
evaluate(EvaluationContext ctx, Term *in0)
{
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
    DEBUG_INDENT(); DUMP("comparing(", serial, "): ", lhs0, " and ", rhs0, "\n");
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
        if ((lhs->delta == rhs->delta) && (lhs->index == rhs->index))
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
            out.diff_path->head = unique_diff_id;
            out.diff_path->tail  = unique_diff_path;
          }
        }
      } break;

      case Term_Constructor:
      {
        Constructor *lhs = castTerm(lhs0, Constructor);
        Constructor *rhs = castTerm(rhs0, Constructor);
        out.result = toTrinary(equal(&lhs->uni->t, &rhs->uni->t) &&
                               (lhs->index == rhs->index));
      } break;

      case Term_Accessor:
      {
        Accessor *lhs = castTerm(lhs0, Accessor);
        Accessor *rhs = castTerm(rhs0, Accessor);
        if (equal(lhs->record, rhs->record) &&
            lhs->field_id == rhs->field_id)
        {
          out.result = Trinary_True;
        }
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
  {DEBUG_DEDENT(); DUMP("=>(", serial, ") ", out.result, "\n");}
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
      else if (slot->hash_tail)
        slot = slot->hash_tail;
      else
      {
        if (add_new)
        {
          slot->hash_tail = pushStruct(global_state.top_level_arena, GlobalBinding, true);
          slot = slot->hash_tail;
          slot->key = key;
        }
        else
          slot = 0;
        break;
      }
    }
  }
  else if (add_new)
    slot->key = key;
  else
    slot = 0;

  if (slot && !add_new)
    assert(slot->count != 0);

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
      else if (slot->tail)
        slot = slot->tail;
      else
      {
        stop = true;
        if (add_if_missing)
        {
          allocate(bindings->arena, slot->tail);
          slot = slot->tail;
          slot->key  = key;
          slot->tail = 0;
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

// todo #cleanup #leak don't allocate without progress
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

        out0 = apply(arena, norm_op, in->arg_count, norm_args, getType(in0), ctx->name_to_unfold);

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
        for (DataMap *map = ctx->map; map; map=map->tail)
        {
          if (map->depth == var_depth && map->index == in->index)
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

internal Term *
normalize(MemoryArena *arena, Typer *env, Term *in0, String name_to_unfold)
{
  NormalizeContext ctx = {.arena=arena, .map=(env ? env->map : 0), .depth=getScopeDepth(env), .name_to_unfold=name_to_unfold};
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
introduceSignature(Typer *typer, Arrow *signature, b32 add_bindings)
{
  i32 param_count = signature->param_count;
  typer->scope = newScope(typer->scope, signature);
  if (add_bindings)
  {
    extendBindings(temp_arena, typer);
    for (i32 index=0; index < param_count; index++)
    {
      String name = signature->param_names[index];
      addLocalBinding(typer, name, index);
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
      bindings = bindings->tail;
  }

  return out;
}

inline b32
requireChar(char c, char *reason=0, Tokenizer *tk=global_tokenizer)
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
      parseError(tk, &token, "expected character '%c' (%s)", c, reason);
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
        Term *arg = composite->args[path->head];
        return subExpressionAtPath(arg, path->tail); 
      } break;

      invalidDefaultCase;
    }
  }
  else
    return in;
}

inline i32
getExplicitParamCount(ArrowAst *in)
{
  i32 out = 0;
  for (i32 param_id = 0; param_id < in->param_count; param_id++)
  {
    if (!isInferredParameter(in, param_id))
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
    if (!isInferredParameter(in, param_id))
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

internal b32
unify(Stack *stack, Term *in0, Term *goal0)
{
  b32 success = false;

  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
#if DEBUG_LOG_unify
  if (DEBUG_MODE)
  {DEBUG_INDENT(); DUMP("unify(", serial, ") ", in0, " with ", goal0, "\n");}
#endif

  switch (in0->cat)
  {
    case Term_Variable:
    {
      Variable *in = castTerm(in0, Variable);
      Stack *lookup_stack = stack;
      for (i32 delta=0;  delta < in->delta && lookup_stack;  delta++)
      {
        lookup_stack = lookup_stack->outer;
      }
      if (lookup_stack)
      {
        // unification variable
        if (Term *lookup = lookup_stack->items[in->index])
        {
          Term *rebased = rebase(temp_arena, lookup, in->delta);
          success = equal(rebased, goal0);
        }
        else if (unify(stack, getType(in0), getType(goal0)))
        {
          // NOTE: if rebase happens -> the new term will be on the correct arena.
          // if rebase does nothing -> we put "goal0" on there, which is by definition on the correct arena.
          lookup_stack->items[in->index] = rebase(lookup_stack->unification_arena, goal0, -in->delta);
          if (lookup_stack->unification_arena != temp_arena)
            assert(inArena(lookup_stack->unification_arena, lookup_stack->items[in->index]));
          success = true;
        }
      }
      else if (Variable *goal = castTerm(goal0, Variable))
      {
        // NOTE: local variable from a local hint, we would remove one
        // abstraction layer if unification succeeds, hence we deduct one stack
        // delta.
        success = ((in->delta-1 == goal->delta) && (in->index == goal->index));
      }
    } break;

    case Term_Composite:
    {
      Composite *in = castTerm(in0, Composite);
      if (Composite *goal = castTerm(goal0, Composite))
      {
        if (unify(stack, in->op, goal->op))
        {
          success = true;
          for (int id=0; id < in->arg_count; id++)
          {
            if (!unify(stack, in->args[id], goal->args[id]))
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
      Arrow *in = castTerm(in0, Arrow);
      if (Arrow *goal = castTerm(goal0, Arrow))
      {
        if (in->param_count == goal->param_count)
        {
          success = true;
          Stack *new_stack = newStack(temp_arena, stack, in->param_count);
          new_stack->unification_arena = temp_arena;
          for (i32 id=0; id < in->param_count && success; id++)
          {
            if (!unify(new_stack, in->param_types[id], goal->param_types[id]))
            {
              success = false;
            }
          }
          if (success)
          {
            success = unify(new_stack, in->output_type, goal->output_type);
          }
        }
      }
    } break;

    case Term_Function:
    case Term_Union:
    case Term_Constructor:
    case Term_Builtin:
    {
      success = equal(in0, goal0);
    } break;

    default:
    {
      todoIncomplete;
    } break;
  }

#if DEBUG_LOG_unify
  if (DEBUG_MODE)
  {DEBUG_DEDENT(); DUMP("=>(", serial, ") ", ((char *)(success ? "true\n" : "false\n")));}
#endif

  return success;
}

inline Union *
castUnionWithArgs(Term *in0)
{
  Union *out = 0;
  if (Union *in = castTerm(in0, Union))
  {
    if (in->punion)
      out = in;
  }
  return out;
}

inline SolveArgs
solveArgs(Solver *solver, Term *op, Term *goal, Token *blame_token)
{
  b32    matches   = false;
  i32    arg_count = 0;
  Term **args      = 0;
  if (Constructor *ctor = castTerm(op, Constructor))
  {
    matches = equal(&ctor->uni->t, goal);
    // don't attempt to solve args since it's a constructor.
  }
  else if (ParameterizedConstructor *ctor = castTerm(op, ParameterizedConstructor))
  {
    if (Union *uni = castUnionWithArgs(goal))
    {
      matches = (ctor->punion == uni->punion);
    }
    // don't attempt to solve args since it's a constructor.
  }
  else if (Arrow *signature = castTerm(getType(op), Arrow))
  {
    Stack *stack = newStack(solver->arena, 0, signature->param_count);
    stack->unification_arena = solver->arena;
    if (unify(stack, signature->output_type, goal))
    {
      matches   = true;
      arg_count = signature->param_count;
      args      = stack->items;
      for (i32 arg_i=0; arg_i < signature->param_count; arg_i++)
      {
        // solving loop
        if (!args[arg_i])
        {
          // todo #leak the type could be referenced
          Term *type = evaluate(solver->arena, args, signature->param_types[arg_i]);
          if (!(args[arg_i] = solveGoal(solver, type)))
          {
            if (blame_token)
            {
              parseError(blame_token, "failed to solve arg %d", arg_i);
              attach("arg_type", type);
            }
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
solveArgs(Solver solver, Term *op, Term *goal, Token *blame_token)
{
  return solveArgs(&solver, op, goal, blame_token);
}

inline Term *
newComputation_(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Term *eq = newEquality(arena, lhs, rhs);
  Computation *out = newTerm(arena, Computation, eq);
  return out;
}

inline Term *
newComputationIfEqual(MemoryArena *arena, Typer *typer, Term *lhs, Term *rhs)
{
  // NOTE: mega_paranoid check.
  Term *out = 0;
  if (equal(normalize(arena, typer, lhs),
            normalize(arena, typer, rhs)))
  {
    out = newComputation_(arena, lhs, rhs);
  }
  return out;
}

inline Term *
seekGoal(MemoryArena *arena, Typer *typer, Term *goal)
{
  Term *out = 0;
  auto temp = beginTemporaryMemory(arena);
  if (typer)
  {
    i32 delta = 0;
    for (Scope *scope = typer->scope; scope; scope=scope->outer)
    {
      Arrow *arrow = scope->head;
      for (i32 param_i=0; param_i < arrow->param_count; param_i++)
      {
        // todo #speed we're having to rebase everything, which sucks but
        // unless we store position-independent types, that's what we gotta do.
        Term *var = newVariable(arena, typer, param_i, delta);
        if (equal(getType(var), goal))
        {
          out = var;
        }
        else if (Union *uni = castTerm(getType(var), Union))
        {
          i32 ctor_i = getConstructorIndex(typer, var);
          if (ctor_i >= 0)
          {
            Arrow *struc = uni->structs[ctor_i];
            Term **members = synthesizeMembers(arena, var, ctor_i);
            for (i32 member_i = 0; member_i < struc->param_count && !out; member_i++)
            {
              Term *member = members[member_i];
              if (equal(getType(member), goal))
                out = member;
            }
          }
        }
      }
      delta++;
    }
  }
  if (out)
    commitTemporaryMemory(temp);  // todo This still #leaks because there are members we don't use.
  else
    endTemporaryMemory(temp);
  return out;
}

forward_declare internal Term *
solveGoal(Solver *solver, Term *goal)
{
  Term *out = 0;
  solver->depth++;

  b32 should_attempt_inference = true;
  if (solver->depth > MAX_SOLVE_DEPTH ||
      goal == builtin_Set ||
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
      out = newComputationIfEqual(solver->arena, solver->typer, l, r);
    }

    if (!out)
    {
      b32 tried_global_hints = false;
      for (HintDatabase *hints = solver->local_hints;
           !out;
           hints = hints->tail)
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
          Term *hint = hints->head;
          if (getType(hint)->cat == Term_Arrow)
          {
            SolveArgs solution = solveArgs(solver, hint, goal, 0);
            if (solution.args)
            {
              MemoryArena *arena = solver->arena;
              Term **args = copyArray(arena, solution.arg_count, solution.args);
              out = newComposite(arena, hint, solution.arg_count, args);
            }
          }
          else if (equal(getType(hint), goal))
            out = hint;
        }
        else
          break;
      }

      if (!out)
        out = seekGoal(solver->arena, solver->typer, goal);
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
solveGoal(Solver solver, Term *goal)
{
  return solveGoal(&solver, goal);
}

inline TermArray
getFunctionOverloads(Identifier *ident, Term *output_type_goal)
{
  i32 UNUSED_VAR serial = DEBUG_SERIAL;
  TermArray out = {};
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident, false))
  {
    if (output_type_goal->cat == Term_Hole)
    {
      // bypass typechecking.
      out.items = slot->items;
      out.count = slot->count;
    }
    else
    {
      allocateArray(temp_arena, slot->count, out.items);
      for (int slot_id=0; slot_id < slot->count; slot_id++)
      {
        Term *item = slot->items[slot_id];
        if (solveArgs(Solver{.arena=temp_arena}, item, output_type_goal, 0).matches)
          out.items[out.count++] = slot->items[slot_id];
      }
      if (out.count == 0)
      {
        parseError(&ident->a, "found no matching overload");
        attach("serial", serial);
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
fillInEllipsis(MemoryArena *arena, Typer *typer, Identifier *op_ident, Term *goal)
{
  // NOTE: This routine is different from "solveGoal" in that the top-level
  // operator is fixed.
  Term *out = 0;
  pushContext(__func__);

  if (goal->cat == Term_Hole)
  {
    parseError(&op_ident->a, "cannot solve for arguments since we do know what the output type of this function should be");
  }
  else if (lookupLocalName(typer, &op_ident->token))
  {
    todoIncomplete;
  }
  else if (GlobalBinding *slot = lookupGlobalNameSlot(op_ident, false))
  {
    for (int slot_i=0;
         slot_i < slot->count && noError() && !out;
         slot_i++)
    {
      Term *item = slot->items[slot_i];
      SolveArgs solution = solveArgs(Solver{.arena=temp_arena, .typer=typer}, item, goal, &op_ident->token);
      if (solution.matches && solution.args)
      {
        // NOTE: we don't care which function matches, just grab whichever
        // matches first.
        Term **args = copyArray(arena, solution.arg_count, solution.args);
        out = newComposite(arena, slot->items[slot_i], solution.arg_count, args);
        assert(equal(getType(out), goal));
      }
    }
    if (!out && noError())
    {
      parseError(&op_ident->a, "found no matching overload");
      attach("available_overloads", slot->count, slot->items, printOptionPrintType());
    }
  }
  else
  {
    parseError(&op_ident->a, "identifier not found");
    attach("identifier", op_ident->token.string);
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
          out.path->head = -1;
          out.path->tail  = op.path;
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
              out.path->head = arg_id;
              out.path->tail  = arg.path;
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
    // Can't get out of this rewind business, because sometimes the sequence is empty :<
    Tokenizer tk_save = *global_tokenizer;
    Token token = nextToken();
    Ast *ast0 = 0;
    switch (TacticEnum tactic = matchTactic(token.string))
    {
      case Tactic_norm:
      {
        pushContext("norm [EXPRESSION]");
        String name_to_unfold = {};

        if (optionalString("unfold"))
        {
          pushContext("unfold(FUNCTION_NAME)");
          if (requireChar('('))
          {
            if (requireIdentifier("expect function name"))
            {
              name_to_unfold = lastToken()->string;
              requireChar(')');
            }
          }
          popContext();
        }

        if (noError())
        {
          NormalizeMeAst *ast_goal = newAst(arena, NormalizeMeAst, &token);
          ast_goal->name_to_unfold = name_to_unfold;
          if (seesExpressionEndMarker())
          {// normalize goal
            GoalTransform *ast = newAst(arena, GoalTransform, &token);
            ast->new_goal = &ast_goal->a;
            ast0 = &ast->a;
          }
          else if (Ast *expression = parseExpression(arena))
          {// normalize with let.
            Let *let = newAst(arena, Let, &token);
            let->rhs  = expression;
            let->type = &ast_goal->a;
            ast0 = &let->a;
            if (expression->cat == Ast_Identifier)
            {
              // borrow the name if the expression is an identifier 
              let->lhs  = expression->token.string;
            }
            else
            {
              // NOTE This case can happen if it's a "seek"
            }
          }
        }

        popContext();
      } break;

      case Tactic_rewrite:
      {
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);

        rewrite->right_to_left = false;
        Token next = peekToken();
        if (equal(next.string, "<-"))
        {
          nextToken();
          rewrite->right_to_left = true;
        }

        rewrite->eq_proof = parseExpression(arena);
        ast0 = &rewrite->a;
      } break;

      case Tactic_goal_transform:
      {
        pushContext("Goal transform: => NEW_GOAL [{ EQ_PROOF_HINT }]; ...");
        GoalTransform *ast = newAst(arena, GoalTransform, &token);
        ast0 = &ast->a;
        if (optionalCategory(Token_Directive_print_proof))
        {
          ast->print_proof = true;
        }
        if (optionalString("norm"))
        {
          ast->new_goal = &newAst(arena, NormalizeMeAst, &token)->a;
        }
        else
        {
          ast->new_goal = parseExpression(arena);
          if (optionalChar('{'))
          {
            if (optionalChar('}'))
            {
              // no hint provided, this case is just for editing convenience.
            }
            else
            {
              ast->hint = parseExpression(arena);
              requireChar('}');
            }
          }
        }
        popContext();
      } break;

      case Tactic_prove:
      {
        pushContext("prove PROPOSITION {SEQUENCE} as IDENTIFIER");
        if (Ast *proposition = parseExpression(arena))
        {
          if (Ast *proof = parseSequence(arena, true))
          {
            String name = toString("anon");
            if (optionalString("as") && requireIdentifier("expected name for the proof"))
            {
              name = lastToken()->string;
            }
            if (noError())
            {
              Let *let = newAst(arena, Let, &token);
              let->lhs  = name;
              let->rhs  = proof;
              let->type = proposition;
              ast0 = &let->a;
            }
          }
        }
        popContext();
      } break;

      case Tactic_return:
      {
        ast0 = parseExpression(arena);
        reached_end_of_sequence = true;
      } break;

      case Tactic_fork:
      {
        ast0 = parseFork(arena);
        reached_end_of_sequence = true;
      } break;

      case Tactic_seek:
      {
        SeekAst *ast = newAst(arena, SeekAst, &token);
        ast0 = &ast->a;
        reached_end_of_sequence = true;
      } break;

      case (TacticEnum)0:
      {
        if (isIdentifier(&token))
        {
          // NOTE: identifiers can't be tactics, but I don't think that's a concern.
          Token *name = &token;
          Token after_name = nextToken();
          switch (after_name.cat)
          {
            case Token_ColonEqual:
            {
              pushContext("let: NAME := VALUE");
              if (Ast *rhs = parseExpression(arena))
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
              if (Ast *type = parseExpression(arena))
              {
                if (requireCategory(Token_ColonEqual, ""))
                {
                  if (Ast *rhs = parseExpression(arena))
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

            default:
            {
              parseError("invalid syntax for sequence item (keep in mind that we're in a sequence, so you need to use the \"return\" keyword to return an expression)");
            } break;
          }
        }
        else if (isExpressionEndMarker(&token))
        {// synthetic hole
          ast0  = newAst(arena, Hole, &token);
          *global_tokenizer = tk_save;
          reached_end_of_sequence = true;
        }
        else
        {
          parseError("expected a sequence item");
        }
      } break;
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->head = ast0;
      new_list->tail  = list;
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
      Ast *item0 = list->head;
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
        list = list->tail;
    }
    out = list->head;
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

inline Term *
buildCtorAst(MemoryArena *arena, CtorAst *in, Term *output_type)
{
  Term *out = 0;
  if (Union *uni = castTerm(output_type, Union))
  {
    if (in->ctor_i < uni->ctor_count)
      out = newConstructor(arena, uni, in->ctor_i);
    else
      parseError(&in->a, "union only has %d constructors", uni->ctor_count);
  }
  else
    parseError(&in->a, "cannot guess union of constructor");
  return out;
}

inline HintDatabase *
addHint(MemoryArena *arena, HintDatabase *hint_db, Term *term)
{
  HintDatabase *new_hints = pushStruct(arena, HintDatabase, true);
  new_hints->head = term;
  new_hints->tail  = hint_db;
  return new_hints;
}

inline Term *
getOverloadFromDistinguisher(GlobalBinding *lookup, Term *distinguisher)
{
  Term *out = 0;
  for (i32 slot_i=0;
       slot_i < lookup->count && !out;
       slot_i++)
  {
    Term *item = lookup->items[slot_i];
    if (Arrow *signature = castTerm(getType(item), Arrow))
    {
      b32 matches = false;
      if (distinguisher->cat == Term_Union)
        // TODO very #hacky
        matches = equal(signature->param_types[0], distinguisher);
      else
        todoIncomplete;

      if (matches)
        out = item;
    }
  }
  return out;
}

inline Term *
getOverloadFromDistinguisher(Token *token, const char *name, Term *distinguisher)
{
  Term *out = 0;
  if (GlobalBinding *lookup = lookupGlobalNameSlot(toString(name), false))
  {
    out = getOverloadFromDistinguisher(lookup, distinguisher);
  }
  else
    parseError(token, "no function named \"%s\" found that matches distinguisher", name);

  return out;
}

inline b32
isAlgebraicNorm(Ast *ast)
{
  // Could be extended to a general macro matcher, if we need more macros.
  b32 out = false;
  if (Identifier *ident = castAst(ast, Identifier))
  {
    if (equal(&ident->a.token, "algebraic_norm"))
    {
      out = true;
    }
  }
  return out;
}

inline b32
stringLessThan(String a, String b)
{
  b32 out = false;
  if (a.length < b.length)
    out = true;
  else if (a.length == b.length)
  {
    for (i32 i=0; i < a.length; i++)
    {
      if (a.chars[i] < b.chars[i])
      {
        out = true;
        break;
      }
    }
  }

  return out;
}

inline b32
algebraicallyLessThan(Term *a0, Term *b0)
{
  b32 out = false;
  switch (a0->cat)
  {
    case Term_Variable:
    {
      Variable *a = castTerm(a0, Variable);
      if (Variable *b = castTerm(b0, Variable))
        out = stringLessThan(a->name, b->name);
    } break;
  }
  return out;
}

inline TreePath *
treePath(MemoryArena *arena, i32 head, TreePath *tail)
{
  TreePath *out = pushStruct(arena, TreePath, true);
  out->head = head;
  out->tail = tail;
  return out;
}

inline TreePath *
reverseInPlace(TreePath *in)
{
  TreePath *out = 0;
  for (TreePath *it = in; it; )
  {
    TreePath *next_it = it->tail;
    it->tail = out;
    out = it;
    it = next_it;
  }
  return out;
}

inline TreePath *
reversePath(MemoryArena *arena, TreePath *in)
{
  TreePath *out = 0;
  for (TreePath *it = in; it; it = it->tail)
  {
    TreePath *new_out = pushStruct(arena, TreePath, true);
    new_out->head = it->head;
    new_out->tail = out;
    out = new_out;
  }
  return out;
}

inline TreePath *
addToEnd(MemoryArena *arena, TreePath *prefix, i32 item)
{
  TreePath *reverse_prefix = reversePath(arena, prefix);
  TreePath *out = pushStruct(arena, TreePath, true);
  out->head = item;
  out->tail = reverse_prefix;
  out = reverseInPlace(out);
  return out;
}

inline Term *
getTransformationResult(Term *in)
{
  auto [_, out] = getEqualitySides(getType(in));
  return out;
}

inline Term *
applyEqChain(MemoryArena *arena, Term *e1, Term *e2)
{
  auto [a,b] = getEqualitySides(getType(e1));
  auto [_,c] = getEqualitySides(getType(e2));
  Term *A = getType(a);
  Term *out = newCompositeN(arena, builtin_eqChain, 6, A, a,b,c, e1,e2);
  return out;
}

inline Term *
transformPartOfExpression(MemoryArena *arena, Term *eq_proof, TreePath *path, Term *in)
{
  Term *id = newIdentity(arena, in);
  return newRewrite(arena, eq_proof, id, treePath(arena, 2, path), true);
}

inline Term *
getAlgebraicNorm(MemoryArena *arena, Typer *typer, Algebra *algebra, Term *in0)
{
  Term *out = 0;
  Term *expression0 = in0;

  if (Composite *expression = castTerm(expression0, Composite))
  {
    if (equal(expression->op, algebra->add))
    {
      Term *r = expression->args[1];
      if (Term *norm_r = getAlgebraicNorm(arena, typer, algebra, r))
      {
        out = transformPartOfExpression(arena, norm_r, treePath(arena, 1, 0), expression0);
        expression0 = getTransformationResult(out);
      }
    }
  }

  for (b32 stop = false; !stop; )
  {
    stop = true;
    if (Composite *expression = castTerm(expression0, Composite))
    {
      if (equal(expression->op, algebra->add))
      {
        Term *l0 = expression->args[0];
        Term *r  = expression->args[1];

        if (Composite *l = castTerm(l0, Composite))
        {
          if (equal(l->op, algebra->add))
          {
            stop = false;
            Term *new_proof = newComposite3(arena, algebra->addAssociative, l->args[0], l->args[1], r);
            if (out)
              out = applyEqChain(arena, out, new_proof);
            else
              out = new_proof;
            expression0 = getTransformationResult(out);
          }
        }
      }
    }
  }

  return out;
}

inline Term *
buildAlgebraicNorm(MemoryArena *arena, Typer *typer, CompositeAst *in)
{
  Term *out = 0;
  // Solver solver = Solver{.arena=arena, .typer=typer, .use_global_hints=true};
  if (in->arg_count == 1)
  {
    if (Term *expression0 = buildTerm(arena, typer, in->args[0], holev))
    {
      b32 found_algebra_match = false;
      for (AlgebraDatabase *algebras = global_state.algebras;
           algebras && !found_algebra_match;
           algebras = algebras->tail)
      {
        Algebra *algebra = &algebras->head;
        if (equal(getType(expression0), algebra->type))
        {
          found_algebra_match = true;
          out = getAlgebraicNorm(arena, typer, algebra, expression0);
        }
      }
    }
  }
  else
    parseError("expected 1 argument");

  if (!out)
    parseError(&in->a, "either the expression is already in normal form, or we can't solve the goal");

  return out;
}

forward_declare internal BuildTerm
buildTerm(MemoryArena *arena, Typer *typer, Ast *in0, Term *goal)
{
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 UNUSED_VAR serial = DEBUG_SERIAL++;
  Term *out0 = {};
  assert(goal);
  b32 should_check_type = true;
  b32 recursed = false;

  switch (in0->cat)
  {
    case Ast_CompositeAst:
    {
      CompositeAst *in  = castAst(in0, CompositeAst);

      if (in->arg_count == 1 &&
          in->args[0]->cat == Ast_Ellipsis)
      {
        // Solve all arguments.
        if (Identifier *op_ident = castAst(in->op, Identifier))
          out0 = fillInEllipsis(arena, typer, op_ident, goal);
        else
          parseError(in->args[0], "todo: ellipsis only works with identifier atm");
      }
      else if (isAlgebraicNorm(in->op))
      {
        // macro interception
        out0 = buildAlgebraicNorm(arena, typer, in);
      }
      else
      {
        TermArray op_list = {};
        b32 should_build_op = true;
        if (Identifier *op_ident = castAst(in->op, Identifier))
        {
          if (!lookupLocalName(typer, &in->op->token))
          {
            should_build_op = false;
            op_list = getFunctionOverloads(op_ident, goal);
          }
        }
        else if (CtorAst *op_ctor = castAst(in->op, CtorAst))
        {
          if (Term *ctor = buildCtorAst(arena, op_ctor, goal))
          {
            should_build_op = false;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.count    = 1;
            op_list.items[0] = ctor;
          }
        }

        if (noError() && should_build_op)
        {
          if (Term *op0 = buildTerm(arena, typer, in->op, holev).term)
          {
            op_list.count = 1;
            allocateArray(temp_arena, 1, op_list.items);
            op_list.items[0] = op0;
          }
        }

        for (i32 attempt=0;
             (attempt < op_list.count) && (!out0) && noError();
             attempt++)
        {
          Term *op = op_list.items[attempt];
          if (Arrow *signature = getParameterTypes(op))
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
                  if (isInferredParameter(signature, param_id))
                  {
                    // NOTE: We fill the missing argument with synthetic holes,
                    // because the user input might also have actual holes, so
                    // this makes the code more uniform.
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
              Term **args = pushArray(temp_arena, param_count, Term *, true);
              b32 stack_has_hole = false;  // This var is an optimization: in case we can just solve all the args in one pass.
              // bookmark: it should not be arg_i = 0!!! We messed up the infer mechanism somehow.
              for (int arg_i = 0;
                   (arg_i < param_count) && noError();
                   arg_i++)
              {
                // First round: Build and Infer arguments.
                Term *param_type0 = signature->param_types[arg_i];
                Ast *in_arg = expanded_args[arg_i];
                b32 arg_was_filled = false;
                if (in_arg->cat != Ast_Hole)
                {
                  if (stack_has_hole)
                  {
                    if (Term *arg = buildTerm(arena, typer, in_arg, holev).term)
                    {
                      args[arg_i] = arg;
                      arg_was_filled = true;
                      Stack stack = {.count=param_count, .items=args, .unification_arena=arena};
                      b32 unify_result = unify(&stack, param_type0, getType(arg));
                      if (!unify_result)
                      {
                        parseError(in_arg, "cannot unify parameter type with argument %d's type", arg_i);
                        attach("serial", serial);
                        attach("parameter_type", param_type0);
                        attach("argument_type", getType(arg));
                      }
                    }
                    else
                    {
                      // todo recover from ambiguity only
                      if (!checkErrorFlag(ErrorUnrecoverable))
                        wipeError();
                    }
                  }
                  else
                  {
                    Term *expected_arg_type = evaluate(arena, args, param_type0);
                    if (Term *arg = buildTerm(arena, typer, in_arg, expected_arg_type).term)
                    {
                      args[arg_i] = arg;
                      arg_was_filled = true;
                    }
                  }
                }
                stack_has_hole = stack_has_hole || !arg_was_filled;
              }

              if (noError() && stack_has_hole)
              {
                // Second round, Build and Solve the remaining args.
                for (int arg_i = 0;
                     (arg_i < param_count) && noError();
                     arg_i++)
                {
                  if (!args[arg_i])
                  {
                    Ast *in_arg = expanded_args[arg_i];
                    Term *param_type0 = signature->param_types[arg_i];
                    Term *expected_arg_type = evaluate(arena, args, param_type0);
                    if (in_arg->cat == Ast_Hole)
                    {
                      if (Term *fill = solveGoal(Solver{.arena=arena, .typer=typer}, expected_arg_type))
                      {
                        args[arg_i] = fill;
                      }
                      else
                      {
                        parseError(in_arg, "cannot fill in argument %d", arg_i);
                        attach("expected_arg_type", expected_arg_type);
                      }
                    }
                    else if (Term *arg = buildTerm(arena, typer, in_arg, expected_arg_type).term)
                    {
                      args[arg_i] = arg;
                    }
                  }
                }
              }

              if (noError())
              {
                if (ParameterizedUnion *puni = castTerm(op, ParameterizedUnion))
                {
                  // bookmark
                  Union *out       = copyStruct(arena, puni->body);
                  out->punion_args = args;
                  out0 = &out->t;
                }
                else
                {
                  Term **final_args        = 0;
                  Term  *final_op          = op;
                  i32    final_param_count = param_count;
                  if (ParameterizedConstructor *pctor = castTerm(op, ParameterizedConstructor))
                  {
                    // some monkey business to convert the op to ctor.
                    ParameterizedUnion *puni = pctor->punion;
                    // bookmark
                    Union *uni       = copyStruct(arena, puni->body);
                    uni->punion_args = args;
                    final_op = newConstructor(arena, castTerm(uni, Union), pctor->index);
                    assert(param_count >= pctor->param_count);
                    final_param_count = param_count - pctor->param_count;
                    final_args        = copyArray(arena, final_param_count, args+pctor->param_count);
                  }
                  else
                  {
                    final_args = copyArray(arena, param_count, args);
                  }
                  out0 = newComposite(arena, final_op, final_param_count, final_args);
                }
              }
            }
          }
          else
          {
            parseError(in->op, "operator must have an arrow type");
            attach("operator type", getType(op));
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
      assert(!out0 || getType(out0));
    } break;

    case Ast_Hole:
    {
      if (Term *solution = solveGoal(Solver{.arena=arena, .typer=typer, .use_global_hints=true}, goal))
        out0 = solution;
      else
        parseError(in0, "please provide an expression here");
      assert(!out0 || getType(out0));
    } break;

    case Ast_SyntheticAst:
    {
      SyntheticAst *in = castAst(in0, SyntheticAst);
      out0 = in->term;
      assert(!out0 || getType(out0));
    } break;

    case Ast_Identifier:
    {
      // Identifier *in = castAst(in0, Identifier);
      Token *name = &in0->token;
      if (LookupLocalName local = lookupLocalName(typer, name))
      {
        out0 = newVariable(arena, typer, local.var_id, local.stack_delta);
      }
      else
      {
        Term *value = 0;
        if (GlobalBinding *globals = lookupGlobalName(name))
        {
          for (i32 value_id = 0; value_id < globals->count; value_id++)
          {
            Term *slot_value = globals->items[value_id];
            if (matchType(getType(slot_value), goal))
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
              attach("actual_type", getType(globals->items[0]));
          }
        }

        if (value)
        {
          should_check_type = false;
          out0 = value;
        }
      }
      assert(!out0 || getType(out0));
    } break;

    case Ast_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      Arrow *out = newTerm(arena, Arrow, builtin_Type);
      i32 param_count = in->param_count;
      out->param_count = param_count;
      out->param_names = copyArray(arena, param_count, in->param_names); // todo copy festival
      out->param_flags = copyArray(arena, param_count, in->param_flags);
      allocateArray(arena, param_count, out->param_types);
      {
        typer->scope = newScope(typer->scope, out);
        extendBindings(temp_arena, typer);
        for (i32 index=0; index < param_count && noError(); index++)
        {
          if (Term *param_type = buildTerm(arena, typer, in->param_types[index], holev))
          {
            out->param_types[index] = param_type;
            String name = in->param_names[index];
            addLocalBinding(typer, name, index);
          }
        }

        if (noError())
        {
          out0 = &out->t;
          if (in->output_type)
          {
            if (Term *output_type = buildTerm(arena, typer, in->output_type, holev).term)
              out->output_type = output_type;
          }
        }
        unwindBindingsAndScope(typer);
      }
      assert(!out0 || getType(out0));
    } break;

    case Ast_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      if (Term *record0 = buildTerm(arena, typer, in->record, holev).term)
      {
        i32 ctor_i = getConstructorIndex(typer, record0);
        if (ctor_i >= 0)
        {
          Union *uni = castTerm(getType(record0), Union);
          Arrow *op_type = uni->structs[ctor_i];
          i32 param_count = op_type->param_count;
          b32 valid_param_name = false;
          i32 field_id = -1;
          for (i32 param_id=0; param_id < param_count; param_id++)
          {// figure out the param id
            if (equal(in->field_name.string, op_type->param_names[param_id]))
            {
              field_id = param_id;
              valid_param_name = true;
              break;
            }
          }

          if (valid_param_name)
          {
            Term **args = 0;
            if (Composite *record = castTerm(record0, Composite))
            {
              if (Constructor *ctor = castTerm(record->op, Constructor))
                args = record->args;
            }
            if (!args)
            {
              args = synthesizeMembers(arena, record0, ctor_i);
            }
            Term *type = args[field_id]->type;

            Accessor *out = newTerm(arena, Accessor, type);
            out->record     = record0;
            out->field_id   = field_id;
            out->field_name = in->field_name.string;
            out0 = &out->t;
          }
          else
          {
            tokenError(&in->field_name, "accessor has invalid member");
            attach("expected a member of constructor", uni->ctor_names[ctor_i]);
            setErrorFlag(ErrorUnrecoverable);
          }
          assert(!out0 || getType(out0));
        }
        else
        {
          parseError(in->record, "cannot access a non-record");
          setErrorFlag(ErrorUnrecoverable);
        }
      }
    } break;

    case Ast_FunctionAst:
    {
      // todo :build-global-function-vs-local-function
      FunctionAst *in   = castAst(in0, FunctionAst);
      Term   *type = goal;
      if (in->signature)
        type = buildTerm(arena, typer, &in->signature->a, holev).term;

      if (noError())
      {
        if (Arrow *signature = castTerm(type, Arrow))
        {
          Function *fun = newTerm(arena, Function, &signature->t);

          introduceSignature(typer, signature, true);
          if (Term *body = buildTerm(arena, typer, in->body, signature->output_type).term)
          {
            fun->body           = body;
            fun->function_flags = in->function_flags;  // we don't use any flag for local functions atm but let's just keep things the same.
          }
          unwindBindingsAndScope(typer);
          if (noError())
            out0  = &fun->t;
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
      if (Term *eq_proof = buildTerm(arena, typer, in->eq_proof, holev).term)
      {
        Term *proof_type = getType(eq_proof);
        if (auto [lhs, rhs] = getEqualitySides(proof_type, false))
        {
          Term *from = in->right_to_left ? rhs : lhs;
          Term *to   = in->right_to_left ? lhs : rhs;
          SearchOutput search = searchExpression(arena, typer, from, goal);
          if (search.found)
          {
            new_goal = rewriteTerm(arena, from, to, search.path, goal);
            if (Term *body = buildTerm(arena, typer, in->body, new_goal).term)
              out0 = newRewrite(arena, eq_proof, body, search.path, in->right_to_left);
          }
          else
          {
            parseError(in0, "cannot find a place to apply the rewrite");
            attach("substitution", proof_type);
          }
        }
        else
        {
          parseError(in->eq_proof, "please provide a proof of equality for rewrite");
          attach("got", proof_type);
        }
      }
      assert(!out0 || getType(out0));
    } break;

    case Ast_GoalTransform:
    {
      GoalTransform *in = castAst(in0, GoalTransform);
      Term     *new_goal      = 0;
      Term     *eq_proof      = 0;
      TreePath *rewrite_path  = 0;
      b32       right_to_left = false;

      if (NormalizeMeAst *in_new_goal = castAst(in->new_goal, NormalizeMeAst))
      {// just normalize the goal, no need for tactics (for now).
        Term *norm_goal = normalize(arena, typer, goal, in_new_goal->name_to_unfold);
        if (checkFlag(in->flags, AstFlag_Generated) &&
            equal(goal, norm_goal))
        {// superfluous auto-generated transforms.
          out0 = buildTerm(arena, typer, in->body, goal);
          recursed = true;
        }
        else
        {
          eq_proof = newComputation_(arena, goal, norm_goal);
          new_goal = norm_goal;
          rewrite_path = 0;
        }
      }
      else if ((new_goal = buildTerm(arena, typer, in->new_goal, holev)))
      {
        CompareTerms compare = compareTerms(arena, goal, new_goal);
        if (compare.result == Trinary_True)
          parseError(in0, "new goal is exactly the same as current goal");
        else
        {
          rewrite_path = compare.diff_path;
          Term *from = subExpressionAtPath(goal, compare.diff_path);
          Term *to   = subExpressionAtPath(new_goal, compare.diff_path);

          HintDatabase *hints = 0;
          if (in->hint)
          {
            b32 is_global_identifier = false;
            if (Identifier *ident = castAst(in->hint, Identifier))
            {
              if (!lookupLocalName(typer, &ident->token))
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

            if (!is_global_identifier)
            {
              if ((eq_proof = buildTerm(arena, typer, in->hint, holev).term))
              {
                hints = addHint(temp_arena, hints, eq_proof);
              }
            }
          }

          // TODO: using "temp_arena" here might be dangerous, what can we do?
          Term *lr_eq = newEquality(temp_arena, from, to);
          Term *rl_eq = newEquality(temp_arena, to, from);

          Solver solver = Solver{.arena=arena, .typer=typer, .local_hints=hints, .use_global_hints=true};
          if (!(eq_proof = solveGoal(&solver, lr_eq)))
          {
            if ((eq_proof = solveGoal(&solver, rl_eq)))
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
        if (Term *body = buildTerm(arena, typer, in->body, new_goal))
        {
          out0 = newRewrite(arena, eq_proof, body, rewrite_path, right_to_left);
        }
      }

      if (in->print_proof && eq_proof)
      {
        print(0, eq_proof);
        print(0, "\n");
      }
    } break;

    case Ast_Let:
    {
      Let  *in = castAst(in0, Let);
      Term *type_hint = holev;
      if (in->type && in->type->cat != Ast_NormalizeMeAst)
      {
        if (Term *type = buildTerm(arena, typer, in->type, holev).term)
          type_hint = type;
      }
      if (noError())
      {
        if (Term *build_rhs = buildTerm(arena, typer, in->rhs, type_hint).term)
        {
          Term *rhs = build_rhs;
          Term *rhs_type = type_hint;
          if (type_hint->cat == Term_Hole)
            rhs_type = getType(rhs);
            
          if (in->type)
          {// type coercion
            if (NormalizeMeAst *in_type = castAst(in->type, NormalizeMeAst))
            {
              Term *norm_rhs_type = normalize(arena, typer, rhs_type, in_type->name_to_unfold);
              if (checkFlag(in->flags, AstFlag_Generated) &&
                  equal(rhs_type, norm_rhs_type))
              {// superfluous auto-generated transforms.
                out0 = buildTerm(arena, typer, in->body, goal);
                recursed = true;
              }
              else
              {
                Term *computation = newComputation_(arena, norm_rhs_type, rhs_type);
                rhs_type = norm_rhs_type;
                rhs = newRewrite(arena, computation, build_rhs, 0, false);
                assert(equal(getType(rhs), rhs_type));
              }
            }
          }

          if (!recursed)
          {
            Token *token = &in0->token;
            FunctionAst *lambda = newAst(temp_arena, FunctionAst, token);
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
            lambda->signature = signature;

            Ast *rhs_ast = synthesizeAst(arena, rhs, token);

            CompositeAst *com = newAst(arena, CompositeAst, token);
            allocateArray(temp_arena, param_count, com->args);
            com->op        = &lambda->a;
            com->arg_count = param_count;
            com->args[0]   = rhs_ast;

            out0 = buildTerm(arena, typer, &com->a, goal);
            recursed = true;
          }
        }
      }
      assert(!out0 || getType(out0));
    } break;

    case Ast_ForkAst:
    {// no need to return value since nobody uses the value of a fork
      ForkAst *fork = castAst(in0, ForkAst);
      out0 = buildFork(arena, typer, fork, goal);
      recursed = true;
      assert(!out0 || getType(out0));
    } break;

    case Ast_UnionAst:
    {
      UnionAst *uni = castAst(in0, UnionAst);
      out0 = buildUnion(arena, typer, uni, 0);
      assert(!out0 || getType(out0));
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
        proposition = buildTerm(temp_arena, typer, in->proposition, holev).term;

      if (noError())
      {
        out0 = seekGoal(arena, typer, proposition);
        if (!out0)
          parseError(in0, "cannot find a matching proof in scope");
      }
      assert(!out0 || getType(out0));
    } break;

    case Ast_OverloadAst:
    {
      OverloadAst *in = castAst(in0, OverloadAst);
      if (GlobalBinding *lookup = lookupGlobalName(&in->function_name))
      {
        if (Term *distinguisher = buildTerm(temp_arena, typer, in->distinguisher, holev).term)
        {
          out0 = getOverloadFromDistinguisher(lookup, distinguisher);
          if (!out0)
            parseError(in0, "found no overload corresponding to distinguisher");
        }
      }
      assert(!out0 || getType(out0));
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// typecheck if needed
    Term *actual = getType(out0);
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
      print(error_buffer, typer->scope);
      attach("scope", endString(start));

      start = startString(error_buffer);
      printDataMap(error_buffer, typer);
      attach("data_map", endString(start));

      setErrorFlag(ErrorGoalAttached);
    }
  }
  else
  {
    assert(out0);
  }
  return BuildTerm{.term=out0};
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

    Term *subject_type = getType(subject.term);
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
  Term *from = right_to_left ? lhs : rhs;
  Term *to   = right_to_left ? rhs : lhs;
  Term *type = rewriteTerm(arena, from, to, path, getType(body));

  Rewrite *out = newTerm(arena, Rewrite, type);
  out->eq_proof      = eq_proof;
  out->body          = body;
  out->path          = path;
  out->right_to_left = right_to_left;
  return &out->t;
}

inline BuildTerm
parseExpressionAndBuild(MemoryArena *arena, LocalBindings *bindings, Term *expected_type)
{
  BuildTerm out = {};
  if (Ast *ast = parseExpression(arena))
  {
    Typer env = {};
    env.bindings = bindings;
    out = buildTerm(arena, &env, ast, expected_type);
  }
  return out;
}

inline BuildTerm
parseExpressionAndBuild(MemoryArena *arena)
{
  return parseExpressionAndBuild(arena, 0, holev);
}

struct NormList {
  i32          count;
  Identifier **items;
};

// todo No need to normalize a fork if that fork contains other forks inside.
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
          new_body->type  = &newAst(arena, NormalizeMeAst, &item->token)->a;
          new_body->body  = body;
          setFlag(&new_body->flags, AstFlag_Generated);
          body = &new_body->a;
        }
        GoalTransform *new_body = newAst(arena, GoalTransform, &body->token);
        new_body->new_goal = &newAst(arena, NormalizeMeAst, &body->token)->a;
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

internal FunctionAst *
parseGlobalFunction(MemoryArena *arena, Token *name, b32 is_theorem)
{
  FunctionAst *out = newAst(arena, FunctionAst, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpression(arena))
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
            norm_list.items = pushArray(temp_arena, DEFAULT_MAX_LIST_LENGTH, Identifier*);
            for (; noError(); )
            {
              if (optionalChar(')'))
                break;
              else if (requireIdentifier("expect auto-normalized parameter"))
              {
                // todo handle unbound identifier: all names in the norm list
                // should be in the function signature.
                Token *name = lastToken();
                i32 norm_i = norm_list.count++;
                assert(norm_i < DEFAULT_MAX_LIST_LENGTH);
                norm_list.items[norm_i] = newAst(arena, Identifier, name);
                if (!optionalChar(','))
                {
                  requireChar(')');
                  break;
                }
              }
            }
          }
          popContext();
        }
        else if (optionalCategory(Token_Directive_hint))
        {
          setFlag(&out->function_flags, FunctionFlag_is_global_hint);
        }
        else if (optionalCategory(Token_Directive_no_apply))
        {
          // todo: we can automatically infer this!
          setFlag(&out->function_flags, FunctionFlag_no_apply);
        }
        else if (optionalCategory(Token_Directive_no_print_as_binop))
        {
          setFlag(&out->function_flags, FunctionFlag_no_print_as_binop);
        }
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
  Ast *subject = parseExpression(arena);
  if (requireChar('{', "to open the typedef body"))
  {
    Token *ctors = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Token);
    Ast **bodies = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Ast*);

    i32 actual_case_count = 0;
    for (b32 stop = false;
         !stop && hasMore();)
    {
      if (optionalChar('}'))
        stop = true;
      else
      {
        pushContext("fork case: CASE: BODY");
        i32 input_case_i = actual_case_count++;
        Token ctor = nextToken();
        if (isIdentifier(&ctor))
          ctors[input_case_i] = ctor;
        else
          tokenError(&ctor, "expected a constructor name");

        optionalChar(':');  // just decoration
        if (Ast *body = parseSequence(arena, false))
        {
          bodies[input_case_i] = body;
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
      out = newAst(arena, ForkAst, &token);
      out->a.token    = token;
      out->subject    = subject;
      out->case_count = actual_case_count;
      out->bodies     = bodies;
      out->ctors      = ctors;
    }
  }

  return &out->a;
}

internal ArrowAst *
parseArrowType(MemoryArena *arena, b32 is_struct)
{
  ArrowAst *out = 0;
  i32      param_count = 0;
  String  *param_names;
  Ast    **param_types;
  u32     *param_flags;
  Token marking_token = peekToken();
  char begin_arg_char = '(';
  char end_arg_char   = ')';
  if (requireChar(begin_arg_char))
  {
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_names, true);
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_types, true);
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, param_flags, true);

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
        i32 param_i = param_count++;
        assert(param_i < DEFAULT_MAX_LIST_LENGTH);
        if (optionalChar('$'))
        {
          setFlag(&param_flags[param_i], ParameterFlag_Inferred);
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
            if (Ast *param_type = parseExpression(arena))
            {
              param_types[param_i] = param_type;
              if (typeless_run)
              {
                for (i32 offset = 1; offset <= typeless_run; offset++)
                  param_types[param_i - offset] = param_type;
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
          param_names[param_i] = param_name;
        else
        {
          *global_tokenizer = tk_save;
          pushContext("anonymous parameter");
          Token anonymous_parameter_token = global_tokenizer->last_token;
          if (Ast *param_type = parseExpression(arena))
          {
            param_types[param_i] = param_type;
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
      if (typeless_run)
      {
        tokenError(&typeless_token, "please provide types for all parameters");
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
        if (Ast *return_type = parseExpression(arena))
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

internal UnionAst *
parseUnion(MemoryArena *arena)
{
  UnionAst *uni = newAst(arena, UnionAst, lastToken());

  if (peekNextChar() == ('('))
  {
    uni->params = parseArrowType(arena, true);
  }

  if (requireChar('{'))
  {
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, uni->structs);
    allocateArray(arena, DEFAULT_MAX_LIST_LENGTH, uni->ctor_names);
    while (noError())
    {
      if (optionalChar('}'))
        break;
      else
      {
        i32 ctor_i = uni->ctor_count++;
        Token ctor_name = nextToken();
        uni->ctor_names[ctor_i] = ctor_name;
        if (isIdentifier(&ctor_name))
        {
          Token maybe_paren = peekToken();
          if (equal(maybe_paren.string, "("))
          {// subtype
            pushContext("constructor(FIELD: TYPE ...)");
            {
              if (ArrowAst *struc = parseArrowType(arena, true))
              {
                uni->structs[ctor_i] = struc;
              }
            }
            popContext();
          }
          else
          {// atomic constructor
            ArrowAst *signature = newAst(arena, ArrowAst, &ctor_name);
            uni->structs[ctor_i] = signature;  // empty arrow: no parameter, no output.
          }
        }
        else
          tokenError("expected an identifier as constructor name");

        if (!optionalChar(','))
        {
          requireChar('}');
          break;
        }
      }
    }
  }
  
  return uni;
}

forward_declare internal Term *
buildUnion(MemoryArena *arena, Typer *typer, UnionAst *in, Token *global_name)
{
  Union *uni = newTerm(arena, Union, builtin_Set);
  ParameterizedUnion *puni = 0;
  i32 ctor_count = in->ctor_count;
  uni->ctor_count = ctor_count;
  uni->ctor_names = copyArray(arena, ctor_count, in->ctor_names);
  allocateArray(arena, ctor_count, uni->structs);

  Arrow *uni_params = 0;
  if (in->params)
  {
    assert(global_name);
    Term *uni_params0 = buildTerm(arena, typer, &in->params->a, holev);
    uni_params = castTerm(uni_params0, Arrow);
  }

  if (noError())
  {
    if (global_name)
    {
      // note: bind the type first to support recursive data structure.
      Term *term_to_bind = &uni->t;
      if (uni_params)
      {
        Arrow *signature       = copyStruct(arena, uni_params);
        signature->output_type = builtin_Set;
        puni       = newTerm(arena, ParameterizedUnion, &signature->t);
        puni->body = uni;
        uni->punion = puni;
        term_to_bind = &puni->t;
      }
      addGlobalBinding(global_name, term_to_bind);
    }

    if (uni_params)
      introduceSignature(typer, uni_params, true);

    for (i32 ctor_i=0; noError() && (ctor_i < ctor_count); ctor_i++)
    {
      if (Term *struc0 = buildTerm(arena, typer, &in->structs[ctor_i]->a, holev).term)
      {
        Arrow *struc = castTerm(struc0, Arrow);
        uni->structs[ctor_i] = struc;

        if (global_name)
        {
          Term *term_to_bind = 0;
          if (uni_params)
          {
            i32 added_count = uni_params->param_count;
            Arrow *augmented        = copyStruct(arena, struc);
            augmented->param_count += added_count;
            allocateArray(arena, augmented->param_count, augmented->param_names);
            allocateArray(arena, augmented->param_count, augmented->param_types);
            allocateArray(arena, augmented->param_count, augmented->param_flags);
            for (i32 param_i=0; param_i < added_count; param_i++)
            {
              augmented->param_names[param_i] = uni_params->param_names[param_i];
              augmented->param_types[param_i] = uni_params->param_types[param_i];
              augmented->param_flags[param_i] = uni_params->param_flags[param_i] | ParameterFlag_Inferred;  // todo actually you can't infer the union parameter in case there's no arg (f.ex nil Nat), so we need to automatically do get the flag
            }
            for (i32 param_i=0; param_i < struc->param_count; param_i++)
            {
              augmented->param_names[added_count+param_i] = struc->param_names[param_i];
              augmented->param_types[added_count+param_i] = struc->param_types[param_i];
              augmented->param_flags[added_count+param_i] = struc->param_flags[param_i];
            }

            ParameterizedConstructor *pctor = newTerm(arena, ParameterizedConstructor, &augmented->t);
            pctor->punion                   = puni;
            pctor->index                    = ctor_i;
            pctor->param_count              = added_count;
            term_to_bind = &pctor->t;
          }
          else
          {
            Term *ctor = newConstructor(arena, uni, ctor_i);
            term_to_bind = ctor;
            if (struc->param_count == 0)
              term_to_bind = newComposite(arena, ctor, 0, 0);
          }

          addGlobalBinding(&uni->ctor_names[ctor_i], term_to_bind);
        }
      }
    }
    if (uni_params)
      unwindBindingsAndScope(typer);
  }

  if (noError())
  {
    assert(uni || puni);
  }
  else
  {
    uni  = 0;
    puni = 0;
  }
  if (puni) return &puni->t;
  else      return &uni->t;
}

inline CtorAst *
parseCtor(MemoryArena *arena)
{
  CtorAst *out = newAst(arena, CtorAst, &global_tokenizer->last_token);
  if (requireChar('['))
  {
    out->ctor_i = parseInt32();
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
    seek->proposition = parseExpression(arena);
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
        out->distinguisher = parseExpression(arena);
      }
    }
    requireChar(')');
  }
  if (hasError()) out = 0;
  return &out->a;
}

internal Ast *
parseFunctionExpression(MemoryArena *arena)
{
  // cutnpaste from "parseGlobalFunction"
  FunctionAst *out = newAst(arena, FunctionAst, lastToken());

  if (Ast *signature0 = parseExpression(arena))
  {
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      if (Ast *body = parseSequence(arena))
      {
        out->body      = body;
        out->signature = signature;
      }
    }
    else
      parseError(signature0, "function definition requires an arrow type");
  }

  NULL_WHEN_ERROR(out);
  return &out->a;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  Ast *operand = 0;
  Token token = nextToken();
  switch (token.cat)
  {
    case '_':
    {
      operand = newAst(arena, Hole, &token);
    } break;

    case '(':
    {
      operand = parseExpression(arena);
      requireChar(')');
    } break;

    case Token_Keyword_fn:
    {
      operand = parseFunctionExpression(arena);
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

    case Token_Keyword_overload:
    {
      operand = parseOverload(arena);
    } break;

    default:
    {
      tokenError("expected start of expression");
    }
  }

  while (hasMore())
  {
    if (optionalChar('('))
    {// function call syntax, let's keep going
      Ast *op = operand;
      Ast **args = pushArray(arena, DEFAULT_MAX_LIST_LENGTH, Ast*);
      CompositeAst *new_operand = newAst(arena, CompositeAst, &op->token);
      new_operand->op        = op;
      new_operand->arg_count = 0;
      new_operand->args      = args;
      operand = &new_operand->a;
      while (hasMore())
      {
        if (optionalChar(')'))
          break;
        else
        {
          i32 arg_id = new_operand->arg_count++;
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
            if ((args[arg_id] = parseExpression(arena)))
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
    }
    else if (optionalChar('.'))
    {// member accessor
      AccessorAst *accessor = newAst(arena, AccessorAst, &global_tokenizer->last_token);
      accessor->record      = operand;
      if (requireIdentifier("expected identifier as field name"))
      {
        accessor->field_name = *lastToken();
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
  if (equal(nextToken(tk), '('))
    if (eatUntilMatchingPair(tk))
      out = (nextToken(tk).cat == Token_Arrow);
  return out;
}

inline b32
seesLambda()
{// todo we don't allow naming parameters in here yet
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (equal(nextToken(tk), '_'))
  {
    if (nextToken(tk).cat == Token_StrongArrow)
      out = true;
  }
  return out;
}

internal FunctionAst *
parseLambda(MemoryArena *arena)
{
  pushContext("lambda: _ => {SEQUENCE}");
  nextToken(); nextToken();
  FunctionAst *out = newAst(arena, FunctionAst, &global_tokenizer->last_token);
  out->body = parseSequence(arena);
  popContext();
  return out;
}

internal Ast *
parseExpressionMain(MemoryArena *arena, ParseExpressionOptions opt)
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
            if (Ast *recurse = parseExpressionMain(arena, opt1))
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
parseExpression(MemoryArena *arena)
{
  return parseExpressionMain(arena, ParseExpressionOptions{});
}

inline void
addGlobalHint(Function *fun)
{
  HintDatabase *new_hint = pushStruct(global_state.top_level_arena, HintDatabase);
  new_hint->head = &fun->t;
  new_hint->tail  = global_state.hints;
  global_state.hints = new_hint;
}

// todo :build-global-function-vs-local-function
internal Function *
buildGlobalFunction(MemoryArena *arena, FunctionAst *in)
{
  pushContext(in->token.string, true);
  Function *out = 0;
  Typer typer_ = {};
  auto  typer  = &typer_;

  if (BuildTerm build_signature = buildTerm(arena, typer, &in->signature->a, holev))
  {
    Arrow *signature = castTerm(build_signature.term, Arrow);
    out = newTerm(arena, Function, build_signature.term);
    out->body           = &dummy_function_being_built;
    out->function_flags = in->function_flags;

    // NOTE: add binding first to support recursion
    addGlobalBinding(&in->a.token, &out->t);

    if (noError())
    {
      introduceSignature(typer, signature, true);
      if (BuildTerm body = buildTerm(arena, typer, in->body, signature->output_type))
      {
        out->body = body.term;
        if (checkFlag(in->function_flags, FunctionFlag_is_global_hint))
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

  Token token_ = nextToken(); 
  Token *token = &token_;
  while (hasMore())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
    error_buffer_ = subArena(temp_arena, 2048);
#endif

    Typer  empty_env_ = {};
    Typer *empty_env  = &empty_env_;

    switch (token_.cat)
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
               file_list = file_list->tail)
          {
            if (equal(file_list->head_path, load_path))
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
          tokenError(token, "#should_fail activated");
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
        if (BuildTerm expr = parseExpressionAndBuild(temp_arena))
          normalize(arena, empty_env, expr.term);
      } break;

      case Token_Keyword_print:
      {
        u32 flags = PrintFlag_Detailed|PrintFlag_PrintType;
        if (optionalString("lock_detailed"))
          setFlag(&flags, PrintFlag_LockDetailed);
        if (BuildTerm expr = parseExpressionAndBuild(temp_arena))
        {
          Term *norm = normalize(arena, 0, expr.term);
          print(0, norm, {.flags=flags});
          print(0, "\n");
        }
      } break;

      case Token_Keyword_print_raw:
      {
        if (auto parsing = parseExpressionAndBuild(temp_arena))
          print(0, parsing.term, {.flags = (PrintFlag_Detailed     |
                                            PrintFlag_LockDetailed |
                                            PrintFlag_PrintType)});
        print(0, "\n");
      } break;

      case Token_Keyword_print_ast:
      {
        if (Ast *exp = parseExpression(temp_arena))
          print(0, exp, {.flags = PrintFlag_Detailed});
        print(0, "\n");
      } break;

      case Token_Keyword_check:
      {
        pushContext("check TERM: TYPE");
        Term *expected_type = holev;
        if (Ast *ast = parseExpression(temp_arena))
        {
          if (optionalChar(':'))
          {
            if (BuildTerm type = parseExpressionAndBuild(temp_arena))
              expected_type = type.term;
          }
          if (noError())
            buildTerm(temp_arena, empty_env, ast, expected_type);
        }
        popContext();
      } break;

      case Token_Keyword_check_truth:
      {
        if (Term *goal = parseExpressionAndBuild(temp_arena).term)
        {
          b32 goal_valid = false;
          if (Composite *eq = castTerm(goal, Composite))
          {
            if (eq->op == builtin_equal)
            {
              goal_valid = true;
              Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
              Term *rhs = normalize(temp_arena, empty_env, eq->args[2]);
              if (!equal(lhs, rhs))
              {
                tokenError(token, "equality cannot be proven by computation");
                Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
                attach("lhs", lhs);
                attach("rhs", rhs);
              }
            }
          }
          if (!goal_valid)
          {
            tokenError(token, "computation can only prove equality");
            attach("got", goal);
          }
        }
      } break;

      case Token_Keyword_algebra_declare:
      {
        if (Term *type = parseExpressionAndBuild(arena).term)
        {
          AlgebraDatabase *new_algebras = pushStruct(global_state.top_level_arena, AlgebraDatabase);
          new_algebras->tail            = global_state.algebras;
          global_state.algebras = new_algebras;

          Algebra *algebra = &new_algebras->head;
          algebra->type = type;
          const i32 function_count = 7;
          const char *function_names[function_count] = {
            "+", "addCommutative", "addAssociative",
            "*", "mulCommutative", "mulAssociative",
            "mulDistributive",
          };
          Term **functions[function_count] = {
            &algebra->add, &algebra->addCommutative, &algebra->addAssociative,
            &algebra->mul, &algebra->mulCommutative, &algebra->mulAssociative,
            &algebra->mulDistributive,
          };

          for (i32 i=0; i < function_count && noError(); i++)
          {
            if (Term *function = getOverloadFromDistinguisher(token, function_names[i], type))
              *functions[i] = function;
          }
        }
      } break;

      default:
      {
        if (isIdentifier(token))
        {
          Token after_name = nextToken();
          if (isIdentifier(&after_name) &&
              areSequential(token, &after_name))
          {// token combination
            token_.string.length += after_name.string.length;
            after_name = nextToken();
          }

          switch (after_name.cat)
          {
            case Token_ColonEqual:
            {
              pushContext("constant definition: CONSTANT := VALUE;");
              if (BuildTerm rhs = parseExpressionAndBuild(arena))
              {
                addGlobalBinding(token, rhs.term);
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
                  buildUnion(arena, empty_env, ast, token);
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
                if (FunctionAst *fun = parseGlobalFunction(arena, token, is_theorem))
                  buildGlobalFunction(arena, fun);
              }
            } break;

            case ':':
            {
              if (BuildTerm type = parseExpressionAndBuild(arena))
              {
                if (requireCategory(Token_ColonEqual, "require :=, syntax: name : type := value"))
                {
                  if (BuildTerm rhs = parseExpressionAndBuild(arena, 0, type.term))
                    addGlobalBinding(token, rhs.term);
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
        tokenError(token, "#should_fail active but didn't fail");
      else if (checkErrorFlag(ErrorTypecheck))
        wipeError();
    }

    if (hasMore())
    {
      token_ = nextToken();
      while (equal(token_.string, ";"))
      {// todo: should we do "eat all semicolons after the first one?"
        token_ = nextToken();
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
    new_file_list->head_path    = input_path.path;
    new_file_list->head_content = read.content;
    new_file_list->tail          = state->file_list;
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
      printf("\n\n");
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
beginInterpreterSession(MemoryArena *top_level_arena, char *initial_file)
{
  DEBUG_OFF;
  // :global_state_cleared_at_startup Clear global state as we might run the
  // interpreter multiple times.
  auto arena = top_level_arena;
  global_state       = {};
  global_state.top_level_arena = arena;

  global_state.bindings = pushStruct(arena, GlobalBindings);  // :global-bindings-zero-at-startup because // :global_state_cleared_at_startup

  // NOTE: Atm we gotta create the builtins every interpreter session, since the
  // parsing depends on the global bindings, which resets every time. Since
  // aren't many sessions, this redundancy is fine, just ugly.
  {
    builtin_Type       = &newTerm(arena, Builtin, 0)->t;
    builtin_Type->type = builtin_Type; // NOTE: circular types
    addBuiltinGlobalBinding("Type", builtin_Type);

    builtin_Set = &newTerm(arena, Builtin, builtin_Type)->t;
    addBuiltinGlobalBinding("Set", builtin_Set);

    Tokenizer builtin_tk = newTokenizer(toString("<builtin_not_a_real_dir>"), 0);
    global_tokenizer = &builtin_tk;
    builtin_tk.at = "($A: Set, a,b: A) -> Set";
    Term *equal_type = parseExpressionAndBuild(arena).term; 
    assert(noError());
    builtin_equal = &newTerm(arena, Builtin, equal_type)->t;
    addBuiltinGlobalBinding("=", builtin_equal);

    builtin_tk.at = "($A: Type, a,b: A) -> Set";
    Term *type_equal_type = parseExpressionAndBuild(arena).term; 
    assert(noError());
    builtin_type_equal = &newTerm(arena, Builtin, type_equal_type)->t;

    builtin_tk.at = "union {}";
    Term *builtin_False0 = parseExpressionAndBuild(arena).term;
    builtin_False = &castTerm(builtin_False0, Union)->t;
    addBuiltinGlobalBinding("False", builtin_False);

    builtin_tk.at = R""""(fn ($A: Set, $a, $b, $c: A, a=b, b=c) -> a=c
{=> b = c {seek(a=b)} seek}
)"""";
    builtin_eqChain = parseExpressionAndBuild(arena).term;
    assert(noError());
    addBuiltinGlobalBinding("eqChain", builtin_eqChain);

    resetArena(temp_arena);
  }

  FilePath input_path = platformGetFileFullPath(arena, initial_file);
  b32 success = interpretFile(&global_state, input_path, true);

  for (FileList *file_list = global_state.file_list;
       file_list;
       file_list = file_list->tail)
  {
    platformFreeFileMemory(file_list->head_content);
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

  assert(arrayCount(language_keywords) == Token_Keyword_END - Token_Keyword_START);
  assert(arrayCount(meta_directives)   == Token_Directive_END - Token_Directive_START);
  assert(arrayCount(language_tactics)  == Tactic_COUNT);

  void   *top_level_arena_base = (void*)teraBytes(2);
  size_t  top_level_arena_size = megaBytes(256);
  top_level_arena_base = platformVirtualAlloc(top_level_arena_base, top_level_arena_size);
  MemoryArena top_level_arena_ = newArena(top_level_arena_size, top_level_arena_base);
  MemoryArena *top_level_arena = &top_level_arena_;

  void   *temp_arena_base = (void*)teraBytes(3);
  size_t  temp_arena_size = megaBytes(2);
  temp_arena_base = platformVirtualAlloc(temp_arena_base, top_level_arena_size);
  temp_arena_ = newArena(temp_arena_size, temp_arena_base);

  char *files[] = {
    "../data/test.rea",
    "../data/z-slider.rea",
    "../data/natp-experiment.rea",
    "../data/z.rea",
  };
  for (i32 file_id=0; file_id < arrayCount(files); file_id++)
  {
    if (!beginInterpreterSession(top_level_arena, files[file_id]))
      success = false;
    resetArena(top_level_arena, true);
  }
  return success;
}

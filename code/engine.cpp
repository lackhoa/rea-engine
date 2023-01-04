/*
  General Todos: 
  - #cleanup Replace all token <-> string comparison with keyword checks.
  - #tool something that cleans up when it goes out of scope
  - Try to remove recursion, we pass a bunch of things in the signature and it's annoying to change.
  - #speed evaluating functions by substituting the body is really bad in case of "let"
  - make "computation" be a builtin
  - debug serial situation
  - clean up the data tree containing constructors
  - we're printing the stack every time we encounter an error, but the error might be recoverable so it's just wasted work. Either pass the intention down, or abandon the recoveriy route.
 */

#include "utils.h"
#include "memory.h"
#include "intrinsics.h"
#include "engine.h"
#include "tokenization.cpp"
#include "debug.h"

global_variable Builtins builtins;
global_variable Term dummy_function_being_built;
global_variable Term  holev_ = {.cat = Term_Hole};
global_variable Term *holev = &holev_;

global_variable EngineState global_state;

inline String
globalNameOf(Term *term)
{
  if (term->global_name)
    return term->global_name->string;
  else
    return {};
}

internal Term *
fillHole(MemoryArena *arena, Typer *env, Term *goal)
{
  Term *out = 0;
  if (Composite *eq = castTerm(goal, Composite))
  {
    if (eq->op == &builtins.equal->t)
    {
      Term *lhs_norm = normalize(temp_arena, env, eq->args[1]);
      Term *rhs_norm = normalize(temp_arena, env, eq->args[2]);
      if (equal(lhs_norm, rhs_norm))
      {
        getType(arena, env, eq->args[1]);
        getType(arena, env, eq->args[2]);
        out = newComputation(arena, eq->args[1], eq->args[2]);
      }
    }
  }
  return out;
}

inline Term *
newVariable(MemoryArena *arena, Token *name, i32 delta, i32 index)
{
  Variable *out = newTerm(arena, Variable, 0);
  out->name  = name->string;
  out->delta = delta;
  out->id = index;
  return &out->t;
}

inline Term *
newComposite(MemoryArena *arena, Term *op, i32 arg_count, Term **args)
{
  Composite *out = newTerm(arena, Composite, 0);
  out->op        = op;
  out->arg_count = arg_count;
  out->args      = args;
  return &out->t;
}

inline Term *
newEquality(MemoryArena *arena, Term *type, Term *lhs, Term *rhs)
{
  Composite *eq = newTerm(arena, Composite, &builtins.Set->t);
  allocateArray(arena, 3, eq->args);
  eq->op        = &builtins.equal->t;
  eq->arg_count = 3;
  eq->args[0]   = type;
  eq->args[1]   = lhs;
  eq->args[2]   = rhs;
  return &eq->t;
}

inline Term *
newEquality(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Term *lhs_type = getType(lhs);
  assert(lhs_type);
  return newEquality(arena, lhs_type, lhs, rhs);
}

// todo #typesafe error out when the sides don't match
forward_declare inline Term *
newComputation(MemoryArena *arena, Term *lhs, Term *rhs)
{
  Computation *out = newTerm(arena, Computation, 0);
  out->lhs = lhs;
  out->rhs = rhs;
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
    case AC_RewriteAst:
    case AC_Let:
    case AC_ForkAst:
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
deriveType(Constructor *ctor)
{
  if (ctor->type)
    return castTerm(ctor->type, Arrow);
  else
  {
    Arrow *signature = ctor->uni->ctor_signatures[ctor->id];
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
  deriveType(ctor);
  return ctor;
}

// todo this is a massive waste of time, maybe we can try using the data tree
// directly.
inline Composite *
makeFakeRecord(MemoryArena *arena, Term *parent, DataTree *tree)
{  
  Composite *record = 0;
  Constructor *ctor = newConstructor(arena, tree->uni, tree->ctor_id);  // todo need to rebase the union, no way this is correct
  Arrow *ctor_sig = getType(ctor);
  i32 param_count = ctor_sig->param_count;
  record = newTerm(arena, Composite, 0);
  record->op        = &ctor->t;
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term*);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = ctor_sig->param_names[field_id].string;
    Accessor *accessor = newTerm(arena, Accessor, 0);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    DataTree *member_tree = tree->members[field_id];
    if (member_tree)
      record->args[field_id] = &makeFakeRecord(arena, &accessor->t, member_tree)->t;
    else
      record->args[field_id] = &accessor->t;
  }
  return record;
}

inline String
getVarNameInScope(Typer *env, DataMap *map)
{
  String out = {};
  for (Scope *scope = env->scope; scope; scope=scope->outer)
  {
    if (scope->depth == map->depth)
    {
      out = scope->first->param_names[map->index].string;
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

// todo This is an even bigger waste of time, the worst thing is I don't know
// how to get the type of a struct, does anybody know? Pretty please?
inline Composite *
makeShallowRecord(MemoryArena *arena, Term *parent, Union *uni, i32 ctor_id)
{
  Composite *record = newTerm(arena, Composite, 0);
  Arrow *ctor_sig = uni->ctor_signatures[ctor_id];
  i32 param_count = ctor_sig->param_count;
  record->op        = &newConstructor(arena, uni, ctor_id)->t;  // todo you can't use "uni"
  record->arg_count = param_count;
  record->args      = pushArray(arena, param_count, Term *);
  for (i32 field_id=0; field_id < param_count; field_id++)
  {
    String field_name = ctor_sig->param_names[field_id].string;
    Accessor *accessor = newTerm(arena, Accessor, 0);
    accessor->record     = parent;
    accessor->field_id   = field_id;
    accessor->field_name = field_name;
    record->args[field_id] = &accessor->t;
  }
  return record;
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
  i32 ctor_arg_count = uni->ctor_signatures[ctor_id]->param_count;
  tree->uni          = uni;
  tree->ctor_id      = ctor_id;
  tree->member_count = ctor_arg_count;
  tree->members      = pushArray(arena, ctor_arg_count, DataTree*, true);
}

inline i32 getScopeDepth(Typer *env) {return (env && env->scope) ? env->scope->depth : 0;}

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
    if (Union *uni = castTerm(getType(temp_arena, env, in0), Union))
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

inline Term *
deriveType(MemoryArena *arena, Typer *env, Term *in0)
{
  i32 UNUSED_VAR serial = global_debug_serial++;
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
        
        assert(scope->depth == (env->scope->depth - in->delta));
        out0 = scope->first->param_types[in->id];
        out0 = rebase(arena, out0, in->delta);

        assert(out0);
      } break;

      case Term_Composite:
      {
        Composite *in = castTerm(in0, Composite);
        if (Constructor *ctor = castTerm(in->op, Constructor))
          out0 = &ctor->uni->t;
        else
        {
          Term *op_type0 = deriveType(arena, env, in->op);
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
        out0 = newEquality(arena, in->lhs, in->rhs);
      } break;

      case Term_Accessor:
      {
        Accessor *in = castTerm(in0, Accessor);
        Composite *record = 0;

        Arrow *signature = 0;
        if ((record = castTerm(in->record, Composite)))
        {
          if (Constructor *ctor = castTerm(record->op, Constructor))
            signature = getType(ctor);
          else
            record = 0;  // back out since it's not an actual record.
        }

        if (!record)
        {
          Constructor ctor = getConstructor(env, in->record);
          if (ctor.uni)
          {
            signature = ctor.uni->ctor_signatures[ctor.id];
            record = makeShallowRecord(arena, in->record, ctor.uni, ctor.id);
          }
        }

        out0 = evaluate(arena, record->args, signature->param_types[in->field_id]);
      } break;

      case Term_Rewrite:
      {
        Rewrite *in = castTerm(in0, Rewrite);
        auto [lhs, rhs] = getEqualitySides(deriveType(arena, env, in->eq_proof));
        Term *rewrite_to = in->right_to_left ? rhs : lhs;
        out0 = rewriteTerm(arena, rewrite_to, in->path, getType(arena, env, in->body));
      } break;

      case Term_Constructor:
      {
        Constructor *ctor = castTerm(in0, Constructor);
        out0 = &deriveType(ctor)->t;
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
getType(MemoryArena *arena, Typer *env, Term *in0)
{
  return deriveType(arena, env, in0);
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

// todo #cleanup a lot of the copies are unnecessary, we must think about where
// we can put stack values. and whether to have stack values at all.
//
// todo #cleanup I think this is now only for the global overloads typecheck for
// composites?  If so then just copy the composite, no need to deepcopy
internal Ast *
deepCopy(MemoryArena *arena, Ast *in0)
{
  Ast *out0 = 0;
  switch (in0->cat)
  {
    case AC_Hole:
    case AC_Identifier:
    {out0 = in0;} break;

    case AC_CompositeAst:
    {
      CompositeAst *in = castAst(in0, CompositeAst);
      CompositeAst *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, out->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
      {
        out->args[id] = deepCopy(arena, in->args[id]);
      }
      out0 = &out->a;
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      ArrowAst *out = copyStruct(arena, in);
      out->output_type = deepCopy(arena, in->output_type);
      allocateArray(arena, out->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
      {
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      }
      out0 = &out->a;
    } break;

    case AC_Let:
    {
      Let *in = castAst(in0, Let);
      Let *out = copyStruct(arena, in);
      out->rhs = deepCopy(arena, in->rhs);
      out0 = &out->a;
    } break;

    case AC_RewriteAst:
    {
      RewriteAst *in = castAst(in0, RewriteAst);
      RewriteAst *out = copyStruct(arena, in);
      out->eq_proof_hint = deepCopy(arena, in->eq_proof_hint);
      out0 = &out->a;
    } break;

    case AC_AccessorAst:
    {
      AccessorAst *in = castAst(in0, AccessorAst);
      AccessorAst *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->a;
    } break;

    invalidDefaultCase;
  }
  return out0;
}

internal Term *
deepCopy(MemoryArena *arena, Term *in0)
{
  Term *out0 = 0;
  switch (in0->cat)
  {
    case Term_Composite:
    {
      Composite *in  = castTerm(in0, Composite);
      Composite *out = copyStruct(arena, in);
      out->op = deepCopy(arena, in->op);
      allocateArray(arena, in->arg_count, out->args);
      for (i32 id=0; id < in->arg_count; id++)
        out->args[id] = deepCopy(arena, in->args[id]);
      out0 = &out->t;
    } break;

    case Term_Arrow:
    {
      Arrow *in  = castTerm(in0, Arrow);
      Arrow *out = copyStruct(arena, in);
      allocateArray(arena, in->param_count, out->param_types);
      for (i32 id=0; id < in->param_count; id++)
        out->param_types[id] = deepCopy(arena, in->param_types[id]);
      out->output_type = deepCopy(arena, in->output_type);
      out0 = &out->t;
    } break;

    case Term_Accessor:
    {
      Accessor *in  = castTerm(in0, Accessor);
      Accessor *out = copyStruct(arena, in);
      out->record = deepCopy(arena, in->record);
      out0 = &out->t;
    } break;

    case Term_Builtin:
    case Term_Union:
    case Term_Constructor:
    case Term_Function:
    {out0 = in0;} break;

    default: todoIncomplete;
  }
  return out0;
}

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

i32 global_variable debug_indentation;
forward_declare inline void debugIndent()
{
  debug_indentation++;
  for (i32 id = 0; id < debug_indentation; id++)
    dump(" ");
}

forward_declare inline void debugDedent()
{
  for (i32 id = 0; id < debug_indentation; id++)
    dump(" ");
  debug_indentation--;
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
  else if (equal(op, "<") || equal(op, ">") || equal(op, "=?"))
    out = 55;
  else if (equal(op, "|")
           || equal(op, "+")
           || equal(op, "-"))
    out = 60;
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
      b32 print_all_arguments = global_debug_mode && DEBUG_print_all_arguments;
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

forward_declare internal char *
print(MemoryArena *buffer, Ast *in0, PrintOptions opt)
{// printAst
  char *out = buffer ? (char*)getNext(buffer) : 0;
  if (in0)
  {
    PrintOptions new_opt = opt;
    unsetFlag(&new_opt.flags, PrintFlag_Detailed);
    new_opt.indentation += 1;

    switch (in0->cat)
    {
      case AC_Hole:
      {print(buffer, "_");} break;

      case AC_SyntheticAst:
      {
        SyntheticAst *in = castAst(in0, SyntheticAst);
        print(buffer, in->term);
      } break;

      case AC_Identifier:
      {print(buffer, in0->token.string);} break;

      case AC_RewriteAst:
      {
        RewriteAst *in = castAst(in0, RewriteAst);
        print(buffer, "rewrite");
        print(buffer, in->path);
        print(buffer, " ");
        if (in->right_to_left) print(buffer, "<- ");
        print(buffer, in->eq_proof_hint, new_opt);
      } break;

      case AC_CompositeAst:
      {
        printComposite(buffer, in0, false, new_opt);
      } break;

      case AC_ForkAst:
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

      case AC_ArrowAst:
      {
        ArrowAst *in = castAst(in0, ArrowAst);
        print(buffer, "(");
        for (int param_id = 0;
             param_id < in->param_count;
             param_id++)
        {
          print(buffer, in->param_names[param_id].string);
          print(buffer, ": ");
          print(buffer, in->param_types[param_id], new_opt);
          if (param_id < in->param_count-1)
            print(buffer, ", ");
        }
        print(buffer, ") -> ");

        print(buffer, in->output_type, new_opt);
      } break;

      case AC_AccessorAst:
      {
        AccessorAst *in = castAst(in0, AccessorAst);
        print(buffer, in->record, new_opt);
        print(buffer, ".");
        print(buffer, in->field_name.string);
      } break;

      case AC_FunctionDecl: {print(buffer, "function decl");} break;

      case AC_Lambda: {print(buffer, "lambda");} break;

      case AC_Let:
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

      case AC_ComputationAst:
      {
        ComputationAst *computation = castAst(in0, ComputationAst);
        print(buffer, "computation: (");
        print(buffer, computation->lhs, new_opt);
        print(buffer, ") => (");
        print(buffer, computation->rhs, new_opt);
        print(buffer, ")");
      } break;

      case AC_UnionAst:
      {
        print(buffer, "<some union>");
      } break;

      case AC_DestructAst:
      {
        print(buffer, "<some destruct>");
      } break;

      case AC_CtorAst:
      {
        print(buffer, "<some ctor>");
      } break;

      case AC_SeekAst:
      {
        print(buffer, "<some seek>");
      } break;
    }
  }
  else
    print(buffer, "<NULL>");
  return out;
}

forward_declare internal char *
print(MemoryArena *buffer, Ast *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal char *
print(MemoryArena *buffer, Term *in0, PrintOptions opt)
{// mark: printTerm
  char *out = buffer ? (char*)getNext(buffer) : 0;
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
        print(buffer, in->name);
        if (global_debug_mode)
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
              print(buffer, &in->ctor_signatures[ctor_id]->t, new_opt);
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
          print(buffer, in->param_names[param_id].string);
          print(buffer, ": ");
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

  return out;
}

inline char *
print(MemoryArena *buffer, Scope *scopes)
{
  char *out = buffer ? (char*)getNext(buffer) : 0;
  print(buffer, "[");
  while (scopes)
  {
    auto scope = scopes->first;
    print(buffer, "(");
    for (int param_id = 0;
         param_id < scope->param_count;
         param_id++)
    {
      print(buffer, scope->param_names[param_id].string);
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
  return out;
}

inline void dump(Scope *stack) {print(0, stack);}
inline void dump(Typer *env) {dump("stack: "); dump(env->scope);}

forward_declare internal char *
print(MemoryArena *buffer, Term *in0)
{
  return print(buffer, in0, {});
}

forward_declare internal char *
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
isGround(Term *in0)
{
  if (in0->global_name)
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
        allocateArray(arena, in->ctor_count, out->ctor_signatures);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *rebased = rebaseMain(arena, &in->ctor_signatures[id]->t, delta, offset);
          out->ctor_signatures[id] = castTerm(rebased, Arrow);
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
apply(MemoryArena *arena, Term *op, Term **args)
{
  Term *out0 = 0;

#if DEBUG_LOG_apply
  i32 serial = global_debug_serial++;
  if (global_debug_mode)
  {debugIndent(); DUMP("apply(", serial, "): ", op, "(...)\n");}
#endif

  if (Function *fun = castTerm(op, Function))
  {// Function application
    if (fun->body != &dummy_function_being_built)
      out0 = evaluateAndNormalize(arena, args, fun->body);
  }
  else
  {
    // special casing for equality
    if (op == &builtins.equal->t)
    {// special case for equality
      Term *lhs = args[1];
      Term *rhs = args[2];
      Trinary compare = equalTrinary(lhs, rhs);
      // #hack to handle inconsistency
      if (compare == Trinary_False)
        out0 = &builtins.False->t;
    }
  }

#if DEBUG_LOG_apply
  if (global_debug_mode) {debugDedent(); DUMP("=> ", out0, "\n");}
#endif
  return out0;
}

internal Term *
evaluateMain(EvaluationContext *ctx, Term *in0)
{
  Term *out0 = 0;
  MemoryArena *arena = ctx->arena;

#if DEBUG_LOG_evaluate
  i32 serial = global_debug_serial++;
  if (global_debug_mode)
  {debugIndent(); DUMP("evaluate(", serial, "): ", in0, "\n");}
  assert(ctx->offset >= 0);
#endif

  if (in0->global_name)
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
          args[id] = evaluateMain(ctx, in->args[id]);

        if (ctx->normalize)
          out0 = apply(arena, op, args);

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

        b32 old_normalize = ctx->normalize;
        ctx->normalize = false;
        ctx->offset++;
        out->body = evaluateMain(ctx, in->body);
        ctx->offset--;
        ctx->normalize = old_normalize;

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
        b32 old_normalize = ctx->normalize;
        ctx->normalize = false;
        out->lhs = evaluateMain(ctx, in->lhs);
        out->rhs = evaluateMain(ctx, in->rhs);
        ctx->normalize = old_normalize;
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
        if (ctx->normalize)
        {
          Term *subject0 = evaluateMain(ctx, in->subject);
          if (Composite *subject = castTerm(subject0, Composite))
          {
            if (Constructor *ctor = castTerm(subject->op, Constructor))
              out0 = evaluateMain(ctx, in->bodies[ctor->id]);
          }
        }
        else
        {
          Fork *out = copyStruct(arena, in);
          out->subject = evaluateMain(ctx, in->subject);
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
        allocateArray(arena, in->ctor_count, out->ctor_signatures);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Arrow *signature = in->ctor_signatures[id];
          out->ctor_signatures[id] = castTerm(evaluateMain(ctx, &signature->t), Arrow);
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
  if (global_debug_mode) {debugDedent(); DUMP("=> ", out0, "\n");}
#endif

  assert(isSequenced(in0) || out0);
  return out0;
}

forward_declare inline Term *
evaluate(MemoryArena *arena, Term **args, Term *in0)
{
  EvaluationContext ctx = {.arena=arena, .args=args, .normalize=false};
  return evaluateMain(&ctx, in0);
}

forward_declare inline Term *
evaluateAndNormalize(MemoryArena *arena, Term **args, Term *in0)
{
  EvaluationContext ctx = {.arena=arena, .args=args, .normalize=true};
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
  i32 serial = global_debug_serial++;
  if (global_debug_mode)
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
        if (!lhs0->global_name && !rhs0->global_name)  // only support anonymous union compare rn, to avoid dealing with recursive structs
        {
          Union *lhs = castTerm(lhs0, Union);
          Union *rhs = castTerm(rhs0, Union);
          i32 ctor_count = lhs->ctor_count;
          if (rhs->ctor_count == ctor_count)
          {
            b32 found_mismatch = false;
            for (i32 id=0; id < ctor_count; id++)
            {
              if (!equal(&lhs->ctor_signatures[id]->t,
                         &rhs->ctor_signatures[id]->t))
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
  if (global_debug_mode)
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
          slot->next_hash_slot = pushStruct(global_state.arena, GlobalBinding, true);
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
  i32 serial = global_debug_serial++;
  if (global_debug_mode)
  {debugIndent(); DUMP("normalize(", serial, "): ", in0, "\n");}
#endif

  if (!in0->global_name)
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

        if (Term *app = apply(arena, norm_op, norm_args))
          out0 = app;
        else if (progressed)
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
          out0 = &makeFakeRecord(arena, in0, tree)->t;
      } break;

      case Term_Union:
      {
        Union *in  = castTerm(in0, Union);
        Union *out = copyStruct(arena, in);
        allocateArray(arena, in->ctor_count, out->ctor_signatures);
        for (i32 id=0; id < in->ctor_count; id++)
        {
          Term *signature = &in->ctor_signatures[id]->t;
          signature = normalizeMain(ctx, signature);
          out->ctor_signatures[id] = castTerm(signature, Arrow);
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
  if (global_debug_mode)
  {debugDedent(); dump("=> "); dump(out0); dump();}
#endif

  assert(isSequenced(in0) || out0);
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
addLocalBinding(Typer *env, Token *key, i32 var_id)
{
  auto lookup = lookupCurrentFrame(env->bindings, key->string, true);
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
      Token *name = signature->param_names + index;
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
    parseError(token, "identifier not found");
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
  Token *name_copy = copyStruct(global_state.arena, name);
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
  Token token = peekToken(tk);
  if (equal(&token, c))
  {
    out = true;
    nextToken(tk);
  }
  return out;
}

inline b32
optionalString(char *str, Tokenizer *tk=global_tokenizer)
{
  b32 out = false;
  Token token = peekToken(tk);
  if (equal(&token, str))
  {
    out = true;
    nextToken(tk);
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

  if (token->cat > TC_Directive_START && token->cat < TC_Directive_END)
    return true;

  switch (token->cat)
  {
    case TC_DoubleColon:
    case TC_ColonEqual:
    case TC_DoubleDash:
    case TC_StrongArrow:
      return true;
    default: {}
  }

  return false;
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

// todo We don't need "env", we only need the scope.
internal b32
unify(Typer *env, Stack *stack, Scope *lhs_scope, Term *lhs0, Term *goal0)
{
  b32 success = false;

  i32 UNUSED_VAR serial = global_debug_serial++;
#if DEBUG_LOG_unify
  if (global_debug_mode)
  {debugIndent(); DUMP("unify(", serial, ") ", lhs0, " with ", goal0, "\n");}
#endif

  switch (lhs0->cat)
  {
    case Term_Variable:
    {
      Variable *lhs = castTerm(lhs0, Variable);
      Stack *lookup_stack = stack;
      for (i32 delta=0; delta < lhs->delta; delta++)
      {
        lookup_stack = lookup_stack->outer;
      }
      if (Term *replaced = lookup_stack->items[lhs->id])
      {
        if (equal(replaced, goal0))
          success = true;
      }
      else
      {
        // todo cleanup
        for (i32 delta=0; delta < lhs->delta; delta++)
        {
          lhs_scope = lhs_scope->outer;
        }
        // todo the act of fetching lhs_type and goal_type should be the same!!!
        Term *lhs_type = lhs_scope->first->param_types[lhs->id];
        lhs_type = rebase(temp_arena, lhs_type, lhs->delta);
        Term *goal_type = getType(temp_arena, env, goal0);
        if (unify(env, stack, lhs_scope, lhs_type, goal_type))
        {
          // todo potential infinite loop with "Type"
          stack->items[lhs->id] = goal0;
          success = true;
        }
      }
    } break;

    case Term_Composite:
    {
      Composite *lhs = castTerm(lhs0, Composite);
      if (Composite *goal = castTerm(goal0, Composite))
      {
        if (unify(env, stack, lhs_scope, lhs->op, goal->op))
        {
          success = true;
          for (int id=0; id < lhs->arg_count; id++)
          {
            if (!unify(env, stack, lhs_scope, lhs->args[id], goal->args[id]))
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
      Arrow *lhs = castTerm(lhs0, Arrow);
      if (Arrow *goal = castTerm(goal0, Arrow))
      {
        if (lhs->param_count == goal->param_count)
        {
          Scope *new_lhs_scope = newScope(lhs_scope, lhs);
          env->scope = newScope(env->scope, goal);
          b32 failed = false;
          Stack *new_stack = newStack(temp_arena, stack, lhs->param_count);
          for (i32 id=0; id < lhs->param_count; id++)
          {
            if (!unify(env, new_stack, new_lhs_scope, lhs->param_types[id], goal->param_types[id]))
            {
              failed = true;
              break;
            }
          }
          if (!failed)
            success = true;
          unwindScope(env);
        }
      }
    } break;

    case Term_Function:
    case Term_Union:
    case Term_Constructor:
    case Term_Builtin:
    {
      success = equal(lhs0, goal0);
    } break;

    default:
    {
      todoIncomplete;
    } break;
  }

#if DEBUG_LOG_unify
  if (global_debug_mode)
  {debugDedent(); DUMP("=>(", serial, ") ", ((char *)(success ? "true\n" : "false\n")));}
#endif

  return success;
}

inline InferArgs
inferArgs(MemoryArena *arena, Typer *env, Term *op, Term *goal)
{
  Term **args = 0;
  b32 matches = false;
  if (Constructor *ctor = castTerm(op, Constructor))
  {
    if (equal(&ctor->uni->t, goal))
      matches = true;  // I guess we wouldn't know what the memberse are in the constructor case.
  }
  else if (Arrow *signature = castTerm(getType(op), Arrow))
  {
    Stack *stack = newStack(arena, 0, signature->param_count);
    Scope *lhs_scopes = newScope(0, signature);
    if (unify(env, stack, lhs_scopes, signature->output_type, goal))
    {
      matches = true;
      args = stack->items;
    }
  }
  return InferArgs{matches, args};
}

inline void
attachTerms(char *key, i32 count, Term **terms)
{
  MemoryArena buffer = subArena(temp_arena, 1024);
  attach(key, (char *)buffer.base);
  for (i32 id=0; id < count; id++)
  {
    print(&buffer, "\n");
    print(&buffer, terms[id]->type);
  }
  print(&buffer, "\0");
}

inline TermArray
getFunctionOverloads(Typer *env, Identifier *ident, Term *output_type_goal)
{
  TermArray out = {};
  if (GlobalBinding *slot = lookupGlobalNameSlot(ident->token.string, false))
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
        if (inferArgs(temp_arena, env, item, output_type_goal).matches)
          out.items[out.count++] = slot->items[slot_id];
      }
      if (out.count == 0)
      {
        parseError(&ident->a, "found no matching overload");
        attach("output_type", output_type_goal);
        attachTerms("available_overloads", slot->count, slot->items);
      }
    }
  }
  else
    parseError(&ident->a, "identifier not found");
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

  b32 stop = false;
  while (noError() && !stop)
  {
    Tokenizer tk_save = *global_tokenizer;
    Token token = nextToken();
    Ast *ast = 0;
    switch (token.cat)
    {
      case TC_Keyword_norm:
      {
        pushContext("norm [LOCAL_VARIABLE]");
        // todo this is confusing if we're at the end of the sequence
        if (optionalChar(';'))
        {// normalize goal
          RewriteAst *rewrite = newAst(arena, RewriteAst, &token);
          ast = &rewrite->a;
        }
        else
        {
          Token name = nextToken();
          if (isIdentifier(&name))
          {
            Let *let = newAst(arena, Let, &token);
            let->lhs  = name.string;
            let->rhs  = &newAst(arena, Identifier, &name)->a;
            let->type = LET_TYPE_NORMALIZE;
            ast = &let->a;
          }
          else
            parseError(&token, "syntax error");
        }
        popContext();
      } break;

      case TC_Keyword_rewrite:
      {
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);

        rewrite->right_to_left = false;
        Token next = peekToken();
        if (equal(next.string, "<-"))
        {
          nextToken();
          rewrite->right_to_left = true;
        }

        rewrite->eq_proof_hint = parseExpressionToAst(arena);
        ast = &rewrite->a;
      } break;

      case TC_StrongArrow:
      {
        pushContext("Full-rewrite: => TO_EXPRESSION [{ EQ_PROOF }]");
        RewriteAst *rewrite = newAst(arena, RewriteAst, &token);
        ast = &rewrite->a;
        {
          if (equal(peekToken().string, "_"))
          {// normlization
            nextToken();
          }
          else if ((rewrite->new_goal = parseExpressionToAst(arena)))
          {
            if (optionalChar('{'))
            {
              if (optionalString("<-"))  // todo: don't know whether to make a token type for this.
              {
                rewrite->right_to_left = true;
              }
              rewrite->eq_proof_hint = parseExpressionToAst(arena);
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
            case TC_ColonEqual:
            {
              pushContext("let: NAME := VALUE");
              if (Ast *rhs = parseExpressionToAst(arena))
              {
                Let *let = newAst(arena, Let, name);
                ast = &let->a;
                let->lhs = name->string;
                let->rhs = rhs;
              }
              popContext();
            } break;

            case TC_Colon:
            {
              pushContext("typed let: NAME : TYPE := VALUE");
              if (Ast *type = parseExpressionToAst(arena))
              {
                if (requireCategory(TC_ColonEqual, ""))
                {
                  if (Ast *rhs = parseExpressionToAst(arena))
                  {
                    Let *let = newAst(arena, Let, name);
                    let->lhs  = name->string;
                    let->rhs  = rhs;
                    let->type = type;
                    ast = &let->a;
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
          ast  = &newAst(arena, Hole, &token)->a; // todo do we print this out correctly?
          stop = true;
        }
      } break;

      case TC_Keyword_prove:
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
            ast = &let->a;
          }
        }
        popContext();
      } break;
    }

    if (noError() && !ast)
    {
      *global_tokenizer = tk_save;
      Token token = peekToken();
      if (token.cat == TC_Keyword_fork)
      {
        nextToken();
        ast = &parseFork(arena)->a;
        stop = true;
      }
      else
      {
        ast = parseExpressionToAst(arena);
        stop = true;
      }
    }

    if (noError())
    {
      count++;
      AstList *new_list = pushStruct(temp_arena, AstList);
      new_list->first = ast;
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
      Ast *item = list->first;
      if (id > 0)
      {
        if (Let *let = castAst(item, Let))
          let->body = previous;
        else if (RewriteAst *rewrite = castAst(item, RewriteAst))
          rewrite->body = previous;
      }
      previous = item;
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

forward_declare internal BuildTerm
buildTerm(MemoryArena *arena, Typer *env, Ast *in0, Term *goal)
{
  // todo #cleanup #mem: sort out what we need and what we don't need to persist
  // todo #cleanup #speed: returning the value is just a waste of time most of the time. Just call evaluate whenever you need the value.
  // todo return the type, since we typecheck it anyway.
  // todo print out the goal whenever we fail
  // beware: Usually we mutate in-place, but we may also allocate anew.
  i32 serial = global_debug_serial++;
  BuildTerm out0 = {};
  assert(goal);
  b32 should_check_type = true;
  b32 recursed = false;

  switch (in0->cat)
  {
    case AC_Hole:
    {
      Term *fill = fillHole(arena, env, goal);
      if (fill)
        out0.term  = fill;
      else
      {
        parseError(in0, "expression required");
      }
    } break;

    case AC_SyntheticAst:
    {
      SyntheticAst *in = castAst(in0, SyntheticAst);
      out0.term = in->term;
    } break;

    case AC_Identifier:
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
            if (matchType(getType(arena, env, slot_value), goal))
            {
              if (value)
              {// ambiguous
                parseError(name, "not enough type information to disambiguate global name");
                setErrorFlag(ErrorAmbiguousName);
                break;
              }
              else
                value = slot_value;
            }
          }
          if (!value)
          {
            parseError(name, "global name does not match expected type");
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

    case AC_CompositeAst:
    {
      CompositeAst *in  = castAst(in0, CompositeAst);
      Composite    *out = newTerm(arena, Composite, 0);

      // i32 serial = global_debug_serial++;
      TermArray op_list = {};
      b32 should_build_op = true;
      // I want this part to be built-in to the parsing, so it's a different thing entirely?
      if (Identifier *op_ident = castAst(in->op, Identifier))
      {
        if (!lookupLocalName(env, &in->op->token))
        {
          should_build_op = false;
          op_list = getFunctionOverloads(env, op_ident, goal);
        }
      }

      if (CtorAst *op_ctor = castAst(in->op, CtorAst))
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

      for (i32 attempt=0; attempt < op_list.count; attempt++)
      {
        Term *op = op_list.items[attempt];
        out->op = op;
        if (Arrow *signature = castTerm(getType(temp_arena, env, op), Arrow))
        {
          if (signature->param_count != in->arg_count)
          {
            i32 explicit_param_count = getExplicitParamCount(signature);
            if (in->arg_count == explicit_param_count)
            {
              Ast **supplied_args = in->args;
              in->arg_count = signature->param_count;
              in->args      = pushArray(arena, signature->param_count, Ast*);
              for (i32 param_id = 0, arg_id = 0;
                   param_id < signature->param_count && noError();
                   param_id++)
              {
                if (isHiddenParameter(signature, param_id))
                {
                  in->args[param_id] = &newAst(arena, Hole, &in->op->token)->a;
                }
                else
                {
                  assert(arg_id < explicit_param_count);
                  in->args[param_id] = supplied_args[arg_id++];
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
            Term **args = pushArray(arena, in->arg_count, Term *);
            for (int arg_id = 0;
                 (arg_id < in->arg_count) && noError();
                 arg_id++)
            {
              Term *param_type0 = signature->param_types[arg_id];
              Term *expected_arg_type = evaluate(arena, args, param_type0);

              // Typecheck & Inference for the arguments.
              if (in->args[arg_id]->cat == AC_Hole)
              {
                if (Term *fill = fillHole(arena, env, expected_arg_type))
                  args[arg_id] = fill;
                else
                {
                  Term *placeholder_arg = copyStruct(temp_arena, holev);
                  setType(placeholder_arg, expected_arg_type);
                  args[arg_id] = placeholder_arg;
                }
              }
              else
              {
                if (BuildTerm arg = buildTerm(arena, env, in->args[arg_id], expected_arg_type))
                {
                  args[arg_id] = arg.term;
                  if (expected_arg_type->cat == Term_Hole)
                  {
                    Variable *param_type = castTerm(param_type0, Variable);
                    assert(param_type->delta == 0);
                    Term *placeholder_arg = args[param_type->id];
                    assert(placeholder_arg->cat == Term_Hole);
                    Term *arg_type = getType(arena, env, arg.term);
                    Term *arg_type_type = getType(arena, env, arg_type);
                    if (equal(placeholder_arg->type, arg_type_type))
                      args[param_type->id] = arg_type;
                    else
                    {
                      parseError(in->args[arg_id], "type of argument has wrong type");
                      attach("expected", placeholder_arg->type);
                      attach("got", arg_type_type);
                    }
                  }
                }
              }
            }

            if (noError())
            {
              for (i32 arg_id = 0;
                   arg_id < in->arg_count && noError();
                   arg_id++)
              {
                if (args[arg_id]->cat == Term_Hole)
                {
                  parseError(in->args[arg_id], "Cannot fill hole");
                  attach("argument number", arg_id);
                  attach("param type", signature->param_types[arg_id]);
                }
              }
            }

            if (noError())
            {
              out->arg_count = in->arg_count;
              allocateArray(arena, out->arg_count, out->args);
              for (i32 id = 0; id < out->arg_count; id++)
                out->args[id] = args[id];
              out0.term  = &out->t;
            }
          }
        }
        else
        {
          parseError(in->op, "operator must have an arrow type");
          attach("operator type", getType(temp_arena, env, op));
        }

        if (op_list.count > 1)
        {
          if (hasError() && !checkErrorFlag(ErrorUnrecoverable))
          {
            wipeError();
            if (attempt == op_list.count-1)
            {
              parseError(in->op, "found no suitable overload");
              attachTerms("available_overloads", op_list.count, op_list.items);
              attach("serial", serial);
            }
          }
          else
            break;
        }
      }
    } break;

    case AC_ArrowAst:
    {
      ArrowAst *in = castAst(in0, ArrowAst);
      Arrow *out = newTerm(arena, Arrow, &builtins.Type->t);
      i32 param_count = in->param_count;
      out->param_count   = param_count;
      out->param_names   = in->param_names;
      out->param_flags   = in->param_flags;
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
            Token *name = in->param_names+index;
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

    case AC_AccessorAst:
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
            if (equal(in->field_name.string, op_type->param_names[param_id].string))
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
            attach("expected a member of constructor", ctor.uni->ctor_names[ctor.id].chars);
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

    case AC_Lambda:
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

    case AC_RewriteAst:
    {
      should_check_type = false;
      RewriteAst *in  = castAst(in0, RewriteAst);
      Rewrite    *out = newTerm(arena, Rewrite, 0);
      Term *new_goal = 0;
      if (!in->eq_proof_hint)
      {
        b32 skip_goal_comparison = false;
        if (!in->new_goal)
        {
          new_goal = normalize(arena, env, goal);
          skip_goal_comparison = true;
        }
        else if (BuildTerm build = buildTerm(arena, env, in->new_goal, holev))
          new_goal = build.term;

        if (noError())
        {
          if (equal(new_goal, goal))
          {// superfluous rewrite -> remove
            recursed = true;
            out0 = buildTerm(arena, env, in->body, goal);
          }
          else
          {
            if (!skip_goal_comparison)
            {
              Term *new_goal_norm = normalize(arena, env, new_goal);
              Term *goal_norm     = normalize(arena, env, goal);
              if (!equal(new_goal_norm, goal_norm))
              {
                parseError(in0, "new goal does not match original");
                // equal(new_goal_norm, goal_norm);
                attach("new goal normalized", new_goal_norm);
                attach("current goal normalized", goal_norm);
              }
            }
            if (noError())
            {
              Term *com = newComputation(arena, goal, new_goal);
              out->eq_proof = com;
            }
          }
        }
      }
      else if (in->new_goal)
      {// diff
        if (BuildTerm build_new_goal = buildTerm(arena, env, in->new_goal, holev))
        {
          new_goal = build_new_goal.term;
          CompareTerms compare = compareTerms(arena,goal, new_goal);
          if (compare.result == Trinary_True)
            parseError(in0, "new goal same as current goal");
          else
          {
            out->path = compare.diff_path;
            Term *from = subExpressionAtPath(goal, compare.diff_path);
            Term *to   = subExpressionAtPath(new_goal, compare.diff_path);
            Term *eq = 0;

            TermArray op_list = {};
            if (Identifier *op_ident = castAst(in->eq_proof_hint, Identifier))
            {// operator hint
              if (lookupLocalName(env, &op_ident->token))
              {
                if (BuildTerm build_op = buildTerm(arena, env, &op_ident->a, holev))
                {
                  op_list.count = 1;
                  allocateArray(temp_arena, 1, op_list.items);
                  op_list.items[0] = build_op.term;
                }
              }
              else
                op_list = getFunctionOverloads(env, op_ident, holev);

              for (int attempt=0; attempt < op_list.count; attempt++)
              {
                Term *hint = op_list.items[attempt];
                b32 hint_is_valid = false;
                Term *hint_type = getType(temp_arena, env, hint);
                if (Arrow *signature = castTerm(hint_type, Arrow))
                {
                  hint_is_valid = true;
                  eq = newEquality(temp_arena, from, to);
                  pushArray(temp_arena, signature->param_count, Term *, true);
                  if (Term **temp_args = inferArgs(temp_arena, env, hint, eq).args)
                  {
                    Term **args = pushArray(arena, signature->param_count, Term *);
                    for (int id=0; id < signature->param_count; id++)
                    {
                      if (temp_args[id])
                      {
                        args[id] = temp_args[id];
                      }
                      else
                      {
                        parseError(in0, "Internal compiler (or user) error: we were not able to infer all parameters");
                        break;
                      }
                    }
                    if (noError())
                    {
                      Composite *eq_proof_composite = newTerm(arena, Composite, 0);
                      eq_proof_composite->op        = hint;
                      eq_proof_composite->arg_count = signature->param_count;
                      eq_proof_composite->args      = args;
                      out->eq_proof = &eq_proof_composite->t;
                      // since the proof was synthesized from unification, double-check the type
                      Term *eq_check = getType(arena, env, out->eq_proof);
                      assert(equal(eq_check, eq));
                    }
                  }
                  else
                  {
                    parseError(in->eq_proof_hint, "unification failed");
                    attach("lhs", signature->output_type);
                    attach("rhs", eq);
                    attach("goal", goal);
                    attach("serial", serial);
                  }
                }
                else if (isEquality(hint_type))
                {
                  eq = hint_type;
                  hint_is_valid = true;
                  out->eq_proof = hint;
                }

                if (!hint_is_valid)
                {
                  parseError(in->eq_proof_hint, "invalid proof pattern");
                  attach("type", hint_type);
                }

                if (op_list.count > 1)
                {
                  if (hasError() && !checkErrorFlag(ErrorUnrecoverable))
                  {
                    wipeError();
                    if (attempt == op_list.count-1)
                    {
                      parseError(&op_ident->a, "found no suitable overload");
                      attachTerms("available_overloads", op_list.count, op_list.items);
                    }
                  }
                  else
                    break;
                }
              }
            }
            else if (BuildTerm build_eq_proof = buildTerm(arena, env, in->eq_proof_hint, holev))
            {// full proof of equality
              out->eq_proof = build_eq_proof.term;
              eq = getType(temp_arena, env, build_eq_proof.term);
              if (!isEquality(eq))
              {
                parseError(in->eq_proof_hint, "invalid proof pattern");
                attach("type", eq);
              }
            }
            else
              parseError(in->eq_proof_hint, "invalid proof pattern");

            if (noError())
            {
              auto [lhs,rhs] = getEqualitySides(eq);
              Term *from, *to;
              if (in->right_to_left) {from = rhs; to = lhs; out->right_to_left = true;}
              else                   {from = lhs; to = rhs;}
              Term *new_goal_check = rewriteTerm(arena, to, out->path, goal);
              if (!equal(new_goal, new_goal_check))
              {
                parseError(in0, "invalid full-rewrite");
                attach("original goal", goal);
                attach("expected rewrite result", new_goal);
                attach("actual rewrite result", new_goal_check);
                attach("rewrite from", from);
                attach("rewrite to", to);
              }
            }
          }
        }
      }
      else
      {// search
        if (BuildTerm eq_proof = buildTerm(arena, env, in->eq_proof_hint, holev))
        {
          out->eq_proof = eq_proof.term;
          Term *eq = getType(temp_arena, env, eq_proof.term);
          if (auto [from, to] = getEqualitySides(eq, false))
          {
            if (in->right_to_left) {auto tmp = from; from = to; to = tmp; out->right_to_left = true;}
            SearchOutput search = searchExpression(arena, env, from, goal);
            if (search.found)
            {
              out->path = search.path;
              new_goal = rewriteTerm(arena, to, out->path, goal);
            }
            else
            {
              parseError(in0, "substitution has no effect");
              attach("substitution", eq);
            }
          }
          else
          {
            parseError(in->eq_proof_hint, "please provide a proof of equality that can be used for substitution");
            attach("got", eq);
          }
        }
      }

      if (noError() && !recursed)
      {
        assert(new_goal);
        if (BuildTerm body = buildTerm(arena, env, in->body, new_goal))
        {
          out->body = body.term;
          out0.term = &out->t;
        }
      }
    } break;

    case AC_Let:
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
            rhs_type = getType(arena, env, build_rhs.term);
            
          if (in->type == LET_TYPE_NORMALIZE)
          {// type coercion
            Term *norm_rhs_type = normalize(arena, env, rhs_type);
            Term *computation = newComputation(arena, norm_rhs_type, rhs_type);
            rhs_type = norm_rhs_type;
            rhs = newRewrite(arena, computation, build_rhs.term, 0, false);
            assert(equal(getType(temp_arena, env, rhs), rhs_type));
          }

          Token *token = &in0->token;
          Lambda *lambda = newAst(temp_arena, Lambda, token);
          lambda->body = in->body;
          ArrowAst *signature = newAst(temp_arena, ArrowAst, token);
          i32 param_count = 1;
          allocateArray(temp_arena, param_count, signature->param_names);
          allocateArray(temp_arena, param_count, signature->param_types);
          signature->param_count    = param_count;
          signature->param_names[0] = newToken(in->lhs);  // probably fine since we don't include this token anywhere, we only need the name

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

    case AC_ForkAst:
    {// no need to return value since nobody uses the value of a fork
      ForkAst *fork = castAst(in0, ForkAst);
      out0.term = buildFork(arena, env, fork, goal);
      recursed = true;
    } break;

    case AC_UnionAst:
    {
      UnionAst *uni = castAst(in0, UnionAst);
      out0.term = &buildUnion(arena, env, uni, 0)->t;
    } break;

    case AC_DestructAst:
    {
      DestructAst *in = castAst(in0, DestructAst);
      if (BuildTerm build_eqp = buildTerm(arena, env, in->eqp, holev))
      {
        Term *eq = getType(arena, env, build_eqp.term);
        if (TermPair sides = getEqualitySides(eq, false))
        {
          Constructor *ctor = 0;
          Composite *lhs = 0;
          Composite *rhs = 0;
          if ((lhs = castTerm(sides.lhs, Composite)))
          {
            if (Constructor *lhs_ctor = castTerm(lhs->op, Constructor))
            {
              if ((rhs = castTerm(sides.rhs, Composite)))
              {
                if (Constructor *rhs_ctor = castTerm(rhs->op, Constructor))
                {
                  if (equal(&rhs_ctor->t, &lhs_ctor->t))
                    ctor = lhs_ctor;
                  else
                    parseError(in0, "lhs constructor is not equal to rhs constructor");
                }
                else
                  parseError(in0, "rhs must be a record");
              }
            }
            else
              parseError(in0, "lhs must be a record");
          }
          else
            parseError(in0, "lhs must be a record");

          if (hasError())
            attach("type", eq);
          else
          {
            i32 param_count = castTerm(ctor->type, Arrow)->param_count;
            if (in->arg_id < param_count)
            {
              for (DestructList *destructs = global_state.builtin_destructs;
                   destructs;
                   destructs = destructs->next)
              {
                // todo #speed
                if ((destructs->uni == ctor->uni) && (destructs->ctor_id == ctor->id))
                {
                  Composite *out = newTerm(arena, Composite, 0);
                  out->op        = destructs->items[in->arg_id];
                  out->arg_count = lhs->arg_count*2+1;
                  out->args      = pushArray(arena, out->arg_count, Term*);
                  // todo cleanup: use parameter type inference
                  for (i32 id=0; id < out->arg_count; id++)
                  {
                    if (id == out->arg_count-1)
                      out->args[id] = build_eqp.term;
                    else if (id < lhs->arg_count)
                      out->args[id] = lhs->args[id];
                    else
                      out->args[id] = rhs->args[id - lhs->arg_count];
                  }
                  out0.term = &out->t;
                  break;
                }
              }
            }
            else
              parseError(in0, "constructor only has %d parameters", param_count);
          }
        }
        else
          parseError(in0, "expected an equality proof as argument");
      }
    } break;

    case AC_CtorAst:
    {
      parseError(in0, "please use this constructor syntax as an operator");
    } break;

    case AC_SeekAst:
    {
      SeekAst *in = castAst(in0, SeekAst);
      if (BuildTerm proposition = buildTerm(temp_arena, env, in->proposition, holev))
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
            if (equal(type, proposition.term))
            {
              Variable *var = newTerm(arena, Variable, 0);
              var->name  = arrow->param_names[param_id].string;
              var->delta = delta;
              var->id    = param_id;
              out0.term = &var->t;
            }
          }
          delta++;
        }
        if (!out0.term)
        {
          parseError(in0, "cannot find a matching proof on the stack");
        }
      }
    } break;

    invalidDefaultCase;
  }

  if (noError())
  {// typecheck if needed
    Term *actual = deriveType(arena, env, out0.term);
    if (should_check_type && !recursed)
    {
      if (!matchType(actual, goal))
      {
        parseError(in0, "actual type differs from expected type");
        attach("got", actual);
        attach("serial", serial);
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

      MemoryArena buffer = subArena(temp_arena, 1024);
      print(&buffer, "\n");
      print(&buffer, env->scope);
      attach("scope", (char *)buffer.base);
      buffer.used++;

      attach("data_map", (char *)getNext(&buffer));
      printDataMap(&buffer, env);
      buffer.used++;

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
  assert(goal && goal->cat != Term_Hole);
  Fork *out = newTerm(arena, Fork, goal);
  out->case_count = in->case_count;
  i32 unused_variable serial = global_debug_serial++;
  if (BuildTerm subject = buildTerm(arena, env, in->subject, holev))
  {
    out->subject = subject.term;
    i32 case_count = in->case_count;

    Term *subject_type = getType(arena, env, subject.term);
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
                attach("constructor", uni->ctor_names[ctor_id].chars);  // todo cleanup attach string
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
            parseError(ctor_name, "not a valid constructor");  // todo print them out
            attach("type", &uni->t);

            char *ctor_names = (char *)getNext(temp_arena);
            for (i32 id=0; id < uni->ctor_count; id++)
            {
              print(temp_arena, uni->ctor_names[id]);
              if (id != uni->ctor_count-1)
                print(temp_arena, ", ");
            }
            attach("valid constructors", ctor_names);
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

#if 0
forward_declare inline void
doubleCheckType(Term *in0)
{
  switch (in0->cat)
  {
    case Term_Rewrite:
    {
      Rewrite *in = castTerm(in0, Rewrite);
      auto [lhs, rhs] = getEqualitySides(in->eq_proof->type);
      Term *rewrite_to = in->right_to_left ? rhs : lhs;
      Term *expected_type = rewriteTerm(temp_arena, rewrite_to, in->path, in->body->type);
      assert(equal(expected_type, in0->type));
    } break;

    default:
    {todoIncomplete;} break;
  }
}
#endif

forward_declare inline Term *
newRewrite(MemoryArena *arena, Term *eq_proof, Term *body, TreePath *path, b32 right_to_left)
{
  Rewrite *out = newTerm(arena, Rewrite, 0);
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
    case AC_ForkAst:
    {
      ForkAst *in = castAst(in0, ForkAst);
      for (i32 case_id=0; case_id < in->case_count; case_id++)
      {
        Ast *body = in->bodies[case_id];
        insertAutoNormalizations(arena, norm_list, body);
        for (i32 norm_id=0; norm_id < norm_list.count; norm_id++)
        {
          Identifier *item = norm_list.items[norm_id];
          Let *new_body = newAst(arena, Let, &item->token);
          new_body->lhs  = item->token.string;
          new_body->rhs  = &item->a;
          new_body->type = LET_TYPE_NORMALIZE;
          new_body->body = body;
          body = &new_body->a;
        }
        RewriteAst *new_body = newAst(arena, RewriteAst, &body->token);
        new_body->body = body;
        in->bodies[case_id] = &new_body->a;
      }
    } break;

    case AC_Let:
    {
      Let *in = castAst(in0, Let);
      insertAutoNormalizations(arena, norm_list, in->body);
    } break;

    default:
    {} break;
  }
}

forward_declare internal FunctionDecl *
parseFunction(MemoryArena *arena, Token *name, b32 is_theorem)
{
  FunctionDecl *out = newAst(arena, FunctionDecl, name);
  assert(isIdentifier(name));

  if (Ast *signature0 = parseExpressionToAst(arena))
  {
    NormList norm_list = {};
    if (ArrowAst *signature = castAst(signature0, ArrowAst))
    {
      if (optionalCategory(TC_Directive_norm))
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

forward_declare internal ForkAst *
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
            parseError(&ctor, "expected a constructor name");

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

  return out;
}

internal ArrowAst *
parseArrowType(MemoryArena *arena, b32 is_struct)
{
  ArrowAst *out = 0;

  i32     param_count;
  Token  *param_names;
  Ast   **param_types;
  u32    *param_flags;
  Token marking_token = peekToken();
  char begin_arg_char = '(';
  char end_arg_char   = ')';
  if (requireChar(begin_arg_char))
  {
    Tokenizer tk_copy = *global_tokenizer;
    param_count = getCommaSeparatedListLength(&tk_copy);
    if (noError(&tk_copy))
    {
      allocateArray(arena, param_count, param_names);
      allocateArray(arena, param_count, param_types);
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
          if (optionalCategory(TC_Directive_hidden))
          {
            setFlag(&param_flags[param_id], ParameterFlag_Hidden);
          }
          if (requireIdentifier("expected parameter name"))
          {
            Token param_name_token = global_tokenizer->last_token;
            param_names[param_id] = param_name_token;

            if (optionalChar(':'))
            {
              if (Ast *param_type = parseExpressionToAst(arena))
              {
                param_types[param_id] = param_type;
                if (typeless_run)
                {
                  for (i32 offset = 1;
                       offset <= typeless_run;
                       offset++)
                  {
                    param_types[param_id - offset]  = param_type;
                  }
                  typeless_run = 0;
                }

                Token delimiter = nextToken();
                if (equal(&delimiter, end_arg_char))
                  stop = true;
                else if (!equal(&delimiter, ','))
                  tokenError("unexpected token after parameter type");
              }
            }
            else if (requireChar(',', "delimit after typeless parameter name"))
            {
              typeless_run++;
              typeless_token = param_name_token;
            }
            else
              stop = true;
          }
        }
      }
      if (noError())
      {
        assert(parsed_param_count == param_count);
        if (typeless_run)
        {
          parseError(&typeless_token, "please provide types for all parameters");
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
      if (requireCategory(TC_Arrow, "syntax: (param: type, ...) -> ReturnType"))
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
  allocateArray(arena, in->ctor_count, uni->ctor_signatures);
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
      uni->ctor_signatures[ctor_id] = signature;
      ctor->type                    = &signature->t;

      if (global_name)
      {
        if (signature->param_count > 0)
        {
          addGlobalBinding(ctor_name, &ctor->t);

          // todo #cleanup This is a "destruct" builtin, which deconstructs an equality for us.
          i32 ctor_arg_count      = signature->param_count;
          i32 compare_param_count = ctor_arg_count*2 + 1;
          Token* param_names = pushArray(arena, compare_param_count, Token);
          Term** param_types = pushArray(arena, compare_param_count, Term*);
          for (i32 group=0; group <= 1; group++)
          {
            for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
            {
              String name = print(arena, "_");
              concat(&name, print(arena, signature->param_names[arg_id].string));
              concat(&name, print(arena, "%d", group));
              i32 offset   = (group == 0) ? 0 : ctor_arg_count;
              i32 param_id = offset + arg_id;
              param_names[param_id] = newToken(name);
              param_types[param_id] = signature->param_types[arg_id];
            }
          }
          Term **lhs_args = pushArray(arena, ctor_arg_count, Term*);
          Term **rhs_args = pushArray(arena, ctor_arg_count, Term*);
          for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
          {
            i32 lhs_param_id = arg_id;
            i32 rhs_param_id = ctor_arg_count+arg_id;
            lhs_args[arg_id] = newVariable(arena, param_names+lhs_param_id, 0, lhs_param_id);
            rhs_args[arg_id] = newVariable(arena, param_names+rhs_param_id, 0, rhs_param_id);
          }
          Term *lhs = newComposite(arena, &ctor->t, ctor_arg_count, lhs_args);
          Term *rhs = newComposite(arena, &ctor->t, ctor_arg_count, rhs_args);
          param_names[compare_param_count-1] = newToken(toString("P"));
          param_types[compare_param_count-1] = newEquality(arena, &uni->t, lhs, rhs);

          DestructList *destruct_list = pushStruct(global_state.arena, DestructList);
          destruct_list->next = global_state.builtin_destructs;
          global_state.builtin_destructs = destruct_list;
          destruct_list->uni     = uni;
          destruct_list->ctor_id = ctor_id;
          allocateArray(arena, ctor_arg_count, destruct_list->items);
          for (i32 arg_id=0; arg_id < ctor_arg_count; arg_id++)
          {
            Arrow *destruct_signature = newTerm(arena, Arrow, 0);
            destruct_signature->param_count = compare_param_count;
            destruct_signature->param_names = param_names;
            destruct_signature->param_types = param_types;
            destruct_signature->output_type = newEquality(arena, signature->param_types[arg_id], lhs_args[arg_id], rhs_args[arg_id]);

            Builtin *destruct = newTerm(arena, Builtin, &destruct_signature->t);
            destruct_list->items[arg_id] = &destruct->t;
          }
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

inline DestructAst *
parseDestruct(MemoryArena *arena)
{
  DestructAst *out = newAst(arena, DestructAst, &global_tokenizer->last_token);
  if (requireChar('['))
  {
    out->arg_id = parseInt32();
    if (requireChar(']'))
    {
      out->eqp = parseExpressionToAst(arena);
    }
  }
  return out;
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
  SeekAst *seek = 0;
  if (Ast *proposition = parseExpressionToAst(arena))
  {
    seek = newAst(arena, SeekAst, &global_tokenizer->last_token);
    seek->proposition = proposition;
  }
  return seek;
}

internal Ast *
parseOperand(MemoryArena *arena)
{
  Ast *operand = 0;
  Token token = nextToken();
  if (equal(&token, '_'))
  {
    operand = &newAst(arena, Hole, &token)->a;
  }
  else if (token.cat == TC_Keyword_seq)
  {
    operand = parseSequence(arena);
  }
  else if (token.cat == TC_Keyword_union)
  {
    operand = &parseUnion(arena)->a;
  }
  else if (token.cat == TC_Keyword_destruct)
  {
    operand = &parseDestruct(arena)->a;
  }
  else if (token.cat == TC_Keyword_ctor)
  {
    operand = &parseCtor(arena)->a;
  }
  else if (token.cat == TC_Keyword_seek)
  {
    operand = &parseSeek(arena)->a;
  }
  else if (isIdentifier(&token))
  {
    operand = &newAst(arena, Identifier, &token)->a;
  }
  else if (equal(&token, '('))
  {
    operand = parseExpressionToAst(arena);
    requireChar(')');
  }
  else
  {
    tokenError("expected start of expression");
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
        for (i32 stop = false;
             hasMore () && !stop;
             )
        {
          if (optionalChar(')'))
            stop = true;
          else
          {
            i32 arg_id = parsed_arg_count++;
            Ast *arg = parseExpressionToAst(arena);
            if (hasMore())
            {
              args[arg_id] = arg;
              if (!optionalChar(','))
              {
                requireChar(')', "expected ',' or ')'");
                stop = true;
              }
            }
          }
        }
        if (hasMore())
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
      out = nextToken(tk).cat == TC_Arrow;
  return out;
}

inline b32 seesLambda()
{// todo we don't allow naming parameters in here yet
  b32 out = false;
  Tokenizer tk_ = *global_tokenizer;
  Tokenizer *tk = &tk_;
  if (requireChar('_', 0, tk))
  {
    if (requireCategory(TC_StrongArrow, 0, tk))
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

internal Function *
buildGlobalFunction(MemoryArena *arena, Typer *env, FunctionDecl *decl)
{
  Function *funv = 0;
  if (BuildTerm build_signature = buildTerm(arena, env, &decl->signature->a, holev))
  {
    Arrow *signature = castTerm(build_signature.term, Arrow);
    funv = newTerm(arena, Function, build_signature.term);
    funv->body = &dummy_function_being_built;

    // note: add binding first to support recursion
    addGlobalBinding(&decl->a.token, &funv->t);

    if (noError())
    {
      introduceSignature(env, signature, true);
      // Term *expected_body_type = evaluateArrow(temp_arena, env, signature, env->stack->items, signature->output_type);
      if (BuildTerm body = buildTerm(arena, env, decl->body, signature->output_type))
        funv->body = body.term;
      unwindBindingsAndScope(env);
    }
  }
  return funv;
}

// NOTE: Main dispatch parse function
internal void
parseTopLevel(EngineState *state)
{
  MemoryArena *arena = state->arena;
  b32 should_fail_active = false;

  Token token = nextToken(); 
  while (hasMore())
  {
#define CLEAN_TEMPORARY_MEMORY 1
#if CLEAN_TEMPORARY_MEMORY
    TemporaryMemory top_level_temp = beginTemporaryMemory(temp_arena);
#endif

    Typer  empty_env_ = {};
    Typer *empty_env  = &empty_env_;

    switch (token.cat)
    {
      case TC_Directive_load:
      {
        pushContext("#load");
        Token file = nextToken();
        if (file.cat != TC_StringLiteral)
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

      case TC_Directive_should_fail:
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

      case TC_Directive_debug:
      {
        if (optionalString("off"))
          global_debug_mode = false;
        else
          global_debug_mode = true;
      } break;

      case TC_Keyword_test_eval:
      {
        if (BuildTerm expr = parseExpressionFull(temp_arena))
          normalize(arena, empty_env, expr.term);
      } break;

      case TC_Keyword_print:
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

      case TC_Keyword_print_raw:
      {
        if (auto parsing = parseExpressionFull(temp_arena))
          print(0, parsing.term, {.flags = (PrintFlag_Detailed     |
                                            PrintFlag_LockDetailed |
                                            PrintFlag_PrintType)});
        print(0, "\n");
      } break;

      case TC_Keyword_print_ast:
      {
        if (Ast *exp = parseExpressionToAst(temp_arena))
          print(0, exp, {.flags = PrintFlag_Detailed});
        print(0, "\n");
      } break;

      case TC_Keyword_check:
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

      case TC_Keyword_check_truth:
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
                parseError(&token, "equality cannot be proven by computation");
                global_debug_mode = true;
                Term *lhs = normalize(temp_arena, empty_env, eq->args[1]);
                attach("lhs", lhs);
                attach("rhs", rhs);
              }
            }
            if (!goal_valid)
            {
              parseError(&token, "computation can only prove equality");
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
            case TC_ColonEqual:
            {
              pushContext("constant definition: CONSTANT := VALUE;");
              if (BuildTerm rhs = parseExpressionFull(arena))
              {
                addGlobalBinding(&token, rhs.term);
                requireChar(';');
              }
              popContext();
            } break;

            case TC_DoubleColon:
            {
              Token after_dcolon = peekToken();
              if (after_dcolon.cat == TC_Keyword_union)
              {
                nextToken();
                if (UnionAst *ast = parseUnion(arena))
                  buildUnion(arena, empty_env, ast, &token);
              }
              else
              {
                b32 is_theorem;
                if (after_dcolon.cat == TC_Keyword_fn)
                {
                  is_theorem = false;
                  nextToken();
                }
                else is_theorem = true;
                if (FunctionDecl *fun = parseFunction(arena, &token, is_theorem))
                  buildGlobalFunction(arena, empty_env, fun);
              }
            } break;

            case ':':
            {
              if (BuildTerm type = parseExpressionFull(arena))
              {
                if (requireCategory(TC_ColonEqual, "require :=, syntax: name : type := value"))
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

    token = nextToken();
    while (equal(token.string, ";"))
    {// todo: should we do "eat all semicolons after the first one?"
      token = nextToken();
    }
  }
}

forward_declare internal b32
interpretFile(EngineState *state, FilePath input_path, b32 is_root_file)
{
  MemoryArena *arena = state->arena;
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
      printf("Interpreting file %s...\n", input_path.file);
    }
    parseTopLevel(state);
    if (ParseError *error = tk->error)
    {
      success = false;
      printf("%s:%d:%d: [%s] ",
             input_path.path,

             error->line,
             error->column,

             error->context ? error->context : "");
      print(0, error->message);

      if (error->attachment_count > 0)
      {
        printf("\n");
        for (int attached_id = 0;
             attached_id < error->attachment_count;
             attached_id++)
        {
          auto attachment = error->attachments[attached_id];
          printf("%s: %s", attachment.key, attachment.value);
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
      printf("----------------\n");
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

forward_declare inline BuildTerm
parseExpressionFromString(MemoryArena *arena, char *string)
{
  Tokenizer tk = newTokenizer(String{}, 0);
  Tokenizer *tk_save = global_tokenizer;
  global_tokenizer = &tk;
  tk.at = string;
  BuildTerm out = parseExpressionFull(arena);
  global_tokenizer = tk_save;
  return out;
}

internal b32
beginInterpreterSession(MemoryArena *arena, char *initial_file)
{
  global_debug_mode = false;
  global_state       = {};
  global_state.arena = arena;

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
      Tokenizer builtin_tk = newTokenizer(print(temp_arena, "<builtin>"), 0);
      global_tokenizer = &builtin_tk;
      builtin_tk.at = "(#hidden A: Set, a,b: A) -> Set";
      BuildTerm equal_type = parseExpressionFull(arena); 
      assert(noError());
      builtins.equal = newTerm(arena, Builtin, equal_type.term);
      addBuiltinGlobalBinding("=", &builtins.equal->t);

      EngineState builtin_engine_state = EngineState{.arena=arena};
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

  assert(arrayCount(keywords)       == TC_Keyword_END - TC_Keyword_START);
  assert(arrayCount(metaDirectives) == TC_Directive_END - TC_Directive_START);

  void   *permanent_memory_base = (void*)teraBytes(2);
  size_t  permanent_memory_size = megaBytes(256);
  permanent_memory_base = platformVirtualAlloc(permanent_memory_base, permanent_memory_size);
  MemoryArena permanent_arena_ = newArena(permanent_memory_size, permanent_memory_base);
  MemoryArena *permanent_arena = &permanent_arena_;

  void   *temp_memory_base = (void*)teraBytes(3);
  size_t  temp_memory_size = megaBytes(2);
  temp_memory_base = platformVirtualAlloc(temp_memory_base, permanent_memory_size);
  MemoryArena temp_arena_ = newArena(temp_memory_size, temp_memory_base);
  temp_arena              = &temp_arena_;

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/test.rea"))
    success = false;
  resetArena(permanent_arena, true);
#endif

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/natp-experimental.rea"))
    success = false;
  resetArena(permanent_arena, true);
#endif

#if 1
  if (!beginInterpreterSession(permanent_arena, "../data/rat.rea"))
    success = false;
  resetArena(permanent_arena, true);
#endif

  return success;
}

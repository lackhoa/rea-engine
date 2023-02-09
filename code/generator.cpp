#include <windows.h>
#include <malloc.h>
#include "utils.h"
#include "clang-c/Index.h"

global_variable Arena *permanent_arena;
global_variable Arena *temp_arena;
global_variable String current_dir;
global_variable __attribute__((unused)) b32 global_debug_mode;

struct LocationList
{
  unsigned      line;
  String        file_name;
  LocationList *next;
};

struct EmbedStructs
{
  String name;
  String fields;
  EmbedStructs *next;
};

struct State
{
  FILE         *forward_declare_file;
  LocationList *forward_declare_locations;

  b32           inside_embedded_struct;
  LocationList *embed_locations;
  EmbedStructs *embed_structs;
};

inline char *
readEntireFile(char *file_name)
{
  FILE *file;
  if (fopen_s(&file, file_name, "r") == 0)
  {
    assert(file);
    fseek(file, 0, SEEK_END);
    size_t file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    char *result = (char *)malloc(file_size+1);
    fread(result, file_size, 1, file);
    result[file_size] = 0;
    fclose(file);
    return (result);
  }
  else
  {
    fprintf(stderr, "Cannot open file %s! \n", file_name);
    return(0);
  }
}

internal void
generateCode(char *templated_code, char *output_name, char *type)
{
  FILE *output;
  if (fopen_s(&output, output_name, "w") == 0)
  {
    char *at = templated_code;
    while (*at)
    {
      if ((*at == '.') && (*(at+1) == '.') && (*(at+2) == '.'))
      {
        at += 2;
        fprintf(output, "%s", type);
      }
      else
      {
        fprintf(output, "%c", *at);
      }
      at++;
    }

    fclose(output);
  }
  else
  {
    fprintf(stderr, "Cannot open file %s! \n", output_name);
  }
}

inline void
generateVectors()
{
  char *vector_types[] = {"Operator", "Atom", "Type", "Instruction"};

  char *templated_code = readEntireFile("templated_Vector.h");
  if (templated_code)
  {
    for (int type_it = 0;
         type_it < arrayCount(vector_types);
         type_it++)
    {
      char output_name[256];
      char *type = vector_types[type_it];
      sprintf_s(output_name, 256, "generated/Vector_%s.h", type);
      generateCode(templated_code, output_name, type);
    }
  }
}

struct FileList
{
  i32    count;
  char **files;
};

internal FileList
getAllCppFilesInDirectory()
{
  FileList out = {};
  for (i32 iter = 0; iter < 2; iter++)
  {
    if (iter == 1)
    {
      out.files = (char**)malloc(out.count * sizeof(char*));
    }

    WIN32_FIND_DATAA find_data;
    HANDLE find_handle = FindFirstFileA("*.cpp", &find_data);
    DWORD dwError = 0;

    if (find_handle == INVALID_HANDLE_VALUE) 
    {
      // todo error?
    }
    else
    {
      i32 file_id = 0;
      do
      {
        if (iter == 0)
          out.count++;
        else
        {
          char *file_name = (char *)malloc(MAX_PATH*sizeof(char));
          char *d = file_name;
          for (char *c = find_data.cFileName; *c;)
          {
            *d++ = *c++;
          }
          *d = 0;
          out.files[file_id++] = file_name;
        }
      }
      while (FindNextFile(find_handle, &find_data) != 0);
 
      dwError = GetLastError();
      if (dwError != ERROR_NO_MORE_FILES) 
      {
        // todo error?
      }
      // Doesn't matter if this handle leaks.
      // FindClose(find_handle);
    }
  }

  return out;
}

inline String
print(Arena *buffer, CXString string)
{
  String out = {};
  const char *cstring = clang_getCString(string);
  if (cstring)
  {
    out = print(buffer, (char *)cstring);
    clang_disposeString(string);
  }
  return out;
}

internal char *
printFunctionSignature(Arena *buffer, CXCursor cursor)
{
  char *out = (char *)getNext(buffer);

  CXType type = clang_getCursorType(cursor);
  print(buffer, clang_getTypeSpelling(clang_getResultType(type)));
  print(buffer, " ");

  print(buffer, clang_getCursorSpelling(cursor));

  print(buffer, "(");
  int num_args = clang_Cursor_getNumArguments(cursor);
  for (int i = 0; i < num_args; ++i)
  {
    CXCursor arg_cursor = clang_Cursor_getArgument(cursor, i);
    print(buffer, clang_getTypeSpelling(clang_getArgType(type, i)));
    print(buffer, " ");
    print(buffer, clang_getCursorSpelling(arg_cursor));
    if (i != num_args-1)
    {
      print(buffer, ", ");
    }
  }
  print(buffer, ");\n\0");

  return out;
}

internal CXChildVisitResult
printStructVisitor(CXCursor cursor, CXCursor parent, CXClientData client_data)
{
  (void)parent;
  Arena *arena = permanent_arena;
  String *out = (String *)client_data;
  CXCursorKind cursor_kind = clang_getCursorKind(cursor);
  switch (cursor_kind)
  {
    case CXCursor_FieldDecl:
    {
      CXString cursor_spelling = clang_getCursorSpelling(cursor);
      CXString type_spelling = clang_getTypeSpelling(clang_getCursorType(cursor));
      concat(out, print(arena, type_spelling));
      concat(out, print(arena, " "));
      concat(out, print(arena, cursor_spelling));
      concat(out, print(arena, "; "));
    } break;

    case CXCursor_UnionDecl:
    {
      concat(out, print(arena, "union {"));
      clang_visitChildren(cursor, printStructVisitor, out);
      concat(out, print(arena, "}; "));
    } break;

    case CXCursor_StructDecl:
    {
      concat(out, print(arena, "struct {"));
      clang_visitChildren(cursor, printStructVisitor, out);
      concat(out, print(arena, "}; "));
    } break;

    invalidDefaultCase;
  }
  return CXChildVisit_Continue;
}

internal void
printStructFields(CXCursor cursor, String *buffer)
{
  clang_visitChildren(cursor, printStructVisitor, buffer);
}

internal CXChildVisitResult
builtinTableVisitor(CXCursor cursor, CXCursor parent, CXClientData client_data)
{
  (void)parent;
  StringBuffer *buffer = (StringBuffer *)client_data;
  CXCursorKind cursor_kind = clang_getCursorKind(cursor);
  switch (cursor_kind)
  {
    case CXCursor_FieldDecl:
    {
      const char *cursor_spelling = clang_getCString(clang_getCursorSpelling(cursor));
      print(buffer, "{\"%s\", &rea_builtins.%s},\n", cursor_spelling, cursor_spelling);
    } break;
  }
  return CXChildVisit_Continue;
}

internal String
generateBuiltinTable(CXCursor cursor)
{
  auto start_string = startString(temp_arena);
  StringBuffer *buffer = start_string.buffer;
  print(buffer, "global_variable BuiltinEntry rea_builtin_names[] = {\n");

  clang_visitChildren(cursor, builtinTableVisitor, start_string.buffer);

  print(buffer, "};");
  String output = endString(start_string);
  return output;
}

internal CXChildVisitResult
topLevelVisitor(CXCursor cursor, CXCursor parent, CXClientData client_data)
{
  Arena *arena = permanent_arena;
  State *state = (State *)client_data;
  (void)parent; (void)client_data;
  TemporaryMemory temp_mem = beginTemporaryMemory(temp_arena);
  CXSourceLocation location = clang_getCursorLocation(cursor);

  unsigned cursor_line;
  CXFile file;
  clang_getExpansionLocation(location, &file, &cursor_line, 0, 0);

  CXChildVisitResult child_visit_result = CXChildVisit_Continue;
  String file_name = print(temp_arena, clang_getFileName(file));
  if (file_name.chars)
  {
    temp_arena->used++;
    CXString path_name0 = clang_File_tryGetRealPathName(file);
    String path_name = print(temp_arena, path_name0);
    if (path_name.chars)
    {
      if (isSubstring(path_name, current_dir, false))
      {
        temp_arena->used++;
        CXString cursor_spelling = clang_getCursorSpelling(cursor);
        CXCursorKind cursor_kind = clang_getCursorKind(cursor);
        CXCursorKind parent_kind = clang_getCursorKind(parent);

        if (state->inside_embedded_struct && parent_kind == CXCursor_TranslationUnit)
        {
          state->inside_embedded_struct = false;
        }

        switch (cursor_kind)
        {
          case CXCursor_MacroExpansion:
          {// check for annotations
            String cursor_string = print(temp_arena, cursor_spelling);
            temp_arena->used++;
            if (equal("forward_declare", cursor_string))
            {
              LocationList *locs = pushStruct(arena, LocationList, true);
              locs->line      = cursor_line;
              locs->next      = state->forward_declare_locations;
              locs->file_name = copyString(arena, file_name);
              state->forward_declare_locations = locs;
            }
            else if (equal("embed_struct", cursor_string))
            {// valid inside a struct only
              LocationList *locs = pushStruct(arena, LocationList, true);
              locs->line      = cursor_line;
              locs->next      = state->embed_locations;
              locs->file_name = copyString(arena, file_name);
              state->embed_locations = locs;
            }
          } break;

          case CXCursor_FunctionDecl:
          {
            for (LocationList *line = state->forward_declare_locations;
                 line;
                 line = line->next)
            {
              b32 match_line = (cursor_line >= line->line) && (cursor_line < line->line+3);
              b32 match_file = equal(file_name, line->file_name);
              if (match_line && match_file)
              {// function was asked to be forward-declared
#if 0
                print(0, "forward declare:"); print(0, cursor_spelling); print(0, "\n");
#endif
                char *signature = printFunctionSignature(temp_arena, cursor);
                fprintf(state->forward_declare_file, "%s", signature);
                break;
              }
            }
          } break;

          case CXCursor_StructDecl:
          {
            String struct_name = print(arena, cursor_spelling);
            for (LocationList *lines = state->embed_locations;
                 lines;
                 lines = lines->next)
            {
              b32 match_line = (cursor_line >= lines->line) && (cursor_line < lines->line+3);
              b32 match_file = equal(file_name, lines->file_name);
              if (match_line && match_file)
              {// struct was asked to be embedded
#if 0
                print(0, "embed: "); print(0, struct_name); print(0, "\n");
#endif
                EmbedStructs *new_struct = pushStruct(arena, EmbedStructs, true);
                new_struct->next   = state->embed_structs;
                new_struct->name   = struct_name;
                new_struct->fields = String{.chars = (char *)getNext(arena)};
                printStructFields(cursor, &new_struct->fields);
                state->embed_structs = new_struct;
                state->inside_embedded_struct = true;
                break;
              }
            }

            if (equal(struct_name, "ReaBuiltins"))
            {
              // rea builtins generation.
              String output = generateBuiltinTable(cursor);

              char *builtin_file_name = "generated/rea_builtin.cpp";
              FILE *builtin_file;
              if (fopen_s(&builtin_file, builtin_file_name, "w") == 0)
              {
                fprintf(builtin_file, "%s\n", output.chars);
              }
              else
              {
                printf("cannot open file %s", builtin_file_name);
                exit(1);
              }
            }
          } break;

          default:
          {} break;
        }
      }
    }
  }

  endTemporaryMemory(temp_mem);
  return child_visit_result;
}

int main()
{
  Arena temp_arena_ = newArena(megaBytes(8), (void *)teraBytes(3));
  VirtualAlloc(temp_arena_.base, temp_arena_.cap, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
  temp_arena = &temp_arena_;

  Arena permanent_arena_ = newArena(megaBytes(128), (void *)teraBytes(2));
  VirtualAlloc(permanent_arena_.base, permanent_arena_.cap, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
  permanent_arena = &permanent_arena_;
  Arena *arena = permanent_arena;

  char *current_dir_base = (char*)getNext(arena);
  i32 current_dir_length = GetCurrentDirectory(arena->cap, (char *)arena->base);
  arena->used += current_dir_length + 1;
  current_dir = {current_dir_base, current_dir_length};

  // FileList list = getAllCppFilesInDirectory();
  CXIndex index = clang_createIndex(0, 0);

  CXTranslationUnit unit = clang_parseTranslationUnit(index, "engine.cpp", nullptr, 0, nullptr, 0, CXTranslationUnit_DetailedPreprocessingRecord);
  CXCursor cursor = clang_getTranslationUnitCursor(unit);

  State state = {};
  char *forward_declare_file_name = "generated/engine_forward.h";
  if (fopen_s(&state.forward_declare_file, forward_declare_file_name, "w") == 0)
  {
    clang_visitChildren(cursor, topLevelVisitor, &state);

    FILE *embed_file = {};
    char *embed_file_name = "generated/engine_embed.h";
    if (fopen_s(&embed_file, embed_file_name, "w") == 0)
    {
      for (EmbedStructs *embed = state.embed_structs; embed; embed = embed->next)
      {
        String macro_ = print(temp_arena, "#define embed_");
        String *macro = &macro_;
        concat(macro, print(temp_arena, embed->name));
        concat(macro, print(temp_arena, "(name) union { "));
        concat(macro, print(temp_arena, embed->name));
        concat(macro, print(temp_arena, " name; struct { "));
        concat(macro, print(temp_arena, embed->fields));
        concat(macro, print(temp_arena, " };"));
        concat(macro, print(temp_arena, " };"));
        fprintf(embed_file, "%s\n", macro->chars);
      }
    }
    else
    {
      printf("cannot open file %s", embed_file_name);
      exit(1);
    }

    fclose(state.forward_declare_file);
  }
  else
  {
    printf("cannot open file %s", forward_declare_file_name);
    exit(1);
  }
  return 0;
}

#include <windows.h>
#include <malloc.h>
#include "utils.h"
#include "clang-c/Index.h"

global_variable MemoryArena *permanent_arena;
global_variable MemoryArena *temp_arena;
global_variable char *current_dir;

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
  s32    count;
  char **files;
};

internal FileList
getAllCppFilesInDirectory()
{
  FileList out = {};
  for (s32 iter = 0; iter < 2; iter++)
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
      s32 file_id = 0;
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

inline char *
printToBuffer(MemoryArena *buffer, CXString string)
{
  char *out = 0;
  const char *cstring = clang_getCString(string);
  if (cstring)
  {
    out = printToBuffer(buffer, (char *)cstring);
    clang_disposeString(string);
  }
  return out;
}

struct LocationList
{
  unsigned      line;
  char         *file_name;
  LocationList *next;
};

struct State
{
  FILE         *out_file;
  LocationList *forward_declare_locations;
};

internal char *
printFunctionSignature(MemoryArena *arena, CXCursor cursor)
{
  char *out = (char *)getNext(arena);

  CXType type = clang_getCursorType(cursor);
  printToBuffer(arena, clang_getTypeSpelling(clang_getResultType(type)));
  printToBuffer(arena, " ");

  printToBuffer(arena, clang_getCursorSpelling(cursor));

  printToBuffer(arena, "(");
  int num_args = clang_Cursor_getNumArguments(cursor);
  for (int i = 0; i < num_args; ++i)
  {
    CXCursor arg_cursor = clang_Cursor_getArgument(cursor, i);
    printToBuffer(arena, clang_getTypeSpelling(clang_getArgType(type, i)));
    printToBuffer(arena, " ");
    printToBuffer(arena, clang_getCursorSpelling(arg_cursor));
    if (i != num_args-1)
    {
      printToBuffer(arena, ", ");
    }
  }
  printToBuffer(arena, ");\n\0");

  return out;
}

int main()
{
  MemoryArena temp_arena_ = newArena(megaBytes(8), (void *)teraBytes(3));
  VirtualAlloc(temp_arena_.base, temp_arena_.cap, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
  temp_arena = &temp_arena_;

  MemoryArena permanent_arena_ = newArena(megaBytes(128), (void *)teraBytes(2));
  VirtualAlloc(permanent_arena_.base, permanent_arena_.cap, MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE);
  permanent_arena = &permanent_arena_;

  current_dir = (char *)getNext(permanent_arena);
  permanent_arena->used += GetCurrentDirectory(permanent_arena->cap, (char *)permanent_arena->base);
  *(permanent_arena->base + permanent_arena->used++) = 0;

  // FileList list = getAllCppFilesInDirectory();
  CXIndex index = clang_createIndex(0, 0);

  CXTranslationUnit unit = clang_parseTranslationUnit(index, "engine.cpp", nullptr, 0, nullptr, 0, CXTranslationUnit_DetailedPreprocessingRecord);
  CXCursor cursor = clang_getTranslationUnitCursor(unit);

  State state = {};
  if (fopen_s(&state.out_file, "generated/engine_forward.h", "w") == 0)
  {
    clang_visitChildren(
      cursor,
      [](CXCursor cursor, CXCursor parent, CXClientData client_data)
      {
        State *state = (State *)client_data;
        (void)parent; (void)client_data;
        TemporaryMemory temp_mem = beginTemporaryMemory(temp_arena);
        CXSourceLocation location = clang_getCursorLocation(cursor);

        unsigned line;
        CXFile file;
        clang_getExpansionLocation(location, &file, &line, 0, 0);

        CXChildVisitResult child_visit_result = CXChildVisit_Continue;
        if (char *file_name = printToBuffer(temp_arena, clang_getFileName(file)))
        {
          temp_arena->used++;
          CXString path_name0 = clang_File_tryGetRealPathName(file);
          if (char *path_name = printToBuffer(temp_arena, path_name0))
          {
            if (isSubstring(path_name, current_dir, false))
            {
              CXString cursor_spelling0 = clang_getCursorSpelling(cursor);
              CXCursorKind kind = clang_getCursorKind(cursor);

              switch (kind)
              {
                case CXCursor_MacroExpansion:
                {// check for annotations
                  char *cursor_spelling = printToBuffer(temp_arena, cursor_spelling0);
                  if (equal("forward_declare", cursor_spelling))
                  {
                    LocationList *locations = pushStruct(permanent_arena, LocationList, true);
                    locations->line      = line;
                    locations->next      = state->forward_declare_locations;
                    locations->file_name = printToBuffer(permanent_arena, file_name);
                    permanent_arena->used++;
                    state->forward_declare_locations = locations;
                  }
                } break;

                case CXCursor_FunctionDecl:
                {
                  for (LocationList *lines = state->forward_declare_locations;
                       lines;
                       lines = lines->next)
                  {
                    b32 match_line = (line > lines->line && line < lines->line+3);
                    b32 match_file = equal(file_name, lines->file_name);
                    if (match_line && match_file)
                    {// function was asked to be forward-declared
#if 0
                      printf("forward declare: %s\n", printToBuffer(temp_arena, cursor_spelling0));
#endif
                      char *signature = printFunctionSignature(temp_arena, cursor);
                      fprintf(state->out_file, "%s", signature);
                      break;
                    }
                  }
                } break;

                default: break;
              }
            }
          }
        }

        endTemporaryMemory(temp_mem);
        return child_visit_result;
      },
      &state);

    fclose(state.out_file);
  }
  return 0;
}

#include <windows.h>
#include <malloc.h>
#include "utils.h"

// todo: does enum automatically increment???
enum TokenCategory
{
  // 0-255 reserved for single-char ASCII types.
  TC_Special       = 256,
  TC_PairingOpen   = 257,
  TC_PairingClose  = 258,
  TC_Alphanumeric  = 259,
  TC_StringLiteral = 261,
};

struct Token
{
  String        text;
  s32           line;
  s32           column;
  TokenCategory cat;
  operator String() { return text; }
};

struct Tokenizer
{
  char  *at;
  Token  last_token;
  s32    line;
  s32    column;

  String directory;
};

inline char
nextChar(Tokenizer *tk)
{
  char out;
  if (*tk->at)
  {
    out = *tk->at++;
    if (out == '\n')
    {
      tk->line++;
      tk->column = 1;
    }
    else
      tk->column++;
  }
  else
    out = 0;
  return out;
}

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
        nextChar(tk);
      } break;

      case ';':
      {
        if (*(tk->at+1) == ';')
        {
          nextChar(tk);
          nextChar(tk);
          while ((*tk->at) && (*tk->at != '\n'))
            nextChar(tk);
        }
        else
        {
          stop = true;
        }
      } break;

      default:
          stop = true;
    }
  }
}

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

int main()
{
  FileList list = getAllCppFilesInDirectory();
  for (s32 file_id = 0; file_id < list.count; file_id++)
  {
    readEntireFile(list.files[file_id]);
  }
  return 0;
}

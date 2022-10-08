#include <stdio.h>
#include <malloc.h>
#include "utils.h"

#if 0
struct Tokenizer
{
    char *at;
};

inline void
requireString(Tokenizer &tokenizer)
{
    tokenizer->at;
}
#endif

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

int main()
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

    return(0);
}

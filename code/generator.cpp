#include <stdio.h>
#include <malloc.h>
#include "utils.h"

char *vector_structs[] = {"Axiom", "Operator", "Atom", "Type"};
char *linked_list_structs[] = {"String"};

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

int main()
{
    const char *data_structures[] = {"Vector", "List"};
    for (int i = 0;
         i < arrayCount(data_structures);
         i++)
    {
        const char *data_structure = data_structures[i];
        char input_name[256];
        sprintf(input_name, "templated_%s.h", data_structure);
        char *templated_code = readEntireFile(input_name);
        char output_name[256];
        sprintf(output_name, "generated_%s.h", data_structure);
        FILE *output;
        char **structs = (i == 0) ? vector_structs : linked_list_structs;
        s32 struct_count = (i == 0) ? arrayCount(vector_structs) : arrayCount(linked_list_structs);
        if (fopen_s(&output, output_name, "w") == 0)
        {
            fprintf(output, "#include \"utils.h\" \n");
            fprintf(output, "#include \"memory.h\" \n");
            fprintf(output, "#include \"intrinsics.h\" \n");
            for (int i = 0;
                 i < struct_count;
                 i++)
            {
                const char *struct_name = structs[i];
                char *at = templated_code;
                while (*at)
                {
                    if ((*at == '.') && (*(at+1) == '.') && (*(at+2) == '.'))
                    {
                        at += 2;
                        fprintf(output, "%s", struct_name);
                    }
                    else
                    {
                        fprintf(output, "%c", *at);
                    }
                    at++;
                }
            }
            fclose(output);
        }
        else
        {
            fprintf(stderr, "Cannot open file %s! \n", output_name);
            return(1);
        }
    }
    return (0);
}

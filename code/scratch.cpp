#include <stdio.h>
#include "utils.h"

int main(int argc, char **argv)
{
    for (int x = 0; x <= 1; x++)
    {
        for (int y = 0; y <= 1; y++)
        {
            printf("%d %d\n", (!x || y), (!(x || y)));
        }
    }
}

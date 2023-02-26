#include "utils.h"

internal void *
bufGrow_(void *buffer, size_t new_len, size_t item_size)
{
  size_t new_cap = maximum(bufCap(buffer)*2, new_len);
  size_t new_size = sizeof(BufferHeader)+new_cap*item_size;
  BufferHeader *new_header = 0;
  if (buffer)
  {
    new_header = (BufferHeader *)realloc(bufHeader_(buffer), new_size);
  }
  else
  {
    new_header = (BufferHeader *)malloc(new_size);
    new_header->len = 0;
  }
  new_header->cap = new_cap;
  buffer = new_header->items;
  assert(bufCap(buffer) >= new_len);
  return buffer;
}

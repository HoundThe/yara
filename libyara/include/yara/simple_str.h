#ifndef _SIMPLESTR_H
#define _SIMPLESTR_H

#include <yara/types.h>

// Simple dynamic string implementation for more readable code
// Could be much more optimized
typedef struct _SIMPLE_STR
{
  uint32_t len;
  uint32_t cap;
  char* str;
} SIMPLE_STR, *PSIMPLE_STR;

SIMPLE_STR* sstr_new(const char* s);
void sstr_free(SIMPLE_STR* str);
bool sstr_appendf(SIMPLE_STR* str, const char* fmt, ...);

#endif
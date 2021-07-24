#include <stdarg.h>
#include <string.h>
#include <yara/mem.h>
#include <yara/simple_str.h>
#include <yara/types.h>

SIMPLE_STR* sstr_new(const char* s)
{
  SIMPLE_STR* str = yr_calloc(1, sizeof(SIMPLE_STR));
  if (!str)
    return NULL;

  if (s)
  {
    uint32_t slen = strlen(s);
    str->str = yr_malloc(slen + 1);
    if (!str->str)
    {
      yr_free(str);
      return NULL;
    }
    str->len = slen;
    str->cap = slen;
    memcpy(str->str, s, slen + 1);
  }
  return str;
}

void sstr_free(SIMPLE_STR* str)
{
  if (str)
  {
    yr_free(str->str);
    yr_free(str);
  }
}

bool sstr_appendf(SIMPLE_STR* str, const char* fmt, ...)
{
  va_list ap, ap2;
  va_start(ap, fmt);
  // Create copy because list will get consumed when getting the final length
  va_copy(ap2, ap);

  int size = vsnprintf(NULL, 0, fmt, ap);
  if (size < 0)  // Error
    return false;

  if (str->cap < str->len + size + 1)  // + 1 for NULL
  {
    // Arbitrary 64 constant to mitigate amount of reallocations
    char* tmp = yr_realloc(str->str, str->len + size + 64);
    if (!tmp)
    {
      return false;
    }
    str->str = tmp;
    str->cap = str->len + size + 64;
  }

  str->len += vsnprintf(str->str + str->len, str->cap, fmt, ap2);

  va_end(ap);
  return true;
}

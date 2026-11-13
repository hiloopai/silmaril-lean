// kind: reactor
// lang: c-bindgen
// A C reactor (wasi-sdk 27, wasm32-wasip1) with wit-bindgen 0.62.0 C bindings for textual.wit:
// strings and lists through cabi_realloc, return pointers and post-return functions, stdio
// through the adapter, and _initialize.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "textual.h"

void exports_textual_shout(textual_string_t *s, textual_string_t *ret) {
  uint8_t *p = malloc(s->len + 1);
  for (size_t i = 0; i < s->len; i++) p[i] = (uint8_t)toupper(s->ptr[i]);
  p[s->len] = '!';
  ret->ptr = p;
  ret->len = s->len + 1;
  fprintf(stderr, "shout: %zu bytes\n", s->len);
  textual_string_free(s);
}

int64_t exports_textual_sum(textual_list_s32_t *xs) {
  int64_t t = 0;
  for (size_t i = 0; i < xs->len; i++) t += xs->ptr[i];
  printf("sum of %zu\n", xs->len);
  fflush(stdout);
  textual_list_s32_free(xs);
  return t;
}

void exports_textual_split(textual_string_t *s, textual_list_string_t *ret) {
  size_t n = 0, cap = 4;
  textual_string_t *out = malloc(cap * sizeof *out);
  size_t i = 0;
  while (i < s->len) {
    while (i < s->len && s->ptr[i] == ' ') i++;
    size_t j = i;
    while (j < s->len && s->ptr[j] != ' ') j++;
    if (j > i) {
      if (n == cap) { cap *= 2; out = realloc(out, cap * sizeof *out); }
      out[n].ptr = malloc(j - i);
      memcpy(out[n].ptr, s->ptr + i, j - i);
      out[n].len = j - i;
      n++;
    }
    i = j;
  }
  ret->ptr = out;
  ret->len = n;
  textual_string_free(s);
}

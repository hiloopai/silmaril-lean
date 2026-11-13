// kind: command
// lang: c
// A C command (wasi-sdk 27, wasm32-wasip1): arguments, environment, stdin, stdout, stderr, exit.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  printf("argc %d\n", argc - 1);
  for (int i = 1; i < argc; i++) printf("arg %s\n", argv[i]);
  const char *e = getenv("SIL_P1");
  printf("env %s\n", e ? e : "(none)");
  char buf[256];
  size_t total = 0, lines = 0;
  while (fgets(buf, sizeof buf, stdin)) { total += strlen(buf); lines++; }
  fprintf(stderr, "stdin %zu bytes %zu lines\n", total, lines);
  return total > 10 ? 4 : 0;
}

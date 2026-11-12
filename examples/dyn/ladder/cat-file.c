#include <errno.h>
#include <error.h>
#include <stdio.h>

/* cat FILE: copy one file to standard output; on failure, report and exit 1. */
int main(int argc, char **argv) {
  char buf[1024];
  size_t n;
  if (argc != 2)
    return 2;
  FILE *f = fopen(argv[1], "r");
  if (!f)
    error(1, errno, "%s", argv[1]);
  while ((n = fread(buf, 1, sizeof buf, f)) > 0)
    fwrite(buf, 1, n, stdout);
  fclose(f);
  return 0;
}

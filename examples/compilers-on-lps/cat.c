/* cat: copy stdin to stdout until end of file, retrying short writes; exit 0 at end of
   file, 1 if a read or write fails (Silmaril/Compile/Examples/LPS/Cat.lean). */
#include <unistd.h>

static char buf[4096];

int main(void) {
  for (;;) {
    ssize_t n = read(0, buf, sizeof buf);
    if (n == 0) return 0;
    if (n < 0) return 1;
    char *p = buf;
    while (n > 0) {
      ssize_t w = write(1, p, (size_t)n);
      if (w <= 0) return 1;
      p += w;
      n -= w;
    }
  }
}

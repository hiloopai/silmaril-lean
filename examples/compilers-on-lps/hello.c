/* hello: write "hello, world\n" to stdout, retrying short writes; exit 0, or 1 if a write
   fails (Silmaril/Compile/Examples/LPS/Hello.lean). */
#include <unistd.h>

static const char msg[] = "hello, world\n";

int main(void) {
  const char *p = msg;
  size_t left = sizeof msg - 1;
  while (left > 0) {
    ssize_t n = write(1, p, left);
    if (n <= 0) return 1;
    p += n;
    left -= (size_t)n;
  }
  return 0;
}

#include <unistd.h>

/* Copy standard input to standard output, as GNU cat does: read(2) and write(2). */
int main(void) {
  char buf[1024];
  ssize_t n;
  while ((n = read(0, buf, sizeof buf)) > 0)
    write(1, buf, n);
  return 0;
}

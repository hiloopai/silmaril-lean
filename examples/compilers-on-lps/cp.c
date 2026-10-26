/* cp SRC DST: copy the file SRC to DST (created or truncated), retrying short writes;
   exit 0, 2 on a wrong argument count, 1 if an open, read, write or close fails
   (Silmaril/Compile/Examples/LPS/Cp.lean). */
#include <fcntl.h>
#include <unistd.h>

static char buf[4096];

int main(int argc, char **argv) {
  if (argc != 3) return 2;
  int in = open(argv[1], O_RDONLY);
  if (in < 0) return 1;
  int out = open(argv[2], O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (out < 0) return 1;
  for (;;) {
    ssize_t n = read(in, buf, sizeof buf);
    if (n == 0) break;
    if (n < 0) return 1;
    char *p = buf;
    while (n > 0) {
      ssize_t w = write(out, p, (size_t)n);
      if (w <= 0) return 1;
      p += w;
      n -= w;
    }
  }
  if (close(out) != 0) return 1;
  return 0;
}

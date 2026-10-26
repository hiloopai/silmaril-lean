/* malloc: allocate 1 MiB, fill it and check it; print "ok\n" and exit 0, or, when the
   allocation is refused (allocation budget, spurious mmap/brk refusal), print "oom\n" and
   exit 2; 1 if a write fails (Silmaril/Compile/Examples/LPS/Malloc.lean). */
#include <stdlib.h>
#include <unistd.h>

#define N (1u << 20)

static int put_all(const char *p, size_t n) {
  while (n > 0) {
    ssize_t w = write(1, p, n);
    if (w <= 0) return 1;
    p += w;
    n -= (size_t)w;
  }
  return 0;
}

int main(void) {
  volatile unsigned char *p = malloc(N);
  if (!p) return put_all("oom\n", 4) ? 1 : 2;
  for (unsigned i = 0; i < N; i++) p[i] = (unsigned char)i;
  unsigned long sum = 0;
  for (unsigned i = 0; i < N; i++) sum += p[i];
  free((void *)p);
  if (sum != (N / 256) * 32640UL) return 3;
  return put_all("ok\n", 3) ? 1 : 0;
}

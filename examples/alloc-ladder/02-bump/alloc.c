/* Rung 02: bump allocation over a fixed static arena; free is a no-op.
   No alignment promise beyond 1. */
#include "alloc.h"
#define ARENA 4096
static u8 arena[ARENA];
static usize used;
void *malloc(usize n) {
  usize u = used;
  if (n > ARENA - u) return 0;
  used = u + n;
  return arena + u;
}
void free(void *p) { }

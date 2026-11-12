/* Rung 03: bump allocation with 16-byte alignment.  Invariant: used % 16 == 0,
   so n <= ARENA - used implies round16(n) <= ARENA - used. */
#include "alloc.h"
#define ARENA 4096
static u8 arena[ARENA] __attribute__((aligned(16)));
static usize used;
void *malloc(usize n) {
  usize u = used;
  if (n > ARENA - u) return 0;
  used = u + ((n + 15) & ~(usize)15);
  return arena + u;
}
void free(void *p) { }

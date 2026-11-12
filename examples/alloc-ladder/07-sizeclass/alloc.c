/* Rung 07: segregated size classes.  Four classes of payload size 16, 32, 64 and
   128 bytes, each with a LIFO free list; fresh blocks come from a 4096-byte bump
   arena.  Every block has a 16-byte header whose first word is its payload size,
   so free knows the class.  Requests above 128 bytes fail.  The class heads are
   four separate globals (no array), selected by comparisons. */
#include "alloc.h"
#define ARENA 4096
static u8 arena[ARENA] __attribute__((aligned(16)));
static usize used;
static void *h16, *h32, *h64, *h128;

static void **head_of(usize sz) {
  if (sz == 16) return &h16;
  if (sz == 32) return &h32;
  if (sz == 64) return &h64;
  return &h128;
}

void *malloc(usize n) {
  usize sz;
  if (n <= 16) sz = 16;
  else if (n <= 32) sz = 32;
  else if (n <= 64) sz = 64;
  else if (n <= 128) sz = 128;
  else return 0;
  void **h = head_of(sz);
  void *p = *h;
  if (p) { *h = *(void **)p; return p; }
  usize u = used;
  if (sz + 16 > ARENA - u) return 0;
  used = u + sz + 16;
  *(usize *)(arena + u) = sz;
  return arena + u + 16;
}

void free(void *p) {
  if (!p) return;
  void **h = head_of(*((usize *)p - 2));
  *(void **)p = *h;
  *h = p;
}

/* Rung 05: first-fit over an explicit free list of headed blocks, with
   splitting and without coalescing.  A block is a 16-byte header (payload size,
   a multiple of 16, and the free-list link) followed by its payload; payloads
   are 16-byte aligned.  The free list starts as one block spanning the arena,
   initialised statically (no init code).  free pushes the block at the head. */
#include "alloc.h"
#define ARENA 4096
struct hdr { usize size; struct hdr *next; };
static union { struct hdr h; u8 b[ARENA]; } heap __attribute__((aligned(16))) =
  { .h = { ARENA - sizeof(struct hdr), 0 } };
static struct hdr *freelist = &heap.h;
void *malloc(usize n) {
  if (n > ARENA) return 0;
  usize need = (n + 15) & ~(usize)15;
  struct hdr **prev = &freelist;
  for (struct hdr *h = freelist; h; prev = &h->next, h = h->next) {
    if (h->size < need) continue;
    if (h->size >= need + 2 * sizeof(struct hdr)) {
      struct hdr *r = (struct hdr *)((u8 *)(h + 1) + need);
      r->size = h->size - need - sizeof(struct hdr);
      r->next = h->next;
      h->size = need;
      *prev = r;
    } else {
      *prev = h->next;
    }
    return h + 1;
  }
  return 0;
}
void free(void *p) {
  if (!p) return;
  struct hdr *h = (struct hdr *)p - 1;
  h->next = freelist;
  freelist = h;
}

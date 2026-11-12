/* Rung 06: rung 05 with an address-ordered free list and coalescing of
   adjacent free blocks in free. */
#include "alloc.h"
#define ARENA 4096
struct hdr { usize size; struct hdr *next; };
static union { struct hdr h; u8 b[ARENA]; } heap __attribute__((aligned(16))) =
  { .h = { ARENA - sizeof(struct hdr), 0 } };
static struct hdr *freelist = &heap.h;
static inline u8 *end_of(struct hdr *h) { return (u8 *)(h + 1) + h->size; }
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
  struct hdr *prev = 0, *cur = freelist;
  while (cur && cur < h) { prev = cur; cur = cur->next; }
  h->next = cur;
  if (cur && end_of(h) == (u8 *)cur) { h->size += sizeof(struct hdr) + cur->size; h->next = cur->next; }
  if (prev) {
    prev->next = h;
    if (end_of(prev) == (u8 *)h) { prev->size += sizeof(struct hdr) + h->size; prev->next = h->next; }
  } else {
    freelist = h;
  }
}

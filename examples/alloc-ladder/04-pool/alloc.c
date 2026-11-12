/* Rung 04: fixed-size blocks (64 bytes, 64 of them) with an intrusive LIFO free
   list.  Never-used blocks are handed out by a bump index, so there is no
   initialisation loop.  Requests above the block size fail. */
#include "alloc.h"
#define BS 64
#define NB 64
static u8 pool[NB * BS] __attribute__((aligned(16)));
static void *head;   /* free list of returned blocks; the link is the first word */
static usize next;   /* blocks [next, NB) have never been handed out */
void *malloc(usize n) {
  if (n > BS) return 0;
  void *p = head;
  if (p) { head = *(void **)p; return p; }
  if (next >= NB) return 0;
  p = pool + next * BS;
  next++;
  return p;
}
void free(void *p) {
  if (!p) return;
  *(void **)p = head;
  head = p;
}

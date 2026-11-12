/* Rung 08t: textbook boundary tags (Knuth; CS:APP 9.9).  A 4096-byte arena of
   blocks whose sizes are multiples of 16 (at least 32).  Every block, free or
   allocated, has a header and a footer word holding its size with the allocated
   bit (bit 0); the arena is bracketed by an allocated prologue footer and an
   allocated epilogue header.  A free block also holds its list links (next at
   +8, prev at +16).  One doubly linked free list, first fit, the tail of a fit
   that leaves at least 32 bytes is handed out.  free reads the tags of both
   neighbours, allocated or free, and coalesces in constant time. */
#include "alloc.h"
#define ARENA 4096
struct blk { usize tag; struct blk *next, *prev; };
/* Blocks start 8 bytes past a 16-byte boundary and payloads right after the
   header word, so payloads are 16-aligned.  heap[0] is the prologue footer,
   heap[1..510] one free block of 4080 bytes, heap[511] the epilogue header. */
static usize heap[ARENA / 8] __attribute__((aligned(16))) = {
  [0] = 1,                              /* prologue footer: size 0, allocated */
  [1] = ARENA - 16,                     /* the free block's header */
  [ARENA / 8 - 2] = ARENA - 16,         /* its footer */
  [ARENA / 8 - 1] = 1,                  /* epilogue header: size 0, allocated */
};
static struct blk *flist = (struct blk *)&heap[1];

static usize size(usize t) { return t & ~(usize)15; }
static usize *foot(struct blk *b) { return (usize *)((u8 *)b + size(b->tag) - 8); }

static void unlink(struct blk *x) {
  struct blk *n = x->next, *p = x->prev;
  if (p) p->next = n; else flist = n;
  if (n) n->prev = p;
}

void *malloc(usize n) {
  if (n > ARENA) return 0;
  usize a = (n + 16 + 15) & ~(usize)15;  /* header + payload + footer */
  if (a < 32) a = 32;
  struct blk *b;
  for (b = flist; b; b = b->next)
    if (b->tag >= a) break;             /* free blocks have bit 0 clear */
  if (!b) return 0;
  usize s = b->tag;
  if (s - a >= 32) {
    usize ns = s - a;
    b->tag = ns;
    *foot(b) = ns;
    struct blk *r = (struct blk *)((u8 *)b + ns);
    r->tag = a | 1;
    *foot(r) = a | 1;
    return (u8 *)r + 8;
  }
  unlink(b);
  b->tag = s | 1;
  *foot(b) = s | 1;
  return (u8 *)b + 8;
}

void free(void *p) {
  if (!p) return;
  struct blk *b = (struct blk *)((u8 *)p - 8);
  usize s = size(b->tag);
  struct blk *nb = (struct blk *)((u8 *)b + s);
  if (!(nb->tag & 1)) {                 /* the next block's header */
    unlink(nb);
    s += nb->tag;
  }
  usize pt = *((usize *)b - 1);         /* the previous block's footer */
  if (!(pt & 1)) {
    struct blk *pb = (struct blk *)((u8 *)b - pt);
    unlink(pb);
    s += pt;
    b = pb;
  }
  b->tag = s;
  *(usize *)((u8 *)b + s - 8) = s;
  b->next = flist;
  b->prev = 0;
  if (flist) flist->prev = b;
  flist = b;
}

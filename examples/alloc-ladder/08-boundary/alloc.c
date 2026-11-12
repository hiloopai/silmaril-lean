/* Rung 08: boundary tags.  A 4096-byte arena of blocks whose sizes are multiples
   of 16 (at least 32).  Every block starts with its size word; a free block also
   holds its free-list links (next at +8, prev at +16) and a footer (its size, in
   its last word).  One doubly linked free list, first fit; a fit that leaves at
   least 32 bytes is split and the tail is handed out.  free coalesces in constant
   time with both neighbours: the side tables first[] and last[] mark the first
   and the last 16-byte granule of every free block, so free never reads the
   header or the footer of an allocated neighbour (the client's token owns those).
   The initial state is one free block covering the arena (static data). */
#include "alloc.h"
#define ARENA 4096
#define NG (ARENA / 16)
struct blk { usize size; struct blk *next, *prev; };
static usize heap[ARENA / 8] __attribute__((aligned(16))) = { [0] = ARENA, [ARENA / 8 - 1] = ARENA };
static u8 first[NG] = { [0] = 1 };
static u8 last[NG] = { [NG - 1] = 1 };
static struct blk *flist = (struct blk *)heap;

static usize gran(struct blk *b) { return (usize)((u8 *)b - (u8 *)heap) >> 4; }
static void setfoot(struct blk *b, usize s) { *(usize *)((u8 *)b + s - 8) = s; }

static void unlink(struct blk *x) {
  struct blk *n = x->next, *p = x->prev;
  if (p) p->next = n; else flist = n;
  if (n) n->prev = p;
}

void *malloc(usize n) {
  if (n > ARENA) return 0;
  usize a = ((n + 15) & ~(usize)15) + 16;
  if (a < 32) a = 32;
  struct blk *b;
  for (b = flist; b; b = b->next)
    if (b->size >= a) break;
  if (!b) return 0;
  usize s = b->size, g = gran(b);
  if (s - a >= 32) {
    usize ns = s - a;
    b->size = ns;
    setfoot(b, ns);
    last[g + ns / 16 - 1] = 1;
    last[g + s / 16 - 1] = 0;
    usize *r = (usize *)((u8 *)b + ns);
    *r = a;
    return r + 2;
  }
  unlink(b);
  first[g] = 0;
  last[g + s / 16 - 1] = 0;
  return (usize *)b + 2;
}

void free(void *p) {
  if (!p) return;
  struct blk *b = (struct blk *)((u8 *)p - 16);
  usize s = b->size, g = gran(b), e = g + s / 16;
  if (e < NG && first[e]) {
    struct blk *nb = (struct blk *)((u8 *)heap + e * 16);
    unlink(nb);
    first[e] = 0;
    s += nb->size;
  }
  if (g > 0 && last[g - 1]) {
    usize ps = *(usize *)((u8 *)b - 8);
    struct blk *pb = (struct blk *)((u8 *)b - ps);
    unlink(pb);
    last[g - 1] = 0;
    b = pb;
    g = gran(b);
    s += ps;
  }
  b->size = s;
  setfoot(b, s);
  first[g] = 1;
  last[g + s / 16 - 1] = 1;
  b->next = flist;
  b->prev = 0;
  if (flist) flist->prev = b;
  flist = b;
}

/* Shared self-test driver for the allocator rungs.  Per-rung behaviour comes
   from -D flags set by each rung's build.sh:
     NEVER        every malloc returns NULL
     ALIGN=a      every non-NULL result is a multiple of a
     REUSE        a freed block can be handed out again (pool, first-fit)
     MAXREQ=n     requests above n fail (pool block size)            */
#include "alloc.h"
#ifndef ALIGN
#define ALIGN 1
#endif
#define K 24
static u8 *blk[K];
static usize len[K];

__attribute__((unused)) static int disjoint(void) {
  for (int i = 0; i < K; i++)
    for (int j = 0; j < K; j++)
      if (i != j && blk[i] && blk[j] && blk[i] < blk[j] + len[j] && blk[j] < blk[i] + len[i])
        return 0;
  return 1;
}

int cmain(long *sp) {
#ifdef NEVER
  for (usize n = 0; n < 100; n++) rt_check(malloc(n) == 0, "never");
  free(0);
  return rt_finish("never");
#else
  for (int i = 0; i < K; i++) {
    len[i] = (usize)(i * 7 % 48) + 1;
    blk[i] = malloc(len[i]);
    rt_check(blk[i] != 0, "small malloc succeeds");
    rt_check(((usize)blk[i] % ALIGN) == 0, "aligned");
    for (usize b = 0; b < len[i]; b++) blk[i][b] = (u8)(i + 1);
  }
  rt_check(disjoint(), "disjoint");
  for (int i = 0; i < K; i++)
    for (usize b = 0; b < len[i]; b++) rt_check(blk[i][b] == (u8)(i + 1), "contents kept");
  rt_check(malloc((usize)-1) == 0, "huge fails");
  rt_check(malloc((usize)-16) == 0, "huge-16 fails");
#ifdef MAXREQ
  rt_check(malloc(MAXREQ + 1) == 0, "over block size fails");
#endif
  for (int i = 0; i < K; i += 2) { free(blk[i]); blk[i] = 0; }
  free(0);
#ifdef REUSE
  for (int i = 0; i < K; i += 2) {
    len[i] = 8;
    blk[i] = malloc(len[i]);
    rt_check(blk[i] != 0, "reuse after free");
    for (usize b = 0; b < len[i]; b++) blk[i][b] = (u8)(i + 1);
  }
  rt_check(disjoint(), "disjoint after reuse");
  /* exhaust, free everything, allocate again */
  usize got = 0;
  while (malloc(32)) got++;
  rt_check(got > 0, "exhaust");
#endif
  return rt_finish("alloc");
#endif
}

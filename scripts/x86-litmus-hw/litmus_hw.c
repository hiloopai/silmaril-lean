/* Run x86 litmus tests on the host CPU and count outcomes.

   Each test runs N iterations. Before each iteration thread 0 resets the shared
   locations; all threads then meet at a spinning barrier (a `lock xadd` and a
   spin on its counter, so the reset is globally visible) and wait a small,
   per-thread pseudo-random delay before the test body, so that the bodies
   overlap at varying offsets. Test bodies are inline assembly with exactly the
   instructions of the litmus test (plain `mov`, `mfence`, `xchg`, `movnti`,
   `inc`, `lock inc`); the compiler sees only registers and memory clobbers.

   Build: cc -O2 -pthread litmus_hw.c -o litmus_hw
   Run:   ./litmus_hw [iterations]   (prints one line per test and outcome)

   Each line is `test outcome count`. The verdicts the models give for each
   outcome are recorded in README.md next to this file; check.py compares. */
#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXT 4
typedef struct {
  volatile uint64_t x, pad0[7];
  volatile uint64_t y, pad1[7];
  volatile uint64_t cnt, pad2[7];
} __attribute__((aligned(64))) shared_t;

static shared_t S;
/* An 8-byte slot that straddles a cache-line boundary (offset 60 of a 128-byte
   aligned block). */
static unsigned char line2[128] __attribute__((aligned(128)));
#define SPLIT ((volatile uint64_t *)(line2 + 60))

static volatile uint64_t bar_count;
static int nthreads;
static long iters;
static uint64_t res[MAXT][2]; /* per iteration result registers, reused */
static unsigned *hist;       /* outcome histogram, indexed by encoded outcome */
static int test_id;

static inline void barrier(long it) {
  __atomic_fetch_add(&bar_count, 1, __ATOMIC_SEQ_CST);
  uint64_t target = (uint64_t)(it + 1) * nthreads;
  while (__atomic_load_n(&bar_count, __ATOMIC_ACQUIRE) < target)
    __builtin_ia32_pause();
}

static inline void delay(unsigned *seed) {
  *seed = *seed * 1103515245u + 12345u;
  unsigned d = (*seed >> 16) & 63;
  for (volatile unsigned i = 0; i < d; i++) {
  }
}

/* r0, r1: per-thread result registers. */
static void body(int test, int t, uint64_t *r0, uint64_t *r1) {
  uint64_t a = 0, b = 0;
  volatile uint64_t *x = &S.x, *y = &S.y;
  switch (test) {
  case 0: /* SB */
    if (t == 0) __asm__ volatile("movq $1, (%1)\n\tmovq (%2), %0" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%1)\n\tmovq (%2), %0" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case 1: /* SB+mfences */
    if (t == 0) __asm__ volatile("movq $1, (%1)\n\tmfence\n\tmovq (%2), %0" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%1)\n\tmfence\n\tmovq (%2), %0" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case 2: /* SB+xchgs: the stores are xchg (implicitly locked) */
    b = 1;
    if (t == 0) __asm__ volatile("xchgq %0, (%2)\n\tmovq (%3), %1" : "+r"(b), "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("xchgq %0, (%2)\n\tmovq (%3), %1" : "+r"(b), "=&r"(a) : "r"(y), "r"(x) : "memory");
    b = 0;
    break;
  case 3: /* MP */
    if (t == 0) __asm__ volatile("movq $1, (%0)\n\tmovq $1, (%1)" : : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case 4: /* LB */
    if (t == 0) __asm__ volatile("movq (%1), %0\n\tmovq $1, (%2)" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%1), %0\n\tmovq $1, (%2)" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case 5: /* IRIW */
    if (t == 0) __asm__ volatile("movq $1, (%0)" : : "r"(x) : "memory");
    else if (t == 1) __asm__ volatile("movq $1, (%0)" : : "r"(y) : "memory");
    else if (t == 2) __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case 6: /* 2+2W; outcome is the final memory */
    if (t == 0) __asm__ volatile("movq $1, (%0)\n\tmovq $2, (%1)" : : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%0)\n\tmovq $2, (%1)" : : "r"(y), "r"(x) : "memory");
    break;
  case 7: /* MP+movnti: the data store is non-temporal */
    if (t == 0) __asm__ volatile("movnti %2, (%0)\n\tmovq $1, (%1)" : : "r"(x), "r"(y), "r"(1ul) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case 8: /* split store vs split load across a cache line */
    if (t == 0) __asm__ volatile("movq %1, (%0)" : : "r"(SPLIT), "r"(~0ul) : "memory");
    else        __asm__ volatile("movq (%1), %0" : "=&r"(a) : "r"(SPLIT) : "memory");
    break;
  case 9: /* two unlocked inc */
    __asm__ volatile("incq (%0)" : : "r"(x) : "memory");
    break;
  case 10: /* two lock inc */
    __asm__ volatile("lock incq (%0)" : : "r"(x) : "memory");
    break;
  case 11: /* MP+movnti+sfence */
    if (t == 0) __asm__ volatile("movnti %2, (%0)\n\tsfence\n\tmovq $1, (%1)" : : "r"(x), "r"(y), "r"(1ul) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  }
  *r0 = a;
  *r1 = b;
}

static const char *names[] = {"SB", "SB+mfences", "SB+xchgs", "MP", "LB", "IRIW", "2+2W",
                              "MP+movnti", "SPLIT8", "INC2", "LOCKINC2", "MP+movnti+sfence"};
static const int nthr[] = {2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2};

/* Encode the outcome of one iteration as a small integer key. */
static unsigned outcome(int test) {
  switch (test) {
  case 0: case 1: case 2: case 4: return (unsigned)(res[0][0] * 2 + res[1][0]);
  case 3: case 7: case 11: return (unsigned)(res[1][0] * 2 + res[1][1]);
  case 5: return (unsigned)(res[2][0] * 8 + res[2][1] * 4 + res[3][0] * 2 + res[3][1]);
  case 6: return (unsigned)(S.x * 3 + S.y);
  case 8: {
    uint64_t v = res[1][0];
    return v == 0 ? 0 : v == ~0ul ? 1 : 2; /* 2: torn */
  }
  case 9: case 10: return (unsigned)S.x;
  }
  return 0;
}

static void reset(int test) {
  S.x = 0;
  S.y = 0;
  if (test == 8) *SPLIT = 0;
}

static void *worker(void *arg) {
  int t = (int)(intptr_t)arg;
  cpu_set_t cs;
  CPU_ZERO(&cs);
  /* CPUs 0, 2, 4, 6 */
  CPU_SET(t * 2 % 12, &cs);
  pthread_setaffinity_np(pthread_self(), sizeof cs, &cs);
  unsigned seed = 0x9e3779b9u * (t + 1);
  for (long it = 0; it < iters; it++) {
    if (t == 0) reset(test_id);
    barrier(2 * it);
    delay(&seed);
    body(test_id, t, &res[t][0], &res[t][1]);
    barrier(2 * it + 1);
    if (t == 0) hist[outcome(test_id)]++;
  }
  return NULL;
}

int main(int argc, char **argv) {
  iters = argc > 1 ? atol(argv[1]) : 1000000;
  hist = calloc(64, sizeof *hist);
  for (test_id = 0; test_id < (int)(sizeof names / sizeof *names); test_id++) {
    memset(hist, 0, 64 * sizeof *hist);
    nthreads = nthr[test_id];
    bar_count = 0;
    pthread_t th[MAXT];
    for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, (void *)(intptr_t)t);
    for (int t = 0; t < nthreads; t++) pthread_join(th[t], NULL);
    for (int k = 0; k < 64; k++)
      if (hist[k]) printf("%s %d %u\n", names[test_id], k, hist[k]);
    fflush(stdout);
  }
  return 0;
}

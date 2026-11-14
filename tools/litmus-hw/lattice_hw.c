/* lattice_hw: run the witness litmus tests of the memory-model lattice
   (Silmaril.X86.MemoryModel.Lattice) on the host CPU and count outcomes.

   Usage: lattice_hw ITERS CPUS [DELAY] [TEST...]
     ITERS  iterations per test
     CPUS   comma-separated logical CPUs, one per litmus thread (thread t on CPUS[t mod len])
     DELAY  maximum random pre-body delay in spin-loop iterations (default 64)
     TEST   run only these tests (default: all)

   Output: one line `test<TAB>outcome<TAB>count` per observed outcome, outcome as `k=v`
   pairs. lattice.py compares the counts with the per-model verdicts.

   Method (per iteration): thread 0 resets the locations; all threads meet at a spinning
   barrier (`lock xadd`, which also drains every store buffer), wait a per-thread pseudo-random
   delay of 0..DELAY-1 loop iterations without memory accesses, run the test body, and meet
   again; thread 0 then records the registers and the final memory. Test bodies are inline
   assembly with exactly the test's instructions.

   Build: cc -O2 -Wall -pthread lattice_hw.c -o lattice_hw */
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
} __attribute__((aligned(64))) shared_t;

static shared_t S;
/* 256 bytes, 128-aligned: offset 60 is an 8-byte slot straddling the line at 64; offset 1
   is a 2-byte slot inside the first line; offset 127 is a 2-byte slot straddling the line at
   128. */
static unsigned char lines[256] __attribute__((aligned(128)));
#define SPLIT8 ((volatile uint64_t *)(lines + 60))
#define IN2 ((volatile uint16_t *)(lines + 1))
#define X2 ((volatile uint16_t *)(lines + 127))

static volatile uint64_t bar_count;
static int nthreads, ncpus, cpus[64];
static long iters;
static unsigned delay_max = 64;
static uint64_t res[MAXT][2];

typedef struct {
  const char *name;
  int nthr;
} test_t;

enum { SB, SB_MF, SB_XCHG, MP, LB, IRIW, W22, MP_NT, MP_NT_SF, SPLIT, TORN_IN, TORN_X, INC2,
       LOCKINC2, COWR, NTESTS };
static const test_t tests[NTESTS] = {
    [SB] = {"SB", 2},           [SB_MF] = {"SB+mfences", 2}, [SB_XCHG] = {"SB+xchgs", 2},
    [MP] = {"MP", 2},           [LB] = {"LB", 2},            [IRIW] = {"IRIW", 4},
    [W22] = {"2+2W", 2},        [MP_NT] = {"MP+movnti", 2},  [MP_NT_SF] = {"MP+movnti+sfence", 2},
    [SPLIT] = {"SPLIT8", 2},    [TORN_IN] = {"TORN2-inline", 2}, [TORN_X] = {"TORN2-cross", 2},
    [INC2] = {"INC2", 2},       [LOCKINC2] = {"LOCKINC2", 2}, [COWR] = {"CoWR", 2},
};
static int test_id;

/* Outcome histogram: open addressing on 64-bit keys. */
#define HN 4096
static uint64_t hkey[HN];
static unsigned long hcnt[HN];
static void hadd(uint64_t k) {
  unsigned i = (unsigned)((k * 0x9e3779b97f4a7c15ull) >> 52) % HN;
  while (hcnt[i] && hkey[i] != k) i = (i + 1) % HN;
  hkey[i] = k;
  hcnt[i]++;
}

static inline void barrier(long it) {
  __atomic_fetch_add(&bar_count, 1, __ATOMIC_SEQ_CST);
  uint64_t target = (uint64_t)(it + 1) * nthreads;
  while (__atomic_load_n(&bar_count, __ATOMIC_ACQUIRE) < target) __builtin_ia32_pause();
}

static inline void delay(unsigned *seed) {
  *seed = *seed * 1103515245u + 12345u;
  unsigned d = (*seed >> 8) % delay_max;
  for (volatile unsigned i = 0; i < d; i++) {
  }
}

static void body(int test, int t, uint64_t *r0, uint64_t *r1) {
  uint64_t a = 0, b = 0;
  volatile uint64_t *x = &S.x, *y = &S.y;
  switch (test) {
  case SB:
    if (t == 0) __asm__ volatile("movq $1, (%1)\n\tmovq (%2), %0" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%1)\n\tmovq (%2), %0" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case SB_MF:
    if (t == 0) __asm__ volatile("movq $1, (%1)\n\tmfence\n\tmovq (%2), %0" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%1)\n\tmfence\n\tmovq (%2), %0" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case SB_XCHG:
    b = 1;
    if (t == 0) __asm__ volatile("xchgq %0, (%2)\n\tmovq (%3), %1" : "+r"(b), "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("xchgq %0, (%2)\n\tmovq (%3), %1" : "+r"(b), "=&r"(a) : "r"(y), "r"(x) : "memory");
    b = 0;
    break;
  case MP:
    if (t == 0) __asm__ volatile("movq $1, (%0)\n\tmovq $1, (%1)" : : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case LB:
    if (t == 0) __asm__ volatile("movq (%1), %0\n\tmovq $1, (%2)" : "=&r"(a) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%1), %0\n\tmovq $1, (%2)" : "=&r"(a) : "r"(y), "r"(x) : "memory");
    break;
  case IRIW:
    if (t == 0) __asm__ volatile("movq $1, (%0)" : : "r"(x) : "memory");
    else if (t == 1) __asm__ volatile("movq $1, (%0)" : : "r"(y) : "memory");
    else if (t == 2) __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case W22:
    if (t == 0) __asm__ volatile("movq $1, (%0)\n\tmovq $2, (%1)" : : "r"(x), "r"(y) : "memory");
    else        __asm__ volatile("movq $1, (%0)\n\tmovq $2, (%1)" : : "r"(y), "r"(x) : "memory");
    break;
  case MP_NT:
    if (t == 0) __asm__ volatile("movnti %2, (%0)\n\tmovq $1, (%1)" : : "r"(x), "r"(y), "r"(1ul) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case MP_NT_SF:
    if (t == 0) __asm__ volatile("movnti %2, (%0)\n\tsfence\n\tmovq $1, (%1)" : : "r"(x), "r"(y), "r"(1ul) : "memory");
    else        __asm__ volatile("movq (%2), %0\n\tmovq (%3), %1" : "=&r"(a), "=&r"(b) : "r"(y), "r"(x) : "memory");
    break;
  case SPLIT:
    if (t == 0) __asm__ volatile("movq %1, (%0)" : : "r"(SPLIT8), "r"(~0ul) : "memory");
    else        __asm__ volatile("movq (%1), %0" : "=&r"(a) : "r"(SPLIT8) : "memory");
    break;
  case TORN_IN:
    if (t == 0) __asm__ volatile("movw %1, (%0)" : : "r"(IN2), "r"((uint16_t)0x0101) : "memory");
    else        __asm__ volatile("movzwq (%1), %0" : "=&r"(a) : "r"(IN2) : "memory");
    break;
  case TORN_X:
    if (t == 0) __asm__ volatile("movw %1, (%0)" : : "r"(X2), "r"((uint16_t)0x0101) : "memory");
    else        __asm__ volatile("movzwq (%1), %0" : "=&r"(a) : "r"(X2) : "memory");
    break;
  case INC2:
    __asm__ volatile("incq (%0)" : : "r"(x) : "memory");
    break;
  case LOCKINC2:
    __asm__ volatile("lock incq (%0)" : : "r"(x) : "memory");
    break;
  case COWR: /* thread 0: x := 1; r0 := x.  thread 1: x := 2. */
    if (t == 0) __asm__ volatile("movq $1, (%1)\n\tmovq (%1), %0" : "=&r"(a) : "r"(x) : "memory");
    else        __asm__ volatile("movq $2, (%0)" : : "r"(x) : "memory");
    break;
  }
  *r0 = a;
  *r1 = b;
}

/* Outcome key: up to four small fields of 16 bits. */
#define K(a, b, c, d) (((uint64_t)(a) << 48) | ((uint64_t)(b) << 32) | ((uint64_t)(c) << 16) | (uint64_t)(d))

static uint64_t outcome(int test) {
  switch (test) {
  case SB: case SB_MF: case SB_XCHG: case LB: return K(res[0][0], res[1][0], 0, 0);
  case MP: case MP_NT: case MP_NT_SF: return K(res[1][0], res[1][1], 0, 0);
  case IRIW: return K(res[2][0], res[2][1], res[3][0], res[3][1]);
  case W22: return K(S.x, S.y, 0, 0);
  case SPLIT: { uint64_t v = res[1][0]; return K(v == 0 ? 0 : v == ~0ul ? 1 : 2, 0, 0, 0); }
  case TORN_IN: case TORN_X: { uint64_t v = res[1][0]; return K(v == 0 ? 0 : v == 0x0101 ? 1 : 2, 0, 0, 0); }
  case INC2: case LOCKINC2: return K(S.x, 0, 0, 0);
  case COWR: return K(res[0][0], S.x, 0, 0);
  }
  return 0;
}

static void print_outcome(int test, uint64_t k, unsigned long n) {
  unsigned f0 = (k >> 48) & 0xffff, f1 = (k >> 32) & 0xffff, f2 = (k >> 16) & 0xffff, f3 = k & 0xffff;
  static const char *tear[] = {"old", "new", "torn"};
  const char *nm = tests[test].name;
  switch (test) {
  case SB: case SB_MF: case SB_XCHG: case LB: printf("%s\t0:r0=%u 1:r0=%u\t%lu\n", nm, f0, f1, n); break;
  case MP: case MP_NT: case MP_NT_SF: printf("%s\t1:r0=%u 1:r1=%u\t%lu\n", nm, f0, f1, n); break;
  case IRIW: printf("%s\t2:r0=%u 2:r1=%u 3:r0=%u 3:r1=%u\t%lu\n", nm, f0, f1, f2, f3, n); break;
  case W22: printf("%s\tx=%u y=%u\t%lu\n", nm, f0, f1, n); break;
  case SPLIT: case TORN_IN: case TORN_X: printf("%s\t1:r0=%s\t%lu\n", nm, tear[f0 < 3 ? f0 : 2], n); break;
  case INC2: case LOCKINC2: printf("%s\tx=%u\t%lu\n", nm, f0, n); break;
  case COWR: printf("%s\t0:r0=%u x=%u\t%lu\n", nm, f0, f1, n); break;
  }
}

static void reset(int test) {
  S.x = 0;
  S.y = 0;
  if (test == SPLIT) *SPLIT8 = 0;
  if (test == TORN_IN) *IN2 = 0;
  if (test == TORN_X) *X2 = 0;
}

static void *worker(void *arg) {
  int t = (int)(intptr_t)arg;
  cpu_set_t cs;
  CPU_ZERO(&cs);
  CPU_SET(cpus[t % ncpus], &cs);
  if (pthread_setaffinity_np(pthread_self(), sizeof cs, &cs) != 0) {
    fprintf(stderr, "affinity to CPU %d failed\n", cpus[t % ncpus]);
    exit(2);
  }
  unsigned seed = 0x9e3779b9u * (t + 1);
  for (long it = 0; it < iters; it++) {
    if (t == 0) reset(test_id);
    barrier(2 * it);
    delay(&seed);
    body(test_id, t, &res[t][0], &res[t][1]);
    barrier(2 * it + 1);
    if (t == 0) hadd(outcome(test_id));
  }
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s ITERS CPUS [DELAY] [TEST...]\n", argv[0]);
    return 2;
  }
  iters = atol(argv[1]);
  for (char *p = strtok(argv[2], ","); p && ncpus < 64; p = strtok(NULL, ",")) cpus[ncpus++] = atoi(p);
  if (argc > 3) delay_max = (unsigned)atoi(argv[3]);
  if (delay_max == 0) delay_max = 1;
  for (test_id = 0; test_id < NTESTS; test_id++) {
    if (argc > 4) {
      int want = 0;
      for (int i = 4; i < argc; i++) want |= strcmp(argv[i], tests[test_id].name) == 0;
      if (!want) continue;
    }
    memset(hcnt, 0, sizeof hcnt);
    nthreads = tests[test_id].nthr;
    bar_count = 0;
    pthread_t th[MAXT];
    for (int t = 0; t < nthreads; t++) pthread_create(&th[t], NULL, worker, (void *)(intptr_t)t);
    for (int t = 0; t < nthreads; t++) pthread_join(th[t], NULL);
    for (int i = 0; i < HN; i++)
      if (hcnt[i]) print_outcome(test_id, hkey[i], hcnt[i]);
    fflush(stdout);
  }
  return 0;
}

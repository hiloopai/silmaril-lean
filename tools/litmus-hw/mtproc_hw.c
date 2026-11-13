/* mtproc_hw: run the raw x86-64 bytes of the multithreaded-process-model experiments
   (tools/litmus-hw/mtproc/Explore.lean) natively, many times, and count the final
   observations, for comparison with the model's exhaustive schedule exploration.

   Usage: mtproc_hw ITERS [CPU0,CPU1] [TEST...]     tests: SB MP INC2 LOCKINC2

   Each iteration maps nothing new: the code bytes sit in one RX page (copied verbatim from the
   model's programs, which are position independent), the data in one RW page. Two threads
   (pthread_create, pinned) meet at a spinning barrier, wait a random delay, load rdi, rsi,
   rdx and jump into the bytes; the bytes end with the raw exit(0) system call, which ends
   the thread (the kernel clears the thread id glibc's pthread_join waits on).

   Build: cc -O2 -Wall -pthread mtproc_hw.c -o mtproc_hw */
#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define EXIT0 0x48, 0xC7, 0xC0, 0x3C, 0x00, 0x00, 0x00, 0x48, 0x31, 0xFF, 0x0F, 0x05
static const unsigned char sb[] = {0x48, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x02, EXIT0};
static const unsigned char mpw[] = {0x48, 0xC7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x06, 0x01, 0x00, 0x00, 0x00, EXIT0};
static const unsigned char mpr[] = {0x48, 0x8B, 0x06, 0x48, 0x8B, 0x0F, 0x48, 0x89, 0x02, 0x48, 0x89, 0x4A, 0x08, EXIT0};
static const unsigned char inc[] = {0x48, 0x8B, 0x07, 0x48, 0x83, 0xC0, 0x01, 0x48, 0x89, 0x07, EXIT0};
static const unsigned char linc[] = {0xF0, 0x48, 0x83, 0x07, 0x01, EXIT0};

static unsigned char *code;
static volatile uint64_t *data; /* model address 0x3000 + 8 i is data[i] (one 64-byte line apart below) */
static volatile int arrived;
static int cpus[2] = {0, 1};

struct th { const unsigned char *bytes; size_t off; uint64_t rdi, rsi, rdx; int cpu; unsigned seed; };

static void *start(void *p) {
  struct th *a = p;
  cpu_set_t cs;
  CPU_ZERO(&cs);
  CPU_SET(a->cpu, &cs);
  pthread_setaffinity_np(pthread_self(), sizeof cs, &cs);
  __atomic_fetch_add(&arrived, 1, __ATOMIC_SEQ_CST);
  while (__atomic_load_n(&arrived, __ATOMIC_ACQUIRE) < 2) __builtin_ia32_pause();
  for (volatile unsigned i = 0, d = (a->seed >> 8) % 256; i < d; i++) {
  }
  void *entry = code + a->off;
  __asm__ volatile("mov %0, %%rdi\n\tmov %1, %%rsi\n\tmov %2, %%rdx\n\tjmp *%3"
                   : : "r"(a->rdi), "r"(a->rsi), "r"(a->rdx), "r"(entry) : "rdi", "rsi", "rdx", "memory");
  __builtin_unreachable();
}

/* data slots: x, y, r1, r2 on separate cache lines */
#define X ((uint64_t)(uintptr_t)&data[0])
#define Y ((uint64_t)(uintptr_t)&data[8])
#define R1 ((uint64_t)(uintptr_t)&data[16])
#define R2 ((uint64_t)(uintptr_t)&data[24])

int main(int argc, char **argv) {
  long iters = argc > 1 ? atol(argv[1]) : 100000;
  if (argc > 2) sscanf(argv[2], "%d,%d", &cpus[0], &cpus[1]);
  code = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  data = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  memcpy(code + 0x000, sb, sizeof sb);
  memcpy(code + 0x100, mpw, sizeof mpw);
  memcpy(code + 0x200, mpr, sizeof mpr);
  memcpy(code + 0x300, inc, sizeof inc);
  memcpy(code + 0x400, linc, sizeof linc);
  mprotect(code, 4096, PROT_READ | PROT_EXEC);
  const char *names[] = {"SB", "MP", "INC2", "LOCKINC2"};
  unsigned seed = 12345;
  for (int test = 0; test < 4; test++) {
    if (argc > 3) {
      int want = 0;
      for (int i = 3; i < argc; i++) want |= strcmp(argv[i], names[test]) == 0;
      if (!want) continue;
    }
    unsigned long hist[4][4] = {{0}};
    for (long it = 0; it < iters; it++) {
      for (int i = 0; i < 32; i++) data[i] = 0;
      arrived = 0;
      struct th a[2];
      memset(a, 0, sizeof a);
      switch (test) {
      case 0: a[0] = (struct th){sb, 0x000, X, Y, R1}; a[1] = (struct th){sb, 0x000, Y, X, R2}; break;
      case 1: a[0] = (struct th){mpw, 0x100, X, Y, 0}; a[1] = (struct th){mpr, 0x200, X, Y, R1}; break;
      case 2: a[0] = (struct th){inc, 0x300, X, 0, 0}; a[1] = (struct th){inc, 0x300, X, 0, 0}; break;
      case 3: a[0] = (struct th){linc, 0x400, X, 0, 0}; a[1] = (struct th){linc, 0x400, X, 0, 0}; break;
      }
      pthread_t t[2];
      for (int i = 0; i < 2; i++) {
        seed = seed * 1103515245u + 12345u;
        a[i].cpu = cpus[i];
        a[i].seed = seed;
        pthread_create(&t[i], NULL, start, &a[i]);
      }
      for (int i = 0; i < 2; i++) pthread_join(t[i], NULL);
      uint64_t o0, o1;
      switch (test) {
      case 0: o0 = data[16]; o1 = data[24]; break;          /* r1, r2 */
      case 1: o0 = data[16]; o1 = data[17]; break;          /* flag, data as read */
      default: o0 = data[0]; o1 = 0; break;                 /* x */
      }
      hist[o0 < 3 ? o0 : 3][o1 < 3 ? o1 : 3]++;
    }
    for (int i = 0; i < 4; i++)
      for (int j = 0; j < 4; j++)
        if (hist[i][j]) printf("%s\t%d %d\t%lu\n", names[test], i, j, hist[i][j]);
    fflush(stdout);
  }
  return 0;
}

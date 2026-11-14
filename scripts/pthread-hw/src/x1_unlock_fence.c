/* x1: is an unlock a full barrier? Store buffering (SB) with an unlock of the
   thread's own lock between the store and the load:
       T0: x = 1; unlock(L0); r0 = y        T1: y = 1; unlock(L1); r1 = x
   Each thread takes its lock before the iteration starts. The weak outcome
   r0 = r1 = 0 needs the load to pass the store. glibc 2.39 x86-64:
   pthread_spin_unlock is a plain `movl $1` (not a barrier: weak outcome
   expected), pthread_mutex_unlock in multi-threaded mode is `xchg` (a barrier:
   weak outcome forbidden by x86-TSO). Variants: none, spin, mutex, mfence.
   Usage: x1_unlock_fence ITERS. Prints one line per variant. */
#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
static volatile int x, y, r0, r1;
static pthread_spinlock_t s0, s1;
static pthread_mutex_t m0 = PTHREAD_MUTEX_INITIALIZER, m1 = PTHREAD_MUTEX_INITIALIZER;
static int variant;
static long iters;
static long counts[4][4];
static void pin(int cpu) {
  cpu_set_t c; CPU_ZERO(&c); CPU_SET(cpu, &c);
  pthread_setaffinity_np(pthread_self(), sizeof c, &c);
}
/* A sense-reversing barrier for two threads. */
static volatile int bar_count, bar_sense;
static void barrier2(int *local_sense) {
  *local_sense = !*local_sense;
  if (__atomic_add_fetch(&bar_count, 1, __ATOMIC_SEQ_CST) == 2) { bar_count = 0; bar_sense = *local_sense; }
  else while (bar_sense != *local_sense) __builtin_ia32_pause();
}
static void *thr2(void *arg) {
  long me = (long)arg;
  pin(me == 0 ? 0 : 2);
  unsigned seed = 12345 + me;
  int sense = 0;
  for (long it = 0; it < iters; it++) {
    if (variant == 1) pthread_spin_lock(me ? &s1 : &s0);
    if (variant == 2) pthread_mutex_lock(me ? &m1 : &m0);
    barrier2(&sense);
    for (int d = rand_r(&seed) & 63; d > 0; d--) __asm__ volatile("" ::: "memory");
    if (me == 0) {
      x = 1;
      if (variant == 1) pthread_spin_unlock(&s0);
      else if (variant == 2) pthread_mutex_unlock(&m0);
      else if (variant == 3) __asm__ volatile("mfence" ::: "memory");
      r0 = y;
    } else {
      y = 1;
      if (variant == 1) pthread_spin_unlock(&s1);
      else if (variant == 2) pthread_mutex_unlock(&m1);
      else if (variant == 3) __asm__ volatile("mfence" ::: "memory");
      r1 = x;
    }
    barrier2(&sense);
    if (me == 0) { counts[variant][r0 * 2 + r1]++; x = 0; y = 0; }
    barrier2(&sense);
  }
  return NULL;
}
int main(int argc, char **argv) {
  iters = argc > 1 ? atol(argv[1]) : 1000000;
  pthread_spin_init(&s0, 0);
  pthread_spin_init(&s1, 0);
  const char *names[4] = {"none", "spin_unlock", "mutex_unlock", "mfence"};
  for (variant = 0; variant < 4; variant++) {
    pthread_t a, b;
    pthread_create(&a, NULL, thr2, (void *)0);
    pthread_create(&b, NULL, thr2, (void *)1);
    pthread_join(a, NULL);
    pthread_join(b, NULL);
    printf("SB+%s: %ld runs, r0r1 {00: %ld, 01: %ld, 10: %ld, 11: %ld}\n", names[variant], iters,
           counts[variant][0], counts[variant][1], counts[variant][2], counts[variant][3]);
  }
  return 0;
}

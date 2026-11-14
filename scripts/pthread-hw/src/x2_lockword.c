/* x2: glibc 2.39's internal mutex and spin-lock representations, as the
   implementation obligations assume them (Pthread/Glibc/Defs):
   * __libc_single_threaded is 1 before the first pthread_create and 0 after
     (the single-threaded fast paths of pthread_mutex_lock/unlock use plain
     loads and stores while it is 1);
   * a NORMAL mutex's word (__data.__lock) is 0 when free, 1 when held without
     waiters, 2 when held with (possible) waiters; __owner is the holder's tid
     and is 0 when free;
   * a spin lock's word is 1 when free and <= 0 when held; failed `lock decl`s
     drive it below 0 while it is held, and an unlock stores 1.
   Prints one line of observations. */
#define _GNU_SOURCE
#include <pthread.h>
#include <stdio.h>
#include <sys/syscall.h>
#include <unistd.h>
extern char __libc_single_threaded;
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
static volatile int b_started, b_has;
static void *contender(void *arg) {
  (void)arg;
  b_started = 1;
  pthread_mutex_lock(&m);
  b_has = 1;
  pthread_mutex_unlock(&m);
  return NULL;
}
static pthread_spinlock_t s;
static volatile int spin_min = 1;
static volatile int stop;
static void *spinner(void *arg) {
  (void)arg;
  pthread_spin_lock(&s);
  pthread_spin_unlock(&s);
  return NULL;
}
static void *watcher(void *arg) {
  (void)arg;
  while (!stop) { int v = *(volatile int *)&s; if (v < spin_min) spin_min = v; }
  return NULL;
}
int main(void) {
  int st_before = __libc_single_threaded;
  int w_free = m.__data.__lock;
  pthread_mutex_lock(&m);
  int w_st = m.__data.__lock, own_st = m.__data.__owner == (int)syscall(SYS_gettid);
  pthread_mutex_unlock(&m);
  pthread_t t;
  pthread_create(&t, NULL, contender, NULL);
  pthread_join(t, NULL);
  int st_after = __libc_single_threaded;
  pthread_mutex_lock(&m);
  int w_held = m.__data.__lock, own = m.__data.__owner == (int)syscall(SYS_gettid);
  b_started = 0; b_has = 0;
  pthread_create(&t, NULL, contender, NULL);
  while (!b_started) ;
  int w_wait = 0;
  for (long i = 0; i < 100000000 && w_wait != 2; i++) w_wait = *(volatile int *)&m.__data.__lock;
  pthread_mutex_unlock(&m);
  pthread_join(t, NULL);
  int w_after = m.__data.__lock, own_after = m.__data.__owner;
  pthread_spin_init(&s, 0);
  int s_free = *(volatile int *)&s;
  pthread_spin_lock(&s);
  int s_held = *(volatile int *)&s;
  pthread_t sp[4], w;
  pthread_create(&w, NULL, watcher, NULL);
  for (int i = 0; i < 4; i++) pthread_create(&sp[i], NULL, spinner, NULL);
  for (volatile long i = 0; i < 50000000; i++) ;
  int s_contended = *(volatile int *)&s;
  pthread_spin_unlock(&s);
  for (int i = 0; i < 4; i++) pthread_join(sp[i], NULL);
  stop = 1;
  pthread_join(w, NULL);
  int s_end = *(volatile int *)&s;
  printf("single_threaded %d->%d mutex free %d held(st) %d owner(st) %d held %d owner %d waiters %d after %d owner_after %d "
         "spin free %d held %d contended %d min %d end %d\n",
         st_before, st_after, w_free, w_st, own_st, w_held, own, w_wait, w_after, own_after,
         s_free, s_held, s_contended, spin_min, s_end);
  return 0;
}

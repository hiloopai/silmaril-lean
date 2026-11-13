/* p2: a producer sends 1..N through a one-slot buffer guarded by a mutex and
   two condition variables; the consumer sums what it receives. Waits are in
   while loops, so spurious wake-ups are harmless. Prints the sum: N(N+1)/2. */
#include <pthread.h>
#include <stdio.h>
#ifndef N
#define N 20000
#endif
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t not_full = PTHREAD_COND_INITIALIZER;
static pthread_cond_t not_empty = PTHREAD_COND_INITIALIZER;
static int full;
static long slot;
static void *producer(void *arg) {
  (void)arg;
  for (long i = 1; i <= N; i++) {
    pthread_mutex_lock(&m);
    while (full) pthread_cond_wait(&not_full, &m);
    slot = i;
    full = 1;
    pthread_cond_signal(&not_empty);
    pthread_mutex_unlock(&m);
  }
  return NULL;
}
static void *consumer(void *arg) {
  long *sum = arg;
  for (long i = 1; i <= N; i++) {
    pthread_mutex_lock(&m);
    while (!full) pthread_cond_wait(&not_empty, &m);
    *sum += slot;
    full = 0;
    pthread_cond_signal(&not_full);
    pthread_mutex_unlock(&m);
  }
  return NULL;
}
int main(void) {
  pthread_t p, c;
  long sum = 0;
  pthread_create(&c, NULL, consumer, &sum);
  pthread_create(&p, NULL, producer, NULL);
  pthread_join(p, NULL);
  pthread_join(c, NULL);
  printf("%ld\n", sum);
  return 0;
}

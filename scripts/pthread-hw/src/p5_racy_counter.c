/* p5 (negative example): two threads add 1 to a volatile counter N times each
   WITHOUT a lock. Each increment is a separate load, add and store, so updates
   can be lost: the program has a data race and its output is not determined.
   Any value in [2, 2N] is a possible outcome. */
#include <pthread.h>
#include <stdio.h>
#ifndef N
#define N 100000
#endif
static volatile long counter;
static void *worker(void *arg) {
  (void)arg;
  for (int i = 0; i < N; i++) counter = counter + 1;
  return NULL;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&a, NULL, worker, NULL);
  pthread_create(&b, NULL, worker, NULL);
  pthread_join(a, NULL);
  pthread_join(b, NULL);
  printf("%ld\n", counter);
  return 0;
}

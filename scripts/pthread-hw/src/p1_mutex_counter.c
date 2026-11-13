/* p1: two threads add 1 to a shared counter N times each, under a default
   (PTHREAD_MUTEX_NORMAL) mutex. Prints the final counter: always 2N. */
#include <pthread.h>
#include <stdio.h>
#define N 100000
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
static long counter;
static void *worker(void *arg) {
  (void)arg;
  for (int i = 0; i < N; i++) {
    pthread_mutex_lock(&m);
    counter = counter + 1;
    pthread_mutex_unlock(&m);
  }
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

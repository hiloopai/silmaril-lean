/* p6: p1 with a pthread spin lock (glibc: lock decl / cmp spin / plain-store
   unlock). Prints 2N. */
#include <pthread.h>
#include <stdio.h>
#ifndef N
#define N 100000
#endif
static pthread_spinlock_t s;
static long counter;
static void *worker(void *arg) {
  (void)arg;
  for (int i = 0; i < N; i++) {
    pthread_spin_lock(&s);
    counter = counter + 1;
    pthread_spin_unlock(&s);
  }
  return NULL;
}
int main(void) {
  pthread_t a, b;
  pthread_spin_init(&s, PTHREAD_PROCESS_PRIVATE);
  pthread_create(&a, NULL, worker, NULL);
  pthread_create(&b, NULL, worker, NULL);
  pthread_join(a, NULL);
  pthread_join(b, NULL);
  printf("%ld\n", counter);
  return 0;
}

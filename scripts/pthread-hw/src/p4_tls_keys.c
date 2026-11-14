/* p4: thread-specific data. Each of four threads stores its index + 1 under one
   key and reads it back; the key's destructor runs at each thread exit for the
   non-null value. Prints the number of threads that read back their own value,
   the number of destructor runs and the main thread's value (NULL): "4 4 0". */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#define T 4
#ifndef K
#define K 1000
#endif
static pthread_key_t key;
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
static int dtors;
static int own[T];
static void dtor(void *v) {
  (void)v;
  pthread_mutex_lock(&m);
  dtors = dtors + 1;
  pthread_mutex_unlock(&m);
}
static void *worker(void *arg) {
  intptr_t i = (intptr_t)arg;
  pthread_setspecific(key, (void *)(i + 1));
  for (int k = 0; k < K; k++) {
    if ((intptr_t)pthread_getspecific(key) != i + 1) return NULL;
  }
  own[i] = 1;
  return NULL;
}
int main(void) {
  pthread_key_create(&key, dtor);
  pthread_t th[T];
  for (intptr_t i = 0; i < T; i++) pthread_create(&th[i], NULL, worker, (void *)i);
  int ok = 0;
  for (int i = 0; i < T; i++) { pthread_join(th[i], NULL); ok += own[i]; }
  printf("%d %d %ld\n", ok, dtors, (long)(intptr_t)pthread_getspecific(key));
  return 0;
}

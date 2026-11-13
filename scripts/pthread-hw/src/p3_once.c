/* p3: four threads call pthread_once on one control; the init routine runs
   exactly once and every thread sees its effect after pthread_once returns.
   Prints the number of init runs and the number of threads that saw 42: "1 4". */
#include <pthread.h>
#include <stdio.h>
#define T 4
static pthread_once_t once = PTHREAD_ONCE_INIT;
static int inits;
static int value;
static int seen[T];
static void init(void) { inits = inits + 1; value = 42; }
static void *worker(void *arg) {
  long i = (long)arg;
  pthread_once(&once, init);
  seen[i] = (value == 42);
  return NULL;
}
int main(void) {
  pthread_t th[T];
  for (long i = 0; i < T; i++) pthread_create(&th[i], NULL, worker, (void *)i);
  int ok = 0;
  for (int i = 0; i < T; i++) { pthread_join(th[i], NULL); ok += seen[i]; }
  printf("%d %d\n", inits, ok);
  return 0;
}

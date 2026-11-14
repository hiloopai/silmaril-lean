/* p7: semaphores and a barrier. Two threads alternate strictly through two
   semaphores (ping-pong), appending to a log; then four threads each write a
   slot, meet at a barrier and read every slot. Prints the log and the number of
   threads that saw all slots written plus the number of serial threads:
   "abababababababababab 4 1". */
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#ifndef R
#define R 10
#endif
#define T 4
static sem_t ping, pong;
static char logbuf[2 * R + 1];
static int pos;
static void *pinger(void *arg) {
  (void)arg;
  for (int i = 0; i < R; i++) { sem_wait(&ping); logbuf[pos++] = 'a'; sem_post(&pong); }
  return NULL;
}
static void *ponger(void *arg) {
  (void)arg;
  for (int i = 0; i < R; i++) { sem_wait(&pong); logbuf[pos++] = 'b'; sem_post(&ping); }
  return NULL;
}
static pthread_barrier_t bar;
static int slots[T];
static int all[T];
static int serial[T];
static void *phase(void *arg) {
  long i = (long)arg;
  slots[i] = 1;
  int r = pthread_barrier_wait(&bar);
  serial[i] = (r == PTHREAD_BARRIER_SERIAL_THREAD);
  int s = 0;
  for (int j = 0; j < T; j++) s += slots[j];
  all[i] = (s == T);
  return NULL;
}
int main(void) {
  sem_init(&ping, 0, 1);
  sem_init(&pong, 0, 0);
  pthread_t a, b;
  pthread_create(&a, NULL, pinger, NULL);
  pthread_create(&b, NULL, ponger, NULL);
  pthread_join(a, NULL);
  pthread_join(b, NULL);
  pthread_barrier_init(&bar, NULL, T);
  pthread_t th[T];
  for (long i = 0; i < T; i++) pthread_create(&th[i], NULL, phase, (void *)i);
  int ok = 0, ser = 0;
  for (int i = 0; i < T; i++) { pthread_join(th[i], NULL); ok += all[i]; ser += serial[i]; }
  printf("%s %d %d\n", logbuf, ok, ser);
  return 0;
}

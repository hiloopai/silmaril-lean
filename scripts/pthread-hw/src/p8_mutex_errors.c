/* p8: POSIX error returns of the mutex kinds, spin trylock, sem_trywait and
   rwlock, as the specification states them. Prints one line of codes:
   errorcheck relock EDEADLK(35), errorcheck unlock by a non-owner EPERM(1),
   recursive relock 0 and unlock depth, trylock of a held normal mutex
   EBUSY(16), spin trylock of a held spin lock EBUSY(16), sem_trywait at 0
   (-1, errno EAGAIN 11), rwlock: rdlock twice 0 0, wrtrylock while read-held
   EBUSY(16), wrlock by the same thread after unlocking 0, rdlock while
   write-held by self EDEADLK(35), joining oneself EDEADLK(35). */
#include <errno.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
static pthread_mutex_t ec, rc, nm = PTHREAD_MUTEX_INITIALIZER;
static int r_unlock_other;
static void *other(void *arg) { (void)arg; r_unlock_other = pthread_mutex_unlock(&ec); return NULL; }
static int r_try;
static void *tryer(void *arg) { (void)arg; r_try = pthread_mutex_trylock(&nm); return NULL; }
int main(void) {
  pthread_mutexattr_t a;
  pthread_mutexattr_init(&a);
  pthread_mutexattr_settype(&a, PTHREAD_MUTEX_ERRORCHECK);
  pthread_mutex_init(&ec, &a);
  pthread_mutexattr_settype(&a, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&rc, &a);
  int e1 = pthread_mutex_lock(&ec);
  int e2 = pthread_mutex_lock(&ec);
  pthread_t t;
  pthread_create(&t, NULL, other, NULL);
  pthread_join(t, NULL);
  int e3 = pthread_mutex_unlock(&ec);
  int r1 = pthread_mutex_lock(&rc), r2 = pthread_mutex_lock(&rc), r3 = pthread_mutex_unlock(&rc),
      r4 = pthread_mutex_unlock(&rc), r5 = pthread_mutex_unlock(&rc);
  pthread_mutex_lock(&nm);
  pthread_create(&t, NULL, tryer, NULL);
  pthread_join(t, NULL);
  pthread_mutex_unlock(&nm);
  pthread_spinlock_t s;
  pthread_spin_init(&s, 0);
  int s1 = pthread_spin_trylock(&s), s2 = pthread_spin_trylock(&s);
  pthread_spin_unlock(&s);
  sem_t sem;
  sem_init(&sem, 0, 0);
  errno = 0;
  int w1 = sem_trywait(&sem);
  int w1e = errno;
  pthread_rwlock_t rw = PTHREAD_RWLOCK_INITIALIZER;
  int q1 = pthread_rwlock_rdlock(&rw), q2 = pthread_rwlock_rdlock(&rw), q3 = pthread_rwlock_trywrlock(&rw);
  pthread_rwlock_unlock(&rw);
  pthread_rwlock_unlock(&rw);
  int q4 = pthread_rwlock_wrlock(&rw), q5 = pthread_rwlock_rdlock(&rw);
  pthread_rwlock_unlock(&rw);
  int j = pthread_join(pthread_self(), NULL);
  printf("ec %d %d %d %d rec %d %d %d %d %d try %d spin %d %d sem %d %d rw %d %d %d %d %d join %d\n",
         e1, e2, r_unlock_other, e3, r1, r2, r3, r4, r5, r_try, s1, s2, w1, w1e, q1, q2, q3, q4, q5, j);
  return 0;
}

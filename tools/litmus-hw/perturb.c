/* perturb.so: an LD_PRELOAD shim that perturbs the schedule of a pthread program without
   changing its bytes. Before and after each interposed pthread/semaphore call, and at the
   start of every thread, it yields (sched_yield) or spins for a random number of loop
   iterations, with the probability given by the environment:

     PERTURB_P     per-mille probability of a perturbation at each point (default 200)
     PERTURB_SPIN  maximum spin length in loop iterations (default 2000)
     PERTURB_SEED  seed (default: from the clock and the pid)
     PERTURB_MIGRATE  per-mille probability of moving the thread to a random allowed CPU
                   (sched_setaffinity within the process's initial mask; default 0)

   Every interposed function calls the real one (dlsym(RTLD_NEXT)) with the same arguments
   and returns its result, so the program's semantics is unchanged; only timing changes.

   Build: cc -O2 -Wall -shared -fPIC perturb.c -o perturb.so -ldl */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <pthread.h>
#include <sched.h>
#include <semaphore.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static unsigned P = 200, SPIN = 2000, MIGRATE = 0;
static uint64_t seed0;
static cpu_set_t mask0;
static int ncpu0;
static __thread uint64_t rng;

__attribute__((constructor)) static void init(void) {
  const char *e;
  if ((e = getenv("PERTURB_P"))) P = (unsigned)atoi(e);
  if ((e = getenv("PERTURB_SPIN"))) SPIN = (unsigned)atoi(e);
  if ((e = getenv("PERTURB_MIGRATE"))) MIGRATE = (unsigned)atoi(e);
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  seed0 = (e = getenv("PERTURB_SEED")) ? strtoull(e, NULL, 0)
                                       : (uint64_t)ts.tv_nsec ^ ((uint64_t)getpid() << 32);
  sched_getaffinity(0, sizeof mask0, &mask0);
  ncpu0 = CPU_COUNT(&mask0);
}

static uint64_t next(void) {
  if (rng == 0) rng = seed0 ^ (0x9e3779b97f4a7c15ull * (uint64_t)(uintptr_t)&rng) ^ 1;
  rng ^= rng << 13;
  rng ^= rng >> 7;
  rng ^= rng << 17;
  return rng;
}

static void perturb(void) {
  uint64_t r = next();
  if (MIGRATE && ncpu0 > 1 && (r >> 40) % 1000 < MIGRATE) {
    int k = (int)((r >> 20) % (uint64_t)ncpu0), c = 0;
    for (int i = 0; i < CPU_SETSIZE; i++)
      if (CPU_ISSET(i, &mask0) && c++ == k) {
        cpu_set_t one;
        CPU_ZERO(&one);
        CPU_SET(i, &one);
        sched_setaffinity(0, sizeof one, &one);
        break;
      }
  }
  if (r % 1000 >= P) return;
  if ((r >> 10) & 1) {
    sched_yield();
  } else {
    unsigned n = (unsigned)((r >> 11) % (SPIN + 1));
    for (volatile unsigned i = 0; i < n; i++) {
    }
  }
}

#define REAL(name) \
  static __typeof__(name) *real_##name; \
  if (!real_##name) real_##name = (__typeof__(name) *)dlsym(RTLD_NEXT, #name)

/* thread start: perturb before the start routine */
struct start { void *(*f)(void *); void *a; };
static void *trampoline(void *p) {
  struct start s = *(struct start *)p;
  free(p);
  perturb();
  perturb();
  return s.f(s.a);
}
int pthread_create(pthread_t *t, const pthread_attr_t *at, void *(*f)(void *), void *a) {
  REAL(pthread_create);
  struct start *s = malloc(sizeof *s);
  s->f = f;
  s->a = a;
  perturb();
  int r = real_pthread_create(t, at, trampoline, s);
  perturb();
  return r;
}

/* The condition-variable functions have two symbol versions in glibc; plain dlsym would return
   the GLIBC_2.2.5 compatibility version, which uses another pthread_cond_t layout. */
#define REALV(name, ver) \
  static __typeof__(name) *real_##name; \
  if (!real_##name) real_##name = (__typeof__(name) *)dlvsym(RTLD_NEXT, #name, ver)
#define WRAPV1(ret, name, T1) \
  ret name(T1 x) { REALV(name, "GLIBC_2.3.2"); perturb(); ret r = real_##name(x); perturb(); return r; }
#define WRAPV2(ret, name, T1, T2) \
  ret name(T1 x, T2 y) { REALV(name, "GLIBC_2.3.2"); perturb(); ret r = real_##name(x, y); perturb(); return r; }

#define WRAP1(ret, name, T1) \
  ret name(T1 x) { REAL(name); perturb(); ret r = real_##name(x); perturb(); return r; }
#define WRAP2(ret, name, T1, T2) \
  ret name(T1 x, T2 y) { REAL(name); perturb(); ret r = real_##name(x, y); perturb(); return r; }

WRAP2(int, pthread_join, pthread_t, void **)
WRAP1(int, pthread_mutex_lock, pthread_mutex_t *)
WRAP1(int, pthread_mutex_trylock, pthread_mutex_t *)
WRAP1(int, pthread_mutex_unlock, pthread_mutex_t *)
WRAPV2(int, pthread_cond_wait, pthread_cond_t *, pthread_mutex_t *)
WRAPV1(int, pthread_cond_signal, pthread_cond_t *)
WRAPV1(int, pthread_cond_broadcast, pthread_cond_t *)
WRAP1(int, pthread_spin_lock, pthread_spinlock_t *)
WRAP1(int, pthread_spin_trylock, pthread_spinlock_t *)
WRAP1(int, pthread_spin_unlock, pthread_spinlock_t *)
WRAP1(int, pthread_barrier_wait, pthread_barrier_t *)
typedef void (*init_fn)(void);
WRAP2(int, pthread_once, pthread_once_t *, init_fn)
WRAP2(int, pthread_setspecific, pthread_key_t, const void *)
WRAP1(void *, pthread_getspecific, pthread_key_t)
WRAP1(int, sem_wait, sem_t *)
WRAP1(int, sem_trywait, sem_t *)
WRAP1(int, sem_post, sem_t *)
WRAP1(int, pthread_rwlock_rdlock, pthread_rwlock_t *)
WRAP1(int, pthread_rwlock_wrlock, pthread_rwlock_t *)
WRAP1(int, pthread_rwlock_trywrlock, pthread_rwlock_t *)
WRAP1(int, pthread_rwlock_unlock, pthread_rwlock_t *)

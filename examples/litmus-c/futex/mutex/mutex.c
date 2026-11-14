/* Drepper's futex mutex ("Futexes Are Tricky", mutex 2): 0 unlocked, 1 locked, 2 locked with
 * possible waiters. Two threads each increment a plain counter under the mutex, then record that they finished
 * (the different records also keep the compiler from folding P1 into P0). */
#include "../futex.h"
#define M 0x10000
#define C 0x10040
#define D0 0x10080
#define D1 0x100c0

static inline void lock(void) {
  int c = 0;
  if (!__atomic_compare_exchange_n(ALOC(M), &c, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_ACQUIRE)) {
    if (c != 2)
      c = __atomic_exchange_n(ALOC(M), 2, __ATOMIC_ACQUIRE);
    while (c != 0) {
      FUTEX_WAIT(M, 2);
      c = __atomic_exchange_n(ALOC(M), 2, __ATOMIC_ACQUIRE);
    }
  }
}
static inline void unlock(void) {
  if (__atomic_fetch_sub(ALOC(M), 1, __ATOMIC_RELEASE) != 1) {
    __atomic_store_n(ALOC(M), 0, __ATOMIC_RELEASE);
    FUTEX_WAKE(M, 1);
  }
}

void P0(void) {
  lock();
  LOC(C) = LOC(C) + 1;
  unlock();
  LOC(D0) = 1;
}
void P1(void) {
  lock();
  LOC(C) = LOC(C) + 1;
  unlock();
  LOC(D1) = 1;
}

/* The event flag with a lost wake-up (bug): P0 wakes before it sets the flag, so P1 can check
 * the flag, find it clear, and sleep after the only wake. */
#include "../futex.h"
#define DATA 0x10000
#define FLAG 0x10040
#define R0 0x10080
#define DONE 0x100c0

void P0(void) {
  LOC(DATA) = 1;
  FUTEX_WAKE(FLAG, 1);
  __atomic_store_n(ALOC(FLAG), 1, __ATOMIC_RELEASE);
}
void P1(void) {
  while (__atomic_load_n(ALOC(FLAG), __ATOMIC_ACQUIRE) == 0)
    FUTEX_WAIT(FLAG, 0);
  LOC(R0) = LOC(DATA);
  LOC(DONE) = 1;
}

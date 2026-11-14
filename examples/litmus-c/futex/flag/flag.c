/* A one-shot event flag. P0 publishes data, sets the flag and wakes; P1 sleeps on the flag
 * until it is set, then reads the data and records that it finished. */
#include "../futex.h"
#define DATA 0x10000
#define FLAG 0x10040
#define R0 0x10080
#define DONE 0x100c0

void P0(void) {
  LOC(DATA) = 1;
  __atomic_store_n(ALOC(FLAG), 1, __ATOMIC_RELEASE);
  FUTEX_WAKE(FLAG, 1);
}
void P1(void) {
  while (__atomic_load_n(ALOC(FLAG), __ATOMIC_ACQUIRE) == 0)
    FUTEX_WAIT(FLAG, 0);
  LOC(R0) = LOC(DATA);
  LOC(DONE) = 1;
}

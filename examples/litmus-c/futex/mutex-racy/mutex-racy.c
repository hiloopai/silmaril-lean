/* A broken futex mutex (bug): lock tests the word and then sets it with a plain store, so both
 * threads can see it free and enter together. */
#include "../futex.h"
#define M 0x10000
#define C 0x10040
#define D0 0x10080
#define D1 0x100c0

static inline void lock(void) {
  int c;
  while ((c = LOC(M)) != 0)
    FUTEX_WAIT(M, c);
  LOC(M) = 1;
}
static inline void unlock(void) {
  LOC(M) = 0;
  FUTEX_WAKE(M, 1);
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

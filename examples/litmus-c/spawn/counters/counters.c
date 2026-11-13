/* Two children increment separate counters (P1 non-atomically, P2 with a relaxed fetch_add);
 * after joining both, the parent reads them. */
#include "../spawn.h"
#define C1 0x10000
#define C2 0x10040
#define R0 0x10080
#define R1 0x100c0

void P0(void) {
  SPAWN(1);
  SPAWN(2);
  JOIN(1);
  JOIN(2);
  LOC(R0) = LOC(C1);
  LOC(R1) = LOC(C2);
}
void P1(void) { LOC(C1) += 1; }
void P2(void) { __atomic_fetch_add(&LOC(C2), 1, __ATOMIC_RELAXED); }

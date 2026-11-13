/* Control for MP+spawn: the spawn comes before the data store, so the child may miss it. */
#include "../spawn.h"
#define X 0x10000
#define R0 0x10080

void P0(void) { SPAWN(1); LOC(X) = 1; }
void P1(void) { LOC(R0) = LOC(X); }

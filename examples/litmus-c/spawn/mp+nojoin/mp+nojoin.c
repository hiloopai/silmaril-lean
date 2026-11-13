/* Control for MP+join: the parent reads without joining, so it may miss the child's store. */
#include "../spawn.h"
#define X 0x10000
#define R0 0x10080

void P0(void) { SPAWN(1); LOC(R0) = LOC(X); }
void P1(void) { LOC(X) = 1; }

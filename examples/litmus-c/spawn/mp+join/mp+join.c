/* MP via join: data written by the child is seen by the parent after the join. */
#include "../spawn.h"
#define X 0x10000
#define R0 0x10080

void P0(void) { SPAWN(1); JOIN(1); LOC(R0) = LOC(X); }
void P1(void) { LOC(X) = 1; }

/* MP via spawn: data written before the spawn is seen by the child. */
#include "../spawn.h"
#define X 0x10000
#define R0 0x10080

void P0(void) { LOC(X) = 1; SPAWN(1); }
void P1(void) { LOC(R0) = LOC(X); }

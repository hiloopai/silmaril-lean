/* 2+2W (two writes per thread, final state). exists x=1 /\ y=1 */
#include "../c11.h"
int x, y;
void P0(void) { ST(&x, 1); ST(&y, 2); }
void P1(void) { ST(&y, 1); ST(&x, 2); }

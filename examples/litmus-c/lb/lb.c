/* LB (load buffering). exists r0=1 /\ r1=1 */
#include "../c11.h"
int x, y, r0, r1;
void P0(void) { r0 = LD(&x); ST(&y, 1); }
void P1(void) { r1 = LD(&y); ST(&x, 1); }

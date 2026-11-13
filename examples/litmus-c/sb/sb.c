/* SB (store buffering). exists r0=0 /\ r1=0 */
#include "../c11.h"
int x, y, r0, r1;
void P0(void) { ST(&x, 1); r0 = LD(&y); }
void P1(void) { ST(&y, 1); r1 = LD(&x); }

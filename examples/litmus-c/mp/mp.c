/* MP (message passing). exists r0=1 /\ r1=0 */
#include "../c11.h"
int x, y, r0, r1;
void P0(void) { ST(&x, 1); ST(&y, 1); }
void P1(void) { r0 = LD(&y); r1 = LD(&x); }

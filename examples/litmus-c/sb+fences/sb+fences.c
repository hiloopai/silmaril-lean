/* SB with a seq_cst fence between the store and the load. exists r0=0 /\ r1=0 */
#include "../c11.h"
int x, y, r0, r1;
void P0(void) { ST(&x, 1); F_SC(); r0 = LD(&y); }
void P1(void) { ST(&y, 1); F_SC(); r1 = LD(&x); }

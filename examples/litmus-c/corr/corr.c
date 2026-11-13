/* CoRR (coherence of two reads of one location). exists r0=1 /\ r1=0 */
#include "../c11.h"
int x, r0, r1;
void P0(void) { ST(&x, 1); }
void P1(void) { r0 = LD(&x); r1 = LD(&x); }

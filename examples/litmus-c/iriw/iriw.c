/* IRIW (independent reads of independent writes).
   exists r0=1 /\ r1=0 /\ r2=1 /\ r3=0 */
#include "../c11.h"
int x, y, r0, r1, r2, r3;
void P0(void) { ST(&x, 1); }
void P1(void) { ST(&y, 1); }
void P2(void) { r0 = LD(&x); r1 = LD(&y); }
void P3(void) { r2 = LD(&y); r3 = LD(&x); }

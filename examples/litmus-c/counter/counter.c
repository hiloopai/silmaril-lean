/* RMW counter: two increments of one counter, one discarding and one keeping the old
   value. exists x=1 (a lost update). */
#include "../c11.h"
int x, r1;
void P0(void) { (void)FADD(&x, 1); }
void P1(void) { r1 = FADD(&x, 1); }

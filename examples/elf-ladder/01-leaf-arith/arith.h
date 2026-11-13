#ifndef ARITH_H
#define ARITH_H
#include "rt.h"
/* Leaf functions: no calls, no memory except the stack, System V AMD64 ABI.
   Each has a total functional contract over BitVec 32 / Int32. */
u32 popcount32(u32 x);                 /* = number of set bits */
u32 gcd_u32(u32 a, u32 b);             /* = Nat.gcd a b */
int clamp_i32(int x, int lo, int hi);  /* lo <= hi -> = max lo (min x hi) */
u32 isqrt_u32(u32 x);                  /* = floor (sqrt x) */
u32 sat_add_u32(u32 a, u32 b);         /* = min (a + b) 0xffffffff */
u32 bswap32_manual(u32 x);             /* = byte reversal */
int ilog2_u32(u32 x);                  /* x != 0 -> = Nat.log2 x; x = 0 -> -1 */
#endif

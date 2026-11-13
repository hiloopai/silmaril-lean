/* Rung 01 subject: leaf arithmetic.  Straight-line (popcount, clamp, sat_add,
   bswap) and single-loop (gcd, isqrt, ilog2) leaves. */
#include "arith.h"

u32 popcount32(u32 x) {                 /* SWAR; straight line -> bv_decide */
  x = x - ((x >> 1) & 0x55555555u);
  x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
  x = (x + (x >> 4)) & 0x0f0f0f0fu;
  return (x * 0x01010101u) >> 24;
}

u32 gcd_u32(u32 a, u32 b) {             /* Euclid; loop with `div` */
  while (b != 0) { u32 t = a % b; a = b; b = t; }
  return a;
}

int clamp_i32(int x, int lo, int hi) {  /* signed compares; cmov-free under flags */
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}

u32 isqrt_u32(u32 x) {                  /* digit-by-digit; fixed 16 iterations */
  u32 res = 0, bit = 1u << 30;
  while (bit > x) bit >>= 2;
  while (bit != 0) {
    if (x >= res + bit) { x -= res + bit; res = (res >> 1) + bit; }
    else res >>= 1;
    bit >>= 2;
  }
  return res;
}

u32 sat_add_u32(u32 a, u32 b) {
  u32 s = a + b;
  return s < a ? 0xffffffffu : s;
}

u32 bswap32_manual(u32 x) {             /* GCC recognises this as `bswap` */
  return (x >> 24) | ((x >> 8) & 0xff00u) | ((x << 8) & 0xff0000u) | (x << 24);
}

int ilog2_u32(u32 x) {
  int r = -1;
  while (x) { x >>= 1; r++; }
  return r;
}

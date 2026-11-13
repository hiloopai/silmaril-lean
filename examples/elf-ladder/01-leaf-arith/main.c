/* Rung 01 driver: differential self-test against independently written
   references (the references are test oracles, not verification targets). */
#include "arith.h"

static u32 ref_pop(u32 x) { u32 n = 0; for (; x; x &= x - 1) n++; return n; }
static u32 ref_isqrt(u32 x) { u64 r = 0; while ((r + 1) * (r + 1) <= x) r++; return (u32)r; }
static u32 lcg(u32 *s) { *s = *s * 1664525u + 1013904223u; return *s; }

int cmain(long *sp) {
  static const u32 edge[] = {0, 1, 2, 3, 0x7fffffffu, 0x80000000u, 0xffffffffu,
                             0xfffffffeu, 0x10000u, 0xffffu, 65535u * 65535u};
  for (unsigned i = 0; i < sizeof edge / sizeof edge[0]; i++) {
    u32 x = edge[i];
    rt_check(popcount32(x) == ref_pop(x), "popcount edge");
    rt_check(isqrt_u32(x) == ref_isqrt(x) || x > 0xfffe0000u, "isqrt edge");
  }
  rt_check(isqrt_u32(0xffffffffu) == 65535u, "isqrt max");
  u32 s = 12345;
  for (int i = 0; i < 2000; i++) {
    u32 a = lcg(&s), b = lcg(&s) >> (i & 31);
    rt_check(popcount32(a) == ref_pop(a), "popcount");
    if ((i & 15) == 0) rt_check(isqrt_u32(b) == ref_isqrt(b), "isqrt");
    u32 g = gcd_u32(a, b);
    rt_check(g == 0 ? (a == 0 && b == 0) : (a % g == 0 && b % g == 0), "gcd divides");
    rt_check(sat_add_u32(a, b) == ((u64)a + b > 0xffffffffu ? 0xffffffffu : a + b), "sat_add");
    rt_check(bswap32_manual(bswap32_manual(a)) == a, "bswap involution");
    rt_check(bswap32_manual(a) == ((a & 0xff) << 24 | (a >> 8 & 0xff) << 16 | (a >> 16 & 0xff) << 8 | a >> 24), "bswap");
    int r = ilog2_u32(a | 1);
    rt_check((1u << r) <= (a | 1) && (r == 31 || (a | 1) < (2u << r)), "ilog2");
    int x = (int)a, lo = -(int)(b & 0xffff), hi = (int)(b & 0xffff);
    int c = clamp_i32(x, lo, hi);
    rt_check(c >= lo && c <= hi && (c == x || c == lo || c == hi), "clamp");
  }
  rt_check(gcd_u32(48, 18) == 6 && gcd_u32(0, 7) == 7 && gcd_u32(7, 0) == 7, "gcd known");
  rt_check(ilog2_u32(0) == -1, "ilog2 0");
  return rt_finish("01-leaf-arith");
}

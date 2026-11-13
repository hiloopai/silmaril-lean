/* The C library of programs compiled by ccomp (docs/CCompiler.md), compiled by ccomp
   itself and linked as a library (weak definitions: a program's own definition of a
   name wins). It makes no system calls: output goes to the buffer of the runtime
   control block (Silmaril.Compile.Target.Runtime) and the startup code writes it out
   at exit; exit() and abort() record their status there and trap.

   Control block (8-byte words at linear address 0x1000):
   0 software stack pointer, 1 heap break, 2 heap limit, 3 output length, 4 exit
   status, 5 exit kind (1 exit, 2 abort), 6 output buffer, 7 its capacity. */

#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CTL ((unsigned long *)0x1000)

/* The Lir `trap` terminator (an intrinsic of the compiler). */
void __ccomp_trap(void);

FILE *const __stdout = (FILE *)1;
FILE *const __stderr = (FILE *)2;

/* ---- process ---- */

_Noreturn void exit(int status) {
  unsigned long *ctl = CTL;
  ctl[4] = (unsigned long)(status & 255);
  ctl[5] = 1;
  __ccomp_trap();
  for (;;) {}
}

_Noreturn void _Exit(int status) { exit(status); }

_Noreturn void abort(void) {
  unsigned long *ctl = CTL;
  ctl[5] = 2;
  __ccomp_trap();
  for (;;) {}
}

void __builtin_unreachable(void) { abort(); }

int atexit(void (*func)(void)) { (void)func; return 0; }

/* ---- soft-float ---- */

/* IEEE 754 binary64 and binary32 arithmetic on encodings, for compiled code
   (docs/CCompiler.md): the compiler keeps a double as its 64 bits and a float as its
   32 bits zero-extended, and lowers every floating operation to one of these
   routines. Results are those of x86-64 SSE under the default MXCSR: round to nearest
   even, subnormals kept, a NaN operand propagated quieted (the first one), the default
   NaN 0xFFF8... for invalid operations, and the truncating conversions' "integer
   indefinite" value out of range. Single-precision +, -, *, / round the exact
   binary64 result once more, which is correctly rounded (53 >= 2 * 24 + 2). */

typedef unsigned long u64;

#define D_SIGN 0x8000000000000000UL
#define D_EXP 0x7FF0000000000000UL
#define D_QUIET 0x0008000000000000UL
#define D_DEFAULT_NAN 0xFFF8000000000000UL
#define D_TWO63 0x43E0000000000000UL

static int d_isnan(u64 a) { return (a & ~D_SIGN) > D_EXP; }
static int d_isinf(u64 a) { return (a & ~D_SIGN) == D_EXP; }
static int d_iszero(u64 a) { return (a & ~D_SIGN) == 0; }

/* The encoding of (-1)^neg * m * 2^e, m != 0, rounded to nearest even in the format
   of p significand bits and ebits exponent bits. Either m is exact, or it has at
   least p + 2 significant bits and its last bit is set ("jammed"): the value lies
   strictly between m - 1 and m + 1. */
static u64 fp_pack(int neg, long e, u64 m, int p, int ebits) {
  long bias = (1L << (ebits - 1)) - 1;
  long top = (1L << ebits) - 1;
  u64 sign = neg ? 1UL << (p - 1 + ebits) : 0;
  for (int k = 32; k > 0; k >>= 1)
    if ((m >> (64 - k)) == 0) { m <<= k; e -= k; }
  long be = e + 63 + bias;
  if (be >= top) return sign | ((u64)top << (p - 1));
  long shift = 64 - p;
  if (be < 1) { shift += 1 - be; be = 1; }
  u64 q;
  if (shift >= 64) {
    q = (shift == 64 && m > D_SIGN) ? 1 : 0;
  } else {
    q = m >> shift;
    u64 rem = m & ((1UL << shift) - 1);
    u64 half = 1UL << (shift - 1);
    if (rem > half || (rem == half && (q & 1))) q++;
  }
  u64 bits = ((u64)(be - 1) << (p - 1)) + q;
  if (bits >= (u64)top << (p - 1)) bits = (u64)top << (p - 1);
  return sign | bits;
}

/* A finite nonzero binary64 as m * 2^e. */
static u64 d_unpack(u64 a, long *e) {
  long be = (long)((a >> 52) & 0x7FF);
  u64 m = a & 0x000FFFFFFFFFFFFFUL;
  if (be == 0) { *e = -1074; return m; }
  *e = be - 1075;
  return m | 0x0010000000000000UL;
}

/* m (nonzero, below 2^53) shifted up to 53 significant bits. */
static u64 d_norm(u64 m, long *e) {
  while (!(m >> 52)) { m <<= 1; *e -= 1; }
  return m;
}

/* The high 64 bits of a * b, and its low 64 bits in *lo. */
static u64 mul_hi(u64 a, u64 b, u64 *lo) {
  u64 a0 = a & 0xFFFFFFFFUL, a1 = a >> 32, b0 = b & 0xFFFFFFFFUL, b1 = b >> 32;
  u64 p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
  u64 mid = (p00 >> 32) + (p01 & 0xFFFFFFFFUL) + (p10 & 0xFFFFFFFFUL);
  *lo = (mid << 32) | (p00 & 0xFFFFFFFFUL);
  return p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}

u64 __ccomp_dadd(u64 a, u64 b) {
  if (d_isnan(a)) return a | D_QUIET;
  if (d_isnan(b)) return b | D_QUIET;
  if (d_isinf(a)) return (d_isinf(b) && (a ^ b) == D_SIGN) ? D_DEFAULT_NAN : a;
  if (d_isinf(b)) return b;
  if (d_iszero(a)) return d_iszero(b) ? (a & b) : b;
  if (d_iszero(b)) return a;
  long ea, eb;
  u64 ma = d_unpack(a, &ea) << 9, mb = d_unpack(b, &eb) << 9;
  int sa = (int)(a >> 63), sb = (int)(b >> 63);
  if (ea < eb) {
    u64 t = ma; ma = mb; mb = t;
    long te = ea; ea = eb; eb = te;
    int ts = sa; sa = sb; sb = ts;
  }
  long d = ea - eb;
  if (d >= 64) mb = 1;
  else if (d > 0) mb = (mb >> d) | ((mb & ((1UL << d) - 1)) != 0);
  if (sa == sb) return fp_pack(sa, ea - 9, ma + mb, 53, 11);
  if (ma == mb) return 0;
  if (ma > mb) return fp_pack(sa, ea - 9, ma - mb, 53, 11);
  return fp_pack(sb, ea - 9, mb - ma, 53, 11);
}

u64 __ccomp_dsub(u64 a, u64 b) {
  if (d_isnan(a)) return a | D_QUIET;
  if (d_isnan(b)) return b | D_QUIET;
  return __ccomp_dadd(a, b ^ D_SIGN);
}

u64 __ccomp_dmul(u64 a, u64 b) {
  if (d_isnan(a)) return a | D_QUIET;
  if (d_isnan(b)) return b | D_QUIET;
  u64 sign = (a ^ b) & D_SIGN;
  if (d_isinf(a) || d_isinf(b))
    return (d_iszero(a) || d_iszero(b)) ? D_DEFAULT_NAN : sign | D_EXP;
  if (d_iszero(a) || d_iszero(b)) return sign;
  long ea, eb;
  u64 ma = d_unpack(a, &ea), mb = d_unpack(b, &eb);
  ma = d_norm(ma, &ea);
  mb = d_norm(mb, &eb);
  u64 lo;
  u64 hi = mul_hi(ma << 11, mb << 11, &lo);
  return fp_pack(sign != 0, ea + eb + 42, hi | (lo != 0), 53, 11);
}

u64 __ccomp_ddiv(u64 a, u64 b) {
  if (d_isnan(a)) return a | D_QUIET;
  if (d_isnan(b)) return b | D_QUIET;
  u64 sign = (a ^ b) & D_SIGN;
  if (d_isinf(a)) return d_isinf(b) ? D_DEFAULT_NAN : sign | D_EXP;
  if (d_isinf(b)) return sign;
  if (d_iszero(b)) return d_iszero(a) ? D_DEFAULT_NAN : sign | D_EXP;
  if (d_iszero(a)) return sign;
  long ea, eb;
  u64 ma = d_unpack(a, &ea), mb = d_unpack(b, &eb);
  ma = d_norm(ma, &ea);
  mb = d_norm(mb, &eb);
  u64 q = 0, r = ma;
  for (int i = 0; i < 64; i++) {
    q <<= 1;
    if (r >= mb) { r -= mb; q |= 1; }
    r <<= 1;
  }
  return fp_pack(sign != 0, ea - eb - 63, q | (r != 0), 53, 11);
}

/* 0 equal, 1 less, 2 greater, 3 unordered. */
long __ccomp_dcmp(u64 a, u64 b) {
  if (d_isnan(a) || d_isnan(b)) return 3;
  if (a == b || (d_iszero(a) && d_iszero(b))) return 0;
  int sa = (int)(a >> 63), sb = (int)(b >> 63);
  if (sa != sb) return sa ? 1 : 2;
  return ((a < b) != sa) ? 1 : 2;
}

u64 __ccomp_f2d(u64 a) {
  u64 sign = (a & 0x80000000UL) << 32;
  u64 mag = a & 0x7FFFFFFFUL;
  if (mag >= 0x7F800000UL)
    return sign | D_EXP | ((mag & 0x7FFFFFUL) << 29) | (mag > 0x7F800000UL ? D_QUIET : 0);
  if (mag == 0) return sign;
  long be = (long)(mag >> 23);
  u64 m = mag & 0x7FFFFFUL;
  long e = -149;
  if (be != 0) { e = be - 150; m |= 0x800000UL; }
  return fp_pack(sign != 0, e, m, 53, 11);
}

u64 __ccomp_d2f(u64 a) {
  u64 sign = (a >> 32) & 0x80000000UL;
  if (d_isnan(a)) return sign | 0x7FC00000UL | ((a >> 29) & 0x7FFFFFUL);
  if (d_isinf(a)) return sign | 0x7F800000UL;
  if (d_iszero(a)) return sign;
  long e;
  u64 m = d_unpack(a, &e);
  return fp_pack(sign != 0, e, m, 24, 8);
}

u64 __ccomp_fadd(u64 a, u64 b) { return __ccomp_d2f(__ccomp_dadd(__ccomp_f2d(a), __ccomp_f2d(b))); }
u64 __ccomp_fsub(u64 a, u64 b) { return __ccomp_d2f(__ccomp_dsub(__ccomp_f2d(a), __ccomp_f2d(b))); }
u64 __ccomp_fmul(u64 a, u64 b) { return __ccomp_d2f(__ccomp_dmul(__ccomp_f2d(a), __ccomp_f2d(b))); }
u64 __ccomp_fdiv(u64 a, u64 b) { return __ccomp_d2f(__ccomp_ddiv(__ccomp_f2d(a), __ccomp_f2d(b))); }
long __ccomp_fcmp(u64 a, u64 b) { return __ccomp_dcmp(__ccomp_f2d(a), __ccomp_f2d(b)); }

u64 __ccomp_i2d(long x) {
  if (x == 0) return 0;
  return x < 0 ? fp_pack(1, 0, 0UL - (u64)x, 53, 11) : fp_pack(0, 0, (u64)x, 53, 11);
}
u64 __ccomp_u2d(u64 x) { return x ? fp_pack(0, 0, x, 53, 11) : 0; }
u64 __ccomp_i2f(long x) {
  if (x == 0) return 0;
  return x < 0 ? fp_pack(1, 0, 0UL - (u64)x, 24, 8) : fp_pack(0, 0, (u64)x, 24, 8);
}
u64 __ccomp_u2f(u64 x) { return x ? fp_pack(0, 0, x, 24, 8) : 0; }

/* Truncation to a signed integer of `bits` bits; out of range, x86's indefinite
   value (the most negative one). */
static u64 d_trunc(u64 a, int bits) {
  u64 indef = 1UL << (bits - 1);
  if (d_isnan(a) || d_isinf(a)) return indef;
  if (d_iszero(a)) return 0;
  long e;
  u64 m = d_unpack(a, &e);
  u64 v;
  if (e >= 11) return indef;
  if (e >= 0) v = m << e;
  else if (e <= -64) v = 0;
  else v = m >> -e;
  int neg = (int)(a >> 63);
  if (v > indef || (v == indef && !neg)) return indef;
  return neg ? 0UL - v : v;
}

long __ccomp_d2i(u64 a) { return (long)d_trunc(a, 64); }
long __ccomp_d2i32(u64 a) { return (long)(int)(unsigned int)d_trunc(a, 32); }
/* gcc's sequence for double to unsigned long. */
u64 __ccomp_d2u(u64 a) {
  if (__ccomp_dcmp(a, D_TWO63) & 1) return d_trunc(a, 64);
  return d_trunc(__ccomp_dsub(a, D_TWO63), 64) ^ D_SIGN;
}

/* ---- math.h (the part on encodings) ---- */

/* floor (up == 0) or ceil (up == 1) of a binary64 encoding. */
static u64 d_floor(u64 a, int up) {
  long be = (long)((a >> 52) & 0x7FF);
  int neg = (int)(a >> 63);
  if (be >= 1075) return d_isnan(a) ? a | D_QUIET : a;
  if (be < 1023) {
    if (d_iszero(a)) return a;
    if (neg) return up ? D_SIGN : 0xBFF0000000000000UL;
    return up ? 0x3FF0000000000000UL : 0;
  }
  u64 frac = (1UL << (1075 - be)) - 1;
  if (!(a & frac)) return a;
  u64 t = a & ~frac;
  if (neg != up) return __ccomp_dadd(t, neg ? 0xBFF0000000000000UL : 0x3FF0000000000000UL);
  return t;
}

union dbits { double d; u64 u; };

double fabs(double x) { union dbits v; v.d = x; v.u &= ~D_SIGN; return v.d; }

float fabsf(float x) {
  union { float f; unsigned int u; } v;
  v.f = x;
  v.u &= 0x7FFFFFFFU;
  return v.f;
}

double floor(double x) { union dbits v; v.d = x; v.u = d_floor(v.u, 0); return v.d; }

double ceil(double x) { union dbits v; v.d = x; v.u = d_floor(v.u, 1); return v.d; }

double trunc(double x) {
  union dbits v;
  v.d = x;
  return (v.u >> 63) ? -floor(-x) : floor(x);
}

/* @(#)e_pow.c 1.5 04/04/22 SMI */
/*
 * ====================================================
 * Copyright (C) 2004 by Sun Microsystems, Inc. All rights reserved.
 *
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */




/* __ieee754_pow(x,y) return x**y
 *
 *		      n
 * Method:  Let x =  2   * (1+f)
 *	1. Compute and return log2(x) in two pieces:
 *		log2(x) = w1 + w2,
 *	   where w1 has 53-24 = 29 bit trailing zeros.
 *	2. Perform y*log2(x) = n+y' by simulating muti-precision
 *	   arithmetic, where |y'|<=0.5.
 *	3. Return x**y = 2**n*exp(y'*log2)
 *
 * Special cases:
 *	1.  (anything) ** 0  is 1
 *	2.  (anything) ** 1  is itself
 *	3.  (anything) ** NAN is NAN
 *	4.  NAN ** (anything except 0) is NAN
 *	5.  +-(|x| > 1) **  +INF is +INF
 *	6.  +-(|x| > 1) **  -INF is +0
 *	7.  +-(|x| < 1) **  +INF is +0
 *	8.  +-(|x| < 1) **  -INF is +INF
 *	9.  +-1         ** +-INF is 1
 *	10. +0 ** (+anything except 0, NAN)               is +0
 *	11. -0 ** (+anything except 0, NAN, odd integer)  is +0
 *	12. +0 ** (-anything except 0, NAN)               is +INF
 *	13. -0 ** (-anything except 0, NAN, odd integer)  is +INF
 *	14. -0 ** (odd integer) = -( +0 ** (odd integer) )
 *	15. +INF ** (+anything except 0,NAN) is +INF
 *	16. +INF ** (-anything except 0,NAN) is +0
 *	17. -INF ** (anything)  = -0 ** (-anything)
 *	18. (-anything) ** (integer) is (-1)**(integer)*(+anything**integer)
 *	19. (-anything except 0 and inf) ** (non-integer) is NAN
 *
 * Accuracy:
 *	pow(x,y) returns x**y nearly rounded. In particular
 *			pow(integer,integer)
 *	always returns the correct integer provided it is
 *	representable.
 *
 * Constants :
 * The hexadecimal values are the intended ones for the following
 * constants. The decimal values may be used, provided that the
 * compiler will convert from decimal to binary accurately enough
 * to produce the hexadecimal values shown.
 */

/* Adapted from OpenLibm src/e_pow.c (Sun fdlibm).
 * https://github.com/JuliaMath/openlibm/blob/master/src/e_pow.c
 * Use the runtime's binary64 union instead of platform word-access headers.
 * The half-power sqrt shortcut is omitted: the general log/exp path handles it.
 * The huge-exponent near-one shortcut also uses the full split logarithm, to
 * avoid loss of accuracy for bases just below one.
 * This implements fdlibm's near-rounded result, not a correctly-rounded libm;
 * errno and floating-point exception flags are not modeled by this runtime.
 */
static unsigned int pow_hi(double x) {
  union dbits v; v.d = x; return (unsigned int)(v.u >> 32);
}
static unsigned int pow_lo(double x) {
  union dbits v; v.d = x; return (unsigned int)v.u;
}
static double pow_set_hi(double x, unsigned int hi) {
  union dbits v; v.d = x; v.u = ((u64)hi << 32) | (v.u & 0xffffffffUL); return v.d;
}
static double pow_set_lo(double x, unsigned int lo) {
  union dbits v; v.d = x; v.u = (v.u & 0xffffffff00000000UL) | lo; return v.d;
}
#define EXTRACT_WORDS(hi,lo,x) do { (hi) = (int)pow_hi(x); (lo) = pow_lo(x); } while (0)
#define GET_HIGH_WORD(hi,x) do { (hi) = (int)pow_hi(x); } while (0)
#define SET_HIGH_WORD(x,hi) do { (x) = pow_set_hi(x, (unsigned int)(hi)); } while (0)
#define SET_LOW_WORD(x,lo) do { (x) = pow_set_lo(x, (unsigned int)(lo)); } while (0)

/* Only used for subnormal results: z is close to 1 and -1075 <= n <= -1022.
 * First scale normally, then round once into the subnormal range. */
static double pow_subnormal(double z, int n) {
  union dbits scale;
  scale.u = (u64)(n + 2045) << 52;
  return (z * scale.d) * 0x1p-1022;
}

static const double
bp[] = {1.0, 1.5,},
dp_h[] = { 0.0, 5.84962487220764160156e-01,}, /* 0x3FE2B803, 0x40000000 */
dp_l[] = { 0.0, 1.35003920212974897128e-08,}, /* 0x3E4CFDEB, 0x43CFD006 */
zero    =  0.0,
one	=  1.0,
two	=  2.0,
two53	=  9007199254740992.0,	/* 0x43400000, 0x00000000 */
huge	=  1.0e300,
tiny    =  1.0e-300,
	/* poly coefs for (3/2)*(log(x)-2s-2/3*s**3 */
L1  =  5.99999999999994648725e-01, /* 0x3FE33333, 0x33333303 */
L2  =  4.28571428578550184252e-01, /* 0x3FDB6DB6, 0xDB6FABFF */
L3  =  3.33333329818377432918e-01, /* 0x3FD55555, 0x518F264D */
L4  =  2.72728123808534006489e-01, /* 0x3FD17460, 0xA91D4101 */
L5  =  2.30660745775561754067e-01, /* 0x3FCD864A, 0x93C9DB65 */
L6  =  2.06975017800338417784e-01, /* 0x3FCA7E28, 0x4A454EEF */
P1   =  1.66666666666666019037e-01, /* 0x3FC55555, 0x5555553E */
P2   = -2.77777777770155933842e-03, /* 0xBF66C16C, 0x16BEBD93 */
P3   =  6.61375632143793436117e-05, /* 0x3F11566A, 0xAF25DE2C */
P4   = -1.65339022054652515390e-06, /* 0xBEBBBD41, 0xC5D26BF1 */
P5   =  4.13813679705723846039e-08, /* 0x3E663769, 0x72BEA4D0 */
lg2  =  6.93147180559945286227e-01, /* 0x3FE62E42, 0xFEFA39EF */
lg2_h  =  6.93147182464599609375e-01, /* 0x3FE62E43, 0x00000000 */
lg2_l  = -1.90465429995776804525e-09, /* 0xBE205C61, 0x0CA86C39 */
ovt =  8.0085662595372944372e-0017, /* -(1024-log2(ovfl+.5ulp)) */
cp    =  9.61796693925975554329e-01, /* 0x3FEEC709, 0xDC3A03FD =2/(3ln2) */
cp_h  =  9.61796700954437255859e-01, /* 0x3FEEC709, 0xE0000000 =(float)cp */
cp_l  = -7.02846165095275826516e-09; /* 0xBE3E2FE0, 0x145B01F5 =tail of cp_h */

double
pow(double x, double y)
{
	double z,ax,z_h,z_l,p_h,p_l;
	double y1,t1,t2,r,s,t,u,v,w;
	int i,j,k,yisint,n;
	int hx,hy,ix,iy;
	unsigned int lx,ly;

	EXTRACT_WORDS(hx,lx,x);
	EXTRACT_WORDS(hy,ly,y);
	ix = hx&0x7fffffff;  iy = hy&0x7fffffff;

    /* y==zero: x**0 = 1 */
	if((iy|ly)==0) return one;

    /* x==1: 1**y = 1, even if y is NaN */
	if (hx==0x3ff00000 && lx == 0) return one;

    /* y!=zero: result is NaN if either arg is NaN */
	if(ix > 0x7ff00000 || ((ix==0x7ff00000)&&(lx!=0)) ||
	   iy > 0x7ff00000 || ((iy==0x7ff00000)&&(ly!=0)))
		return (x+0.0)+(y+0.0);

    /* determine if y is an odd int when x < 0
     * yisint = 0	... y is not an integer
     * yisint = 1	... y is an odd int
     * yisint = 2	... y is an even int
     */
	yisint  = 0;
	if(hx<0) {
	    if(iy>=0x43400000) yisint = 2; /* even integer y */
	    else if(iy>=0x3ff00000) {
		k = (iy>>20)-0x3ff;	   /* exponent */
		if(k>20) {
		    j = ly>>(52-k);
		    if(((unsigned int)j<<(52-k))==ly) yisint = 2-(j&1);
		} else if(ly==0) {
		    j = iy>>(20-k);
		    if((j<<(20-k))==iy) yisint = 2-(j&1);
		}
	    }
	}

    /* special value of y */
	if(ly==0) {
	    if (iy==0x7ff00000) {	/* y is +-inf */
	        if(((ix-0x3ff00000)|lx)==0)
		    return  one;	/* (-1)**+-inf is 1 */
	        else if (ix >= 0x3ff00000)/* (|x|>1)**+-inf = inf,0 */
		    return (hy>=0)? y: zero;
	        else			/* (|x|<1)**-,+inf = inf,0 */
		    return (hy<0)?-y: zero;
	    }
	    if(iy==0x3ff00000) {	/* y is  +-1 */
		if(hy<0) return one/x; else return x;
	    }
            if(hy==0x40000000) return x*x;   /* y is  2 */
            if(hy==0x40080000) return x*x*x; /* y is  3 */
            if(hy==0x40100000) {             /* y is  4 */
                u = x*x;
                return u*u;
            }

	}

	ax   = fabs(x);
    /* special value of x */
	if(lx==0) {
	    if(ix==0x7ff00000||ix==0||ix==0x3ff00000){
		z = ax;			/*x is +-0,+-inf,+-1*/
		if(hy<0) z = one/z;	/* z = (1/|x|) */
		if(hx<0) {
		    if(((ix-0x3ff00000)|yisint)==0) {
			z = (z-z)/(z-z); /* (-1)**non-int is NaN */
		    } else if(yisint==1)
			z = -z;		/* (x<0)**odd = -(|x|**odd) */
		}
		return z;
	    }
	}

    /* Distinguish a negative base without shifting a signed integer. */
	n = hx < 0 ? 0 : -1;

    /* (x<0)**(non-int) is NaN */
	if((n|yisint)==0) return (x-x)/(x-x);

	s = one; /* s (sign of result -ve**odd) = -1 else = 1 */
	if((n|(yisint-1))==0) s = -one;/* (-ve)**(odd int) */

    /* |y| is huge */
	if(iy>0x41e00000) { /* if |y| > 2**31 */
	    if(iy>0x43f00000){	/* if |y| > 2**64, must o/uflow */
		if(ix<=0x3fefffff) return (hy<0)? huge*huge:tiny*tiny;
		if(ix>=0x3ff00000) return (hy>0)? huge*huge:tiny*tiny;
	    }
	/* over/underflow if x is not close to one */
	    if(ix<0x3fefffff) return (hy<0)? s*huge*huge:s*tiny*tiny;
	    if(ix>0x3ff00000) return (hy>0)? s*huge*huge:s*tiny*tiny;
	/* For x close to one, use the full split logarithm below as well.
         * The short Taylor path loses accuracy for large y just below x=1. */
	}
	{
	    double ss,s2,s_h,s_l,t_h,t_l;
	    n = 0;
	/* take care subnormal number */
	    if(ix<0x00100000)
		{ax *= two53; n -= 53; GET_HIGH_WORD(ix,ax); }
	    n  += ((ix)>>20)-0x3ff;
	    j  = ix&0x000fffff;
	/* determine interval */
	    ix = j|0x3ff00000;		/* normalize ix */
	    if(j<=0x3988E) k=0;		/* |x|<sqrt(3/2) */
	    else if(j<0xBB67A) k=1;	/* |x|<sqrt(3)   */
	    else {k=0;n+=1;ix -= 0x00100000;}
	    SET_HIGH_WORD(ax,ix);

	/* compute ss = s_h+s_l = (x-1)/(x+1) or (x-1.5)/(x+1.5) */
	    u = ax-bp[k];		/* bp[0]=1.0, bp[1]=1.5 */
	    v = one/(ax+bp[k]);
	    ss = u*v;
	    s_h = ss;
	    SET_LOW_WORD(s_h,0);
	/* t_h=ax+bp[k] High */
	    t_h = zero;
	    SET_HIGH_WORD(t_h,((ix>>1)|0x20000000)+0x00080000+(k<<18));
	    t_l = ax - (t_h-bp[k]);
	    s_l = v*((u-s_h*t_h)-s_h*t_l);
	/* compute log(ax) */
	    s2 = ss*ss;
	    r = s2*s2*(L1+s2*(L2+s2*(L3+s2*(L4+s2*(L5+s2*L6)))));
	    r += s_l*(s_h+ss);
	    s2  = s_h*s_h;
	    t_h = 3.0+s2+r;
	    SET_LOW_WORD(t_h,0);
	    t_l = r-((t_h-3.0)-s2);
	/* u+v = ss*(1+...) */
	    u = s_h*t_h;
	    v = s_l*t_h+t_l*ss;
	/* 2/(3log2)*(ss+...) */
	    p_h = u+v;
	    SET_LOW_WORD(p_h,0);
	    p_l = v-(p_h-u);
	    z_h = cp_h*p_h;		/* cp_h+cp_l = 2/(3*log2) */
	    z_l = cp_l*p_h+p_l*cp+dp_l[k];
	/* log2(ax) = (ss+..)*2/(3*log2) = n + dp_h + z_h + z_l */
	    t = (double)n;
	    t1 = (((z_h+z_l)+dp_h[k])+t);
	    SET_LOW_WORD(t1,0);
	    t2 = z_l-(((t1-t)-dp_h[k])-z_h);
	}

    /* split up y into y1+y2 and compute (y1+y2)*(t1+t2) */
	y1  = y;
	SET_LOW_WORD(y1,0);
	p_l = (y-y1)*t1+y*t2;
	p_h = y1*t1;
	z = p_l+p_h;
	EXTRACT_WORDS(j,i,z);
	if (j>=0x40900000) {				/* z >= 1024 */
	    if(((j-0x40900000)|i)!=0)			/* if z > 1024 */
		return s*huge*huge;			/* overflow */
	    else {
		if(p_l+ovt>z-p_h) return s*huge*huge;	/* overflow */
	    }
	} else if((j&0x7fffffff)>=0x4090cc00 ) {	/* z <= -1075 */
	    if(((j-0xc090cc00)|i)!=0) 		/* z < -1075 */
		return s*tiny*tiny;		/* underflow */
	    else {
		if(p_l<=z-p_h) return s*tiny*tiny;	/* underflow */
	    }
	}
    /*
     * compute 2**(p_h+p_l)
     */
	i = j&0x7fffffff;
	k = (i>>20)-0x3ff;
	n = 0;
	if(i>0x3fe00000) {		/* if |z| > 0.5, set n = [z+0.5] */
	    n = j+(0x00100000>>(k+1));
	    k = ((n&0x7fffffff)>>20)-0x3ff;	/* new k for n */
	    t = zero;
	    SET_HIGH_WORD(t,n&~(0x000fffff>>k));
	    n = ((n&0x000fffff)|0x00100000)>>(20-k);
	    if(j<0) n = -n;
	    p_h -= t;
	}
	t = p_l+p_h;
	SET_LOW_WORD(t,0);
	u = t*lg2_h;
	v = (p_l-(t-p_h))*lg2+t*lg2_l;
	z = u+v;
	w = v-(z-u);
	t  = z*z;
	t1  = z - t*(P1+t*(P2+t*(P3+t*(P4+t*P5))));
	r  = (z*t1)/(t1-two)-(w+z*w);
	z  = one-(r-z);
	GET_HIGH_WORD(j,z);
	j += n * 0x00100000;
	if((j>>20)<=0) z = pow_subnormal(z,n);	/* subnormal output */
	else SET_HIGH_WORD(z,j);
	return s*z;
}


#undef EXTRACT_WORDS
#undef GET_HIGH_WORD
#undef SET_HIGH_WORD
#undef SET_LOW_WORD

/* ---- files ---- */

/* Files live in the linear memory, like the output buffer: the runtime makes no system
   calls, so a program sees exactly the files it created itself (fopen with "w" or "a",
   tmpfile), and they end with it. Opening any other name for reading fails with a null
   pointer, as for a missing file. A stream is a position in one file; the file
   outlives a remove() while a stream still refers to it. Writes go to the file at
   once, so no buffering is observable. */
struct file_node { struct file_node *next; char *name; char *data; size_t len; size_t cap; };

struct _IO_FILE {
  struct file_node *node;
  size_t pos;
  int read, write, append, eof, err;
  int unget; /* a character pushed back by ungetc, or -1 */
};

static struct file_node *files;

static struct file_node *file_find(const char *name) {
  for (struct file_node *n = files; n; n = n->next)
    if (strcmp(n->name, name) == 0) return n;
  return 0;
}

/* The stream of a file, or a null pointer for stdout, stderr and a null stream. */
static FILE *file_of(FILE *f) {
  if (f == 0 || f == __stdout || f == __stderr) return 0;
  return f;
}

static int file_reserve(struct file_node *n, size_t need) {
  if (need <= n->cap) return 1;
  size_t cap = n->cap ? n->cap : 64;
  while (cap < need) cap *= 2;
  char *data = malloc(cap);
  if (data == 0) return 0;
  if (n->len) memcpy(data, n->data, n->len);
  n->data = data;
  n->cap = cap;
  return 1;
}

static void file_put(FILE *f, int c) {
  struct file_node *n = f->node;
  if (!f->write) { f->err = 1; return; }
  if (f->append) f->pos = n->len;
  f->unget = -1;
  if (!file_reserve(n, f->pos + 1)) { f->err = 1; return; }
  /* a write after a seek past the end fills the gap with zeros */
  while (n->len < f->pos) n->data[n->len++] = 0;
  n->data[f->pos++] = (char)c;
  if (f->pos > n->len) n->len = f->pos;
}

static int file_get(FILE *f) {
  if (f->unget >= 0) {
    int c = f->unget;
    f->unget = -1;
    return c;
  }
  if (!f->read) { f->err = 1; return EOF; }
  if (f->pos >= f->node->len) { f->eof = 1; return EOF; }
  return (unsigned char)f->node->data[f->pos++];
}

static FILE *file_stream(struct file_node *n, int read, int write, int append) {
  FILE *f = malloc(sizeof(FILE));
  if (f == 0) return 0;
  f->node = n;
  f->pos = 0;
  f->read = read;
  f->write = write;
  f->append = append;
  f->eof = 0;
  f->err = 0;
  f->unget = -1;
  return f;
}

FILE *fopen(const char *restrict name, const char *restrict mode) {
  int plus = 0;
  if (mode[0] == 0) return 0;
  for (const char *m = mode + 1; *m; m++) if (*m == '+') plus = 1;
  struct file_node *n = file_find(name);
  if (mode[0] == 'r') {
    if (n == 0) return 0;
    return file_stream(n, 1, plus, 0);
  }
  if (mode[0] != 'w' && mode[0] != 'a') return 0;
  if (n == 0) {
    n = malloc(sizeof(struct file_node));
    char *copy = strdup(name);
    if (n == 0 || copy == 0) return 0;
    n->name = copy;
    n->data = 0;
    n->len = 0;
    n->cap = 0;
    n->next = files;
    files = n;
  }
  if (mode[0] == 'w') {
    n->len = 0;
    return file_stream(n, plus, 1, 0);
  }
  FILE *f = file_stream(n, plus, 1, 1);
  if (f != 0 && !plus) f->pos = n->len;
  return f;
}

FILE *tmpfile(void) {
  struct file_node *n = malloc(sizeof(struct file_node));
  if (n == 0) return 0;
  n->next = 0;
  n->name = 0;
  n->data = 0;
  n->len = 0;
  n->cap = 0;
  return file_stream(n, 1, 1, 0);
}

int fclose(FILE *f) {
  FILE *g = file_of(f);
  if (g) { g->read = 0; g->write = 0; }
  return 0;
}

int remove(const char *name) {
  for (struct file_node **p = &files; *p; p = &(*p)->next)
    if (strcmp((*p)->name, name) == 0) { *p = (*p)->next; return 0; }
  return -1;
}

int rename(const char *old, const char *new) {
  struct file_node *n = file_find(old);
  if (n == 0) return -1;
  if (strcmp(old, new) == 0) return 0;
  char *copy = strdup(new);
  if (copy == 0) return -1;
  remove(new);
  n->name = copy;
  return 0;
}

int fgetc(FILE *f) {
  FILE *g = file_of(f);
  if (g == 0) return EOF;
  return file_get(g);
}

int getc(FILE *f) { return fgetc(f); }

int ungetc(int c, FILE *f) {
  FILE *g = file_of(f);
  if (g == 0 || c == EOF || g->unget >= 0) return EOF;
  g->unget = (unsigned char)c;
  g->eof = 0;
  return (unsigned char)c;
}

char *fgets(char *restrict s, int size, FILE *restrict f) {
  FILE *g = file_of(f);
  if (size <= 0 || g == 0) return 0;
  int i = 0;
  while (i < size - 1) {
    int c = file_get(g);
    if (c == EOF) {
      if (i == 0) return 0;
      break;
    }
    s[i++] = (char)c;
    if (c == '\n') break;
  }
  s[i] = 0;
  return s;
}

size_t fread(void *restrict p, size_t size, size_t nmemb, FILE *restrict f) {
  FILE *g = file_of(f);
  if (g == 0 || size == 0 || nmemb == 0) return 0;
  char *d = p;
  size_t total = size * nmemb, i = 0;
  while (i < total) {
    int c = file_get(g);
    if (c == EOF) break;
    d[i++] = (char)c;
  }
  return i / size;
}

int fseek(FILE *f, long offset, int whence) {
  FILE *g = file_of(f);
  if (g == 0) return -1;
  long base;
  if (whence == SEEK_SET) base = 0;
  else if (whence == SEEK_CUR) base = (long)g->pos - (g->unget >= 0);
  else if (whence == SEEK_END) base = (long)g->node->len;
  else return -1;
  if (base + offset < 0) return -1;
  g->pos = (size_t)(base + offset);
  g->unget = -1;
  g->eof = 0;
  return 0;
}

long ftell(FILE *f) {
  FILE *g = file_of(f);
  if (g == 0) return -1;
  return (long)g->pos - (g->unget >= 0);
}

void rewind(FILE *f) {
  FILE *g = file_of(f);
  if (g == 0) return;
  fseek(g, 0, SEEK_SET);
  g->err = 0;
}

int fgetpos(FILE *restrict f, fpos_t *restrict pos) {
  long p = ftell(f);
  if (p < 0) return -1;
  *pos = p;
  return 0;
}

int fsetpos(FILE *f, const fpos_t *pos) { return fseek(f, (long)*pos, SEEK_SET); }

int feof(FILE *f) {
  FILE *g = file_of(f);
  return g != 0 && g->eof;
}

int ferror(FILE *f) {
  FILE *g = file_of(f);
  return g != 0 && g->err;
}

void clearerr(FILE *f) {
  FILE *g = file_of(f);
  if (g) { g->eof = 0; g->err = 0; }
}

/* Output is buffered until exit whatever the mode (docs/CCompiler.md). */
int setvbuf(FILE *restrict f, char *restrict buf, int mode, size_t size) {
  (void)f; (void)buf; (void)mode; (void)size;
  return 0;
}

void setbuf(FILE *restrict f, char *restrict buf) { (void)f; (void)buf; }

/* ---- output ---- */

/* A sink: the output buffer (buf == 0), a file (file != 0), or a string of capacity
   cap. */
struct sink { char *buf; size_t cap; size_t n; int discard; FILE *file; };

static void put(struct sink *s, int c) {
  if (s->file) { file_put(s->file, c); s->n++; return; }
  if (s->discard) { s->n++; return; }
  if (s->buf == 0) {
    unsigned long *ctl = CTL;
    unsigned long n = ctl[3];
    if (n < ctl[7]) {
      char *out = (char *)ctl[6];
      out[n] = (char)c;
      ctl[3] = n + 1;
    }
  } else if (s->n + 1 < s->cap) {
    s->buf[s->n] = (char)c;
  }
  s->n++;
}

static void puts_n(struct sink *s, const char *p, size_t n) {
  for (size_t i = 0; i < n; i++) put(s, p[i]);
}

static void pad(struct sink *s, int c, int n) {
  for (int i = 0; i < n; i++) put(s, c);
}

/* Format an unsigned value in `base`; returns the number of digits written to d. */
static int digits(char *d, unsigned long long v, unsigned base, int upper) {
  const char *xs = "0123456789abcdef";
  if (upper) xs = "0123456789ABCDEF";
  int n = 0;
  do { d[n++] = xs[v % base]; v /= base; } while (v != 0);
  return n;
}

/* ---- floating-point output ---- */

/* A natural number in base 2^32, least significant limb first. */
struct big { unsigned int d[84]; int n; };

static void big_mul(struct big *b, unsigned int k) {
  u64 carry = 0;
  for (int i = 0; i < b->n; i++) {
    u64 t = (u64)b->d[i] * k + carry;
    b->d[i] = (unsigned int)t;
    carry = t >> 32;
  }
  if (carry) b->d[b->n++] = (unsigned int)carry;
}

static unsigned int big_div(struct big *b, unsigned int k) {
  u64 rem = 0;
  for (int i = b->n - 1; i >= 0; i--) {
    u64 t = (rem << 32) | b->d[i];
    b->d[i] = (unsigned int)(t / k);
    rem = t % k;
  }
  while (b->n > 0 && b->d[b->n - 1] == 0) b->n--;
  return (unsigned int)rem;
}

/* The exact decimal digits of a finite positive double (most significant first, no
   leading or trailing zero) into dig; returns their number n, and sets *dp so that
   the value is 0.dig[0]...dig[n-1] * 10^dp. */
static int d_digits(u64 a, char *dig, int *dp) {
  long e;
  u64 m = d_unpack(a, &e);
  while (e < 0 && !(m & 1)) { m >>= 1; e++; }
  struct big b;
  b.d[0] = (unsigned int)m;
  b.d[1] = (unsigned int)(m >> 32);
  b.n = b.d[1] ? 2 : 1;
  long k = 0;
  if (e > 0) {
    long i = e;
    for (; i >= 31; i -= 31) big_mul(&b, 1U << 31);
    big_mul(&b, 1U << i);
  } else if (e < 0) {
    k = -e;
    long i = k;
    for (; i >= 13; i -= 13) big_mul(&b, 1220703125U);
    for (; i > 0; i--) big_mul(&b, 5);
  }
  /* the value is b * 10^-k */
  char rev[800];
  int n = 0;
  while (b.n > 0) {
    unsigned int chunk = big_div(&b, 1000000000U);
    for (int j = 0; j < 9; j++) { rev[n++] = (char)('0' + chunk % 10); chunk /= 10; }
  }
  while (n > 1 && rev[n - 1] == '0') n--;
  int lo = 0;
  while (rev[lo] == '0') lo++;
  for (int j = 0; j < n - lo; j++) dig[j] = rev[n - 1 - j];
  *dp = n - (int)k;
  return n - lo;
}

/* Round the n digits of dig to their first `keep` (half to even, on the exact value);
   returns the new number of digits (0 for zero), adjusting *dp on a carry out. */
static int round_digits(char *dig, int n, int keep, int *dp) {
  if (keep >= n) return n;
  if (keep < 0) return 0;
  int up = dig[keep] > '5';
  if (dig[keep] == '5') {
    int rest = 0;
    for (int i = keep + 1; i < n; i++) if (dig[i] != '0') rest = 1;
    up = rest || (keep > 0 && ((dig[keep - 1] - '0') & 1));
  }
  n = keep;
  if (!up) {
    while (n > 0 && dig[n - 1] == '0') n--;
    return n;
  }
  while (n > 0 && dig[n - 1] == '9') n--;
  if (n == 0) { dig[0] = '1'; *dp += 1; return 1; }
  dig[n - 1]++;
  return n;
}

static char digit_at(const char *dig, int n, int i) { return (i >= 0 && i < n) ? dig[i] : '0'; }

/* printf's %f, %e and %g (and upper case) of the binary64 encoding a; flags: 1 '-',
   2 '0', 4 '+', 8 ' ', 16 '#'. */
static void fmt_float(struct sink *s, u64 a, char c, int prec, int flags, int width) {
  int left = flags & 1, zero = flags & 2, plus = flags & 4, space = flags & 8, alt = flags & 16;
  int upper = c == 'F' || c == 'E' || c == 'G';
  char k = (char)(c | 32);
  const char *sgn = "";
  if (a >> 63) sgn = "-"; else if (plus) sgn = "+"; else if (space) sgn = " ";
  char out[1300];
  int o = 0;
  if (d_isnan(a) || d_isinf(a)) {
    const char *t;
    if (d_isnan(a)) { if (upper) t = "NAN"; else t = "nan"; }
    else if (upper) t = "INF"; else t = "inf";
    while (*t) out[o++] = *t++;
    zero = 0;
  } else {
    if (prec < 0) prec = 6;
    if (prec > 1000) prec = 1000;
    char dig[800];
    int dp = 0, n = 0;
    if (!d_iszero(a)) n = d_digits(a & ~D_SIGN, dig, &dp);
    int fixed = k == 'f', strip = 0;
    if (k == 'g') {
      int p = prec == 0 ? 1 : prec;
      char g[800];
      for (int i = 0; i < n; i++) g[i] = dig[i];
      int gdp = dp;
      int x = round_digits(g, n, p, &gdp) == 0 ? 0 : gdp - 1;
      fixed = p > x && x >= -4;
      prec = fixed ? p - 1 - x : p - 1;
      strip = !alt;
    }
    if (fixed) {
      n = round_digits(dig, n, dp + prec, &dp);
      if (n == 0) dp = 1;
      if (dp <= 0) out[o++] = '0';
      for (int i = 0; i < dp; i++) out[o++] = digit_at(dig, n, i);
      if (prec > 0 || alt) out[o++] = '.';
      for (int i = dp; i < dp + prec; i++) out[o++] = digit_at(dig, n, i);
    } else {
      n = round_digits(dig, n, prec + 1, &dp);
      int x = n == 0 ? 0 : dp - 1;
      out[o++] = digit_at(dig, n, 0);
      if (prec > 0 || alt) out[o++] = '.';
      for (int i = 1; i <= prec; i++) out[o++] = digit_at(dig, n, i);
      if (strip) {
        while (out[o - 1] == '0') o--;
        if (out[o - 1] == '.') o--;
        strip = 0;
      }
      out[o++] = upper ? 'E' : 'e';
      out[o++] = x < 0 ? '-' : '+';
      if (x < 0) x = -x;
      if (x >= 100) out[o++] = (char)('0' + x / 100);
      out[o++] = (char)('0' + x / 10 % 10);
      out[o++] = (char)('0' + x % 10);
    }
    if (strip) {
      int dot = 0;
      for (int i = 0; i < o; i++) if (out[i] == '.') dot = 1;
      if (dot) {
        while (out[o - 1] == '0') o--;
        if (out[o - 1] == '.') o--;
      }
    }
  }
  int sl = (int)strlen(sgn);
  int total = sl + o;
  if (!left && !zero) pad(s, ' ', width - total);
  puts_n(s, sgn, (size_t)sl);
  if (!left && zero) pad(s, '0', width - total);
  puts_n(s, out, (size_t)o);
  if (left) pad(s, ' ', width - total);
}

static int vformat(struct sink *s, const char *fmt, va_list ap) {
  for (const char *p = fmt; *p; p++) {
    if (*p != '%') { put(s, *p); continue; }
    p++;
    int left = 0, zero = 0, plus = 0, space = 0, alt = 0;
    for (;; p++) {
      if (*p == '-') left = 1;
      else if (*p == '0') zero = 1;
      else if (*p == '+') plus = 1;
      else if (*p == ' ') space = 1;
      else if (*p == '#') alt = 1;
      else break;
    }
    int width = 0;
    if (*p == '*') { width = va_arg(ap, int); if (width < 0) { left = 1; width = -width; } p++; }
    else while (*p >= '0' && *p <= '9') { width = width * 10 + (*p - '0'); p++; }
    int prec = -1;
    if (*p == '.') {
      p++;
      prec = 0;
      if (*p == '*') { prec = va_arg(ap, int); p++; }
      else while (*p >= '0' && *p <= '9') { prec = prec * 10 + (*p - '0'); p++; }
    }
    int len = 0; /* 0 int, 1 long, 2 long long, -1 short, -2 char, 3 size_t */
    for (;; p++) {
      if (*p == 'l') len = len == 1 ? 2 : 1;
      else if (*p == 'h') len = len == -1 ? -2 : -1;
      else if (*p == 'z' || *p == 't' || *p == 'j') len = 3;
      else break;
    }
    char c = *p;
    if (c == 0) break;
    if (c == '%') { put(s, '%'); continue; }
    if (c == 'c') {
      int ch = va_arg(ap, int);
      if (!left) pad(s, ' ', width - 1);
      put(s, ch);
      if (left) pad(s, ' ', width - 1);
      continue;
    }
    if (c == 's') {
      const char *str = va_arg(ap, const char *);
      if (str == 0) str = "(null)";
      size_t n = 0;
      while (str[n] && (prec < 0 || n < (size_t)prec)) n++;
      if (!left) pad(s, ' ', width - (int)n);
      puts_n(s, str, n);
      if (left) pad(s, ' ', width - (int)n);
      continue;
    }
    unsigned long long v;
    int neg = 0;
    unsigned base = 10;
    int upper = 0;
    if (c == 'd' || c == 'i') {
      long long x;
      if (len == 2) x = va_arg(ap, long long);
      else if (len == 1 || len == 3) x = va_arg(ap, long);
      else x = va_arg(ap, int);
      if (len == -1) x = (short)x;
      if (len == -2) x = (signed char)x;
      if (x < 0) { neg = 1; v = 0ull - (unsigned long long)x; } else v = (unsigned long long)x;
    } else if (c == 'u' || c == 'x' || c == 'X' || c == 'o' || c == 'p') {
      if (c == 'p') { v = (unsigned long long)(unsigned long)va_arg(ap, void *); alt = 1; base = 16; }
      else if (len == 2) v = va_arg(ap, unsigned long long);
      else if (len == 1 || len == 3) v = va_arg(ap, unsigned long);
      else v = va_arg(ap, unsigned int);
      if (len == -1) v = (unsigned short)v;
      if (len == -2) v = (unsigned char)v;
      if (c == 'x') base = 16;
      if (c == 'X') { base = 16; upper = 1; }
      if (c == 'o') base = 8;
    } else if (c == 'f' || c == 'F' || c == 'e' || c == 'E' || c == 'g' || c == 'G') {
      /* a double argument: its encoding (soft-float) */
      fmt_float(s, va_arg(ap, unsigned long), c, prec,
                left | zero << 1 | plus << 2 | space << 3 | alt << 4, width);
      continue;
    } else {
      /* unsupported conversion (%a, long double): print it literally */
      put(s, '%');
      put(s, c);
      continue;
    }
    char d[32];
    int n = (prec == 0 && v == 0) ? 0 : digits(d, v, base, upper);
    int zeros = prec > n ? prec - n : 0;
    if (alt && base == 8 && zeros == 0 && (n == 0 || d[n - 1] != '0')) zeros = 1;
    const char *prefix = "";
    if (neg) prefix = "-"; else if (plus && (c == 'd' || c == 'i')) prefix = "+";
    else if (space && (c == 'd' || c == 'i')) prefix = " ";
    if (alt && base == 16 && (v != 0 || c == 'p')) { if (upper) prefix = "0X"; else prefix = "0x"; }
    int plen = (int)strlen(prefix);
    int total = plen + zeros + n;
    if (zero && !left && prec < 0) { zeros += width > total ? width - total : 0; total = plen + zeros + n; }
    if (!left) pad(s, ' ', width - total);
    puts_n(s, prefix, (size_t)plen);
    pad(s, '0', zeros);
    while (n > 0) put(s, d[--n]);
    if (left) pad(s, ' ', width - total);
  }
  return (int)s->n;
}

static void stream_sink(struct sink *s, FILE *f) {
  s->buf = 0;
  s->cap = 0;
  s->n = 0;
  s->file = file_of(f);
  s->discard = f != __stdout;
}

int vfprintf(FILE *restrict f, const char *restrict fmt, va_list ap) {
  struct sink s;
  stream_sink(&s, f);
  return vformat(&s, fmt, ap);
}

int vprintf(const char *restrict fmt, va_list ap) { return vfprintf(__stdout, fmt, ap); }

int printf(const char *restrict fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = vfprintf(__stdout, fmt, ap);
  va_end(ap);
  return r;
}

int fprintf(FILE *restrict f, const char *restrict fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = vfprintf(f, fmt, ap);
  va_end(ap);
  return r;
}

int vsnprintf(char *restrict buf, size_t cap, const char *restrict fmt, va_list ap) {
  struct sink s = { buf, cap, 0, cap == 0, 0 };
  int r = vformat(&s, fmt, ap);
  if (cap > 0) buf[s.n < cap ? s.n : cap - 1] = 0;
  return r;
}

int snprintf(char *restrict buf, size_t cap, const char *restrict fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = vsnprintf(buf, cap, fmt, ap);
  va_end(ap);
  return r;
}

int vsprintf(char *restrict buf, const char *restrict fmt, va_list ap) {
  return vsnprintf(buf, (size_t)INT_MAX, fmt, ap);
}

int sprintf(char *restrict buf, const char *restrict fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = vsnprintf(buf, (size_t)INT_MAX, fmt, ap);
  va_end(ap);
  return r;
}

int fputc(int c, FILE *f) {
  struct sink s;
  stream_sink(&s, f);
  if (s.file != 0 && !s.file->write) { s.file->err = 1; return EOF; }
  put(&s, c);
  return (unsigned char)c;
}

int putc(int c, FILE *f) { return fputc(c, f); }

int putchar(int c) { return fputc(c, __stdout); }

int fputs(const char *restrict str, FILE *restrict f) {
  struct sink s;
  stream_sink(&s, f);
  puts_n(&s, str, strlen(str));
  return 0;
}

int puts(const char *str) {
  fputs(str, __stdout);
  putchar('\n');
  return 0;
}

size_t fwrite(const void *restrict p, size_t size, size_t nmemb, FILE *restrict f) {
  struct sink s;
  stream_sink(&s, f);
  if (s.file != 0 && !s.file->write) { s.file->err = 1; return 0; }
  puts_n(&s, (const char *)p, size * nmemb);
  return nmemb;
}

int fflush(FILE *f) { (void)f; return 0; }

/* ---- memory ---- */

void *malloc(size_t n) {
  unsigned long *ctl = CTL;
  unsigned long p = ctl[1];
  unsigned long padding = (0ul - p) & 15ul;
  /* Check alignment, header and payload space before adding, without wrapping. */
  if (p > ctl[2] || padding > ctl[2] - p) return 0;
  p += padding;
  if (ctl[2] - p < 16ul || n > ctl[2] - p - 16ul) return 0;
  *(unsigned long *)p = n;
  ctl[1] = p + 16ul + n;
  return (void *)(p + 16ul);
}

void *calloc(size_t m, size_t n) {
  if (n != 0 && m > (size_t)-1 / n) return 0;
  /* Fresh heap space is zeroed: linear memory starts zeroed and free never reuses it. */
  return malloc(m * n);
}

void free(void *p) { (void)p; }

void *realloc(void *p, size_t n) {
  void *q = malloc(n);
  if (p != 0 && q != 0) {
    size_t old = *(unsigned long *)((char *)p - 16);
    memcpy(q, p, old < n ? old : n);
  }
  return q;
}

void *memcpy(void *restrict d, const void *restrict s, size_t n) {
  char *dd = d;
  const char *ss = s;
  for (size_t i = 0; i < n; i++) dd[i] = ss[i];
  return d;
}

void *memmove(void *d, const void *s, size_t n) {
  char *dd = d;
  const char *ss = s;
  if (dd < ss) for (size_t i = 0; i < n; i++) dd[i] = ss[i];
  else for (size_t i = n; i > 0; i--) dd[i - 1] = ss[i - 1];
  return d;
}

void *memset(void *d, int c, size_t n) {
  unsigned char *dd = d;
  for (size_t i = 0; i < n; i++) dd[i] = (unsigned char)c;
  return d;
}

int memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *x = a, *y = b;
  for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return 0;
}

void *memchr(const void *s, int c, size_t n) {
  const unsigned char *p = s;
  for (size_t i = 0; i < n; i++) if (p[i] == (unsigned char)c) return (void *)(p + i);
  return 0;
}

/* ---- strings ---- */

size_t strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }

int strcmp(const char *a, const char *b) {
  while (*a && *a == *b) { a++; b++; }
  return (unsigned char)*a - (unsigned char)*b;
}

int strncmp(const char *a, const char *b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (a[i] != b[i] || a[i] == 0) return (unsigned char)a[i] - (unsigned char)b[i];
  }
  return 0;
}

char *strcpy(char *restrict d, const char *restrict s) {
  size_t i = 0;
  while ((d[i] = s[i]) != 0) i++;
  return d;
}

char *strncpy(char *restrict d, const char *restrict s, size_t n) {
  size_t i = 0;
  for (; i < n && s[i]; i++) d[i] = s[i];
  for (; i < n; i++) d[i] = 0;
  return d;
}

char *strcat(char *restrict d, const char *restrict s) { strcpy(d + strlen(d), s); return d; }

char *strncat(char *restrict d, const char *restrict s, size_t n) {
  char *e = d + strlen(d);
  size_t i = 0;
  for (; i < n && s[i]; i++) e[i] = s[i];
  e[i] = 0;
  return d;
}

char *strchr(const char *s, int c) {
  for (;; s++) {
    if (*s == (char)c) return (char *)s;
    if (*s == 0) return 0;
  }
}

char *strrchr(const char *s, int c) {
  const char *r = 0;
  for (;; s++) {
    if (*s == (char)c) r = s;
    if (*s == 0) return (char *)r;
  }
}

char *strstr(const char *h, const char *n) {
  size_t k = strlen(n);
  for (; *h; h++) if (strncmp(h, n, k) == 0) return (char *)h;
  if (k == 0) return (char *)h;
  return 0;
}

char *strdup(const char *s) {
  size_t n = strlen(s) + 1;
  char *d = malloc(n);
  if (d) memcpy(d, s, n);
  return d;
}

/* ---- conversions ---- */

int isdigit(int c) { return c >= '0' && c <= '9'; }
int isspace(int c) { return c == ' ' || (c >= '\t' && c <= '\r'); }
int isupper(int c) { return c >= 'A' && c <= 'Z'; }
int islower(int c) { return c >= 'a' && c <= 'z'; }
int isalpha(int c) { return isupper(c) || islower(c); }
int isalnum(int c) { return isalpha(c) || isdigit(c); }
int isxdigit(int c) { return isdigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'); }
int isprint(int c) { return c >= 32 && c < 127; }
int toupper(int c) { return islower(c) ? c - 'a' + 'A' : c; }
int tolower(int c) { return isupper(c) ? c - 'A' + 'a' : c; }

long long strtoll(const char *restrict s, char **restrict end, int base) {
  while (isspace(*s)) s++;
  int neg = 0;
  if (*s == '-' || *s == '+') { neg = *s == '-'; s++; }
  if ((base == 0 || base == 16) && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) { s += 2; base = 16; }
  else if (base == 0 && s[0] == '0') base = 8;
  else if (base == 0) base = 10;
  unsigned long long v = 0;
  for (;; s++) {
    int d;
    if (isdigit(*s)) d = *s - '0';
    else if (islower(*s)) d = *s - 'a' + 10;
    else if (isupper(*s)) d = *s - 'A' + 10;
    else break;
    if (d >= base) break;
    v = v * (unsigned long long)base + (unsigned long long)d;
  }
  if (end) *end = (char *)s;
  return neg ? (long long)(0ull - v) : (long long)v;
}

long strtol(const char *restrict s, char **restrict end, int base) { return (long)strtoll(s, end, base); }
unsigned long strtoul(const char *restrict s, char **restrict end, int base) {
  return (unsigned long)strtoll(s, end, base);
}
unsigned long long strtoull(const char *restrict s, char **restrict end, int base) {
  return (unsigned long long)strtoll(s, end, base);
}
int atoi(const char *s) { return (int)strtoll(s, 0, 10); }
long atol(const char *s) { return (long)strtoll(s, 0, 10); }
long long atoll(const char *s) { return strtoll(s, 0, 10); }

int abs(int j) { return j < 0 ? -j : j; }
long labs(long j) { return j < 0 ? -j : j; }
long long llabs(long long j) { return j < 0 ? -j : j; }

static unsigned long rand_state = 1;
int rand(void) {
  rand_state = rand_state * 1103515245ul + 12345ul;
  return (int)((rand_state >> 16) & 0x7fff);
}
void srand(unsigned int seed) { rand_state = seed; }

void qsort(void *base, size_t n, size_t size, int (*cmp)(const void *, const void *)) {
  char *b = base;
  for (size_t i = 1; i < n; i++) {
    for (size_t j = i; j > 0 && cmp(b + (j - 1) * size, b + j * size) > 0; j--) {
      char *x = b + (j - 1) * size, *y = b + j * size;
      for (size_t k = 0; k < size; k++) { char t = x[k]; x[k] = y[k]; y[k] = t; }
    }
  }
}

/* ---- builtins.h ---- */

int __builtin_ffs(int x) { return __builtin_ffsll((long long)(unsigned)x); }
int __builtin_ffsl(long x) { return __builtin_ffsll(x); }
int __builtin_ffsll(long long x) {
  unsigned long long v = (unsigned long long)x;
  if (v == 0) return 0;
  int n = 1;
  while ((v & 1) == 0) { v >>= 1; n++; }
  return n;
}
int __builtin_ctz(unsigned int x) { return __builtin_ffsll(x) - 1; }
int __builtin_ctzl(unsigned long x) { return __builtin_ffsll((long long)x) - 1; }
int __builtin_ctzll(unsigned long long x) { return __builtin_ffsll((long long)x) - 1; }
__cerbty_uint16_t __builtin_bswap16(__cerbty_uint16_t x) {
  return (__cerbty_uint16_t)((x >> 8) | (x << 8));
}
__cerbty_uint32_t __builtin_bswap32(__cerbty_uint32_t x) {
  return (x >> 24) | ((x >> 8) & 0xff00u) | ((x << 8) & 0xff0000u) | (x << 24);
}
__cerbty_uint64_t __builtin_bswap64(__cerbty_uint64_t x) {
  return ((__cerbty_uint64_t)__builtin_bswap32((__cerbty_uint32_t)x) << 32) |
         __builtin_bswap32((__cerbty_uint32_t)(x >> 32));
}

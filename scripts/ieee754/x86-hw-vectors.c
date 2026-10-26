/*
 * Recompute TestFloat vectors on this host's x86 hardware (SSE/AVX/FMA/F16C, x87).
 *
 * Usage: x86-hw-vectors FUNCTION MODE [exact|notexact] < testfloat-vectors > hw-vectors
 *
 * Reads the operands of each TestFloat 3e line (the expected result and flags are
 * ignored) and writes a line in the same format whose result and flags come from
 * the hardware instruction: MXCSR for SSE/AVX, the x87 status word for x87.
 * Flag byte as in SoftFloat: inexact 1, underflow 2, overflow 4, infinite 8, invalid 16.
 * MODE is a testfloat_gen rounding option; -rnear_maxMag has no x86 encoding.
 *
 * FUNCTION: f32_/f64_ {add sub mul div sqrt mulAdd x86min x86max roundToInt
 *   eq lt le eq_signaling lt_quiet le_quiet to_i32 to_i64}, f32_to_f64, f64_to_f32,
 *   f32_to_f16, f16_to_f32, i32_to_f32, i64_to_f32, i32_to_f64, i64_to_f64,
 *   extF80_ {add sub mul div sqrt rem roundToInt eq lt}.
 * f32_/f64_mulAdd run VFMADD213, VFMADD132 and VFMADD231 on the same a * b + c and
 * exit 3 if any two forms differ in result or flags (NaN priority included).
 * MXCSR is fixed at DAZ = FTZ = 0; the denormal-operand flag DE (bit 1) is not
 * reported, because `Std.Flags` has only the five IEEE flags.
 * Build: cc -O1 -mavx2 -mfma -mf16c -o x86-hw-vectors x86-hw-vectors.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned rc_of(const char *m) {
  if (!strcmp(m, "-rnear_even")) return 0;
  if (!strcmp(m, "-rmin")) return 1;
  if (!strcmp(m, "-rmax")) return 2;
  if (!strcmp(m, "-rminMag")) return 3;
  fprintf(stderr, "unsupported mode %s\n", m);
  exit(2);
}

static unsigned mxcsr_base;
static void set_mxcsr(unsigned v) { __asm__ volatile("ldmxcsr %0" ::"m"(v)); }
static unsigned get_mxcsr(void) { unsigned v; __asm__ volatile("stmxcsr %0" : "=m"(v)); return v; }
static unsigned sse_flags(unsigned m) {
  return ((m & 0x20) ? 1 : 0) | ((m & 0x10) ? 2 : 0) | ((m & 0x08) ? 4 : 0) |
         ((m & 0x04) ? 8 : 0) | ((m & 0x01) ? 16 : 0);
}
static void sse_begin(void) { set_mxcsr(mxcsr_base); }
static unsigned sse_end(void) { return sse_flags(get_mxcsr()); }

typedef struct { uint64_t lo; uint16_t hi; } x80;
static uint16_t x87_cw;
static void x87_begin(void) {
  __asm__ volatile("fnclex");
  __asm__ volatile("fldcw %0" ::"m"(x87_cw));
}
static unsigned x87_end(void) {
  uint16_t sw;
  __asm__ volatile("fnstsw %0" : "=m"(sw));
  return ((sw & 0x20) ? 1 : 0) | ((sw & 0x10) ? 2 : 0) | ((sw & 0x08) ? 4 : 0) |
         ((sw & 0x04) ? 8 : 0) | ((sw & 0x01) ? 16 : 0);
}

static uint64_t hex(const char *s) { return strtoull(s, NULL, 16); }
static x80 hex80(const char *s) {
  char a[5] = {0};
  x80 r;
  memcpy(a, s, 4);
  r.hi = (uint16_t)strtoul(a, NULL, 16);
  r.lo = strtoull(s + 4, NULL, 16);
  return r;
}

#define SSE2(name, insn, T, MOV)                                                           \
  static T name(T a, T b) {                                                                \
    T r;                                                                                   \
    __asm__ volatile(MOV " %1, %%xmm0\n\t" MOV " %2, %%xmm1\n\t" insn " %%xmm1, %%xmm0\n\t" \
                     MOV " %%xmm0, %0"                                                     \
                     : "=m"(r) : "m"(a), "m"(b) : "xmm0", "xmm1");                         \
    return r;                                                                              \
  }
SSE2(addss, "addss", uint32_t, "movd")
SSE2(subss, "subss", uint32_t, "movd")
SSE2(mulss, "mulss", uint32_t, "movd")
SSE2(divss, "divss", uint32_t, "movd")
SSE2(minss, "minss", uint32_t, "movd")
SSE2(maxss, "maxss", uint32_t, "movd")
SSE2(addsd, "addsd", uint64_t, "movq")
SSE2(subsd, "subsd", uint64_t, "movq")
SSE2(mulsd, "mulsd", uint64_t, "movq")
SSE2(divsd, "divsd", uint64_t, "movq")
SSE2(minsd, "minsd", uint64_t, "movq")
SSE2(maxsd, "maxsd", uint64_t, "movq")

#define SSECMP(name, imm, T, MOV, insn)                                                     \
  static unsigned name(T a, T b) {                                                          \
    T r;                                                                                    \
    __asm__ volatile(MOV " %1, %%xmm0\n\t" MOV " %2, %%xmm1\n\t" insn " $" #imm             \
                     ", %%xmm1, %%xmm0, %%xmm0\n\t" MOV " %%xmm0, %0"                       \
                     : "=m"(r) : "m"(a), "m"(b) : "xmm0", "xmm1");                          \
    return r != 0;                                                                          \
  }
/* VCMPSS predicates: 0 EQ_OQ, 0x11 LT_OQ, 0x12 LE_OQ, 0x10 EQ_OS, 1 LT_OS, 2 LE_OS */
SSECMP(cmp32_eq, 0x00, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp32_lt, 0x01, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp32_le, 0x02, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp32_eqs, 0x10, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp32_ltq, 0x11, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp32_leq, 0x12, uint32_t, "vmovd", "vcmpss")
SSECMP(cmp64_eq, 0x00, uint64_t, "vmovq", "vcmpsd")
SSECMP(cmp64_lt, 0x01, uint64_t, "vmovq", "vcmpsd")
SSECMP(cmp64_le, 0x02, uint64_t, "vmovq", "vcmpsd")
SSECMP(cmp64_eqs, 0x10, uint64_t, "vmovq", "vcmpsd")
SSECMP(cmp64_ltq, 0x11, uint64_t, "vmovq", "vcmpsd")
SSECMP(cmp64_leq, 0x12, uint64_t, "vmovq", "vcmpsd")

static uint32_t sqrtss(uint32_t a) {
  uint32_t r;
  __asm__ volatile("movd %1, %%xmm1\n\tsqrtss %%xmm1, %%xmm0\n\tmovd %%xmm0, %0"
                   : "=m"(r) : "m"(a) : "xmm0", "xmm1");
  return r;
}
static uint64_t sqrtsd(uint64_t a) {
  uint64_t r;
  __asm__ volatile("movq %1, %%xmm1\n\tsqrtsd %%xmm1, %%xmm0\n\tmovq %%xmm0, %0"
                   : "=m"(r) : "m"(a) : "xmm0", "xmm1");
  return r;
}
/* a * b + c by VFMADD213SS xmm0, xmm1, xmm2 (xmm0 = xmm1 * xmm0 + xmm2) with
 * xmm1 = a, xmm0 = b, xmm2 = c. Observed NaN priority on an i7-8700: src2 (xmm1),
 * then src1 (xmm0), then src3, i.e. the operand order of the computed expression. */
static uint32_t fmass(uint32_t a, uint32_t b, uint32_t c) {
  uint32_t r;
  __asm__ volatile("vmovd %2, %%xmm0\n\tvmovd %1, %%xmm1\n\tvmovd %3, %%xmm2\n\t"
                   "vfmadd213ss %%xmm2, %%xmm1, %%xmm0\n\tvmovd %%xmm0, %0"
                   : "=m"(r) : "m"(a), "m"(b), "m"(c) : "xmm0", "xmm1", "xmm2");
  return r;
}
static uint64_t fmasd(uint64_t a, uint64_t b, uint64_t c) {
  uint64_t r;
  __asm__ volatile("vmovq %2, %%xmm0\n\tvmovq %1, %%xmm1\n\tvmovq %3, %%xmm2\n\t"
                   "vfmadd213sd %%xmm2, %%xmm1, %%xmm0\n\tvmovq %%xmm0, %0"
                   : "=m"(r) : "m"(a), "m"(b), "m"(c) : "xmm0", "xmm1", "xmm2");
  return r;
}
/* The same a * b + c by the other two FMA forms, used to check that all three
 * encodings agree bit for bit and flag for flag (in particular on NaN priority,
 * which follows the operand order of the expression a * b + c in every form).
 * VFMADD132SS xmm0, xmm1, xmm2: xmm0 = xmm0 * xmm2 + xmm1 (xmm0 = a, xmm2 = b, xmm1 = c).
 * VFMADD231SS xmm0, xmm1, xmm2: xmm0 = xmm1 * xmm2 + xmm0 (xmm1 = a, xmm2 = b, xmm0 = c). */
#define FMAFORM(name, T, MOV, insn, ra, rb, rc)                                            \
  static T name(T a, T b, T c) {                                                           \
    T r;                                                                                   \
    __asm__ volatile(MOV " %1, %%" ra "\n\t" MOV " %2, %%" rb "\n\t" MOV " %3, %%" rc "\n\t" \
                     insn " %%xmm2, %%xmm1, %%xmm0\n\t" MOV " %%xmm0, %0"                  \
                     : "=m"(r) : "m"(a), "m"(b), "m"(c) : "xmm0", "xmm1", "xmm2");         \
    return r;                                                                              \
  }
FMAFORM(fmass132, uint32_t, "vmovd", "vfmadd132ss", "xmm0", "xmm2", "xmm1")
FMAFORM(fmass231, uint32_t, "vmovd", "vfmadd231ss", "xmm1", "xmm2", "xmm0")
FMAFORM(fmasd132, uint64_t, "vmovq", "vfmadd132sd", "xmm0", "xmm2", "xmm1")
FMAFORM(fmasd231, uint64_t, "vmovq", "vfmadd231sd", "xmm1", "xmm2", "xmm0")
static unsigned long form_mismatches;
/* ROUNDSS imm: bit 3 suppresses precision (inexact); bits 0-1 the direction (bit 2 = 0). */
#define ROUNDS(name, insn, T, MOV, imm)                                                    \
  static T name(T a) {                                                                     \
    T r;                                                                                   \
    __asm__ volatile(MOV " %1, %%xmm1\n\t" insn " $" #imm ", %%xmm1, %%xmm0\n\t" MOV       \
                     " %%xmm0, %0" : "=m"(r) : "m"(a) : "xmm0", "xmm1");                   \
    return r;                                                                              \
  }
ROUNDS(rss0, "roundss", uint32_t, "movd", 0) ROUNDS(rss1, "roundss", uint32_t, "movd", 1)
ROUNDS(rss2, "roundss", uint32_t, "movd", 2) ROUNDS(rss3, "roundss", uint32_t, "movd", 3)
ROUNDS(rss8, "roundss", uint32_t, "movd", 8) ROUNDS(rss9, "roundss", uint32_t, "movd", 9)
ROUNDS(rss10, "roundss", uint32_t, "movd", 10) ROUNDS(rss11, "roundss", uint32_t, "movd", 11)
ROUNDS(rsd0, "roundsd", uint64_t, "movq", 0) ROUNDS(rsd1, "roundsd", uint64_t, "movq", 1)
ROUNDS(rsd2, "roundsd", uint64_t, "movq", 2) ROUNDS(rsd3, "roundsd", uint64_t, "movq", 3)
ROUNDS(rsd8, "roundsd", uint64_t, "movq", 8) ROUNDS(rsd9, "roundsd", uint64_t, "movq", 9)
ROUNDS(rsd10, "roundsd", uint64_t, "movq", 10) ROUNDS(rsd11, "roundsd", uint64_t, "movq", 11)

static uint64_t cvtss2sd(uint32_t a) {
  uint64_t r;
  __asm__ volatile("movd %1, %%xmm1\n\tcvtss2sd %%xmm1, %%xmm0\n\tmovq %%xmm0, %0"
                   : "=m"(r) : "m"(a) : "xmm0", "xmm1");
  return r;
}
static uint32_t cvtsd2ss(uint64_t a) {
  uint32_t r;
  __asm__ volatile("movq %1, %%xmm1\n\tcvtsd2ss %%xmm1, %%xmm0\n\tmovd %%xmm0, %0"
                   : "=m"(r) : "m"(a) : "xmm0", "xmm1");
  return r;
}
/* F16C: VCVTPS2PH imm 4 uses MXCSR.RC; VCVTPH2PS is exact */
static uint16_t cvtps2ph(uint32_t a) {
  uint32_t r;
  __asm__ volatile("vmovd %1, %%xmm1\n\tvcvtps2ph $4, %%xmm1, %%xmm0\n\tvmovd %%xmm0, %0"
                   : "=m"(r) : "m"(a) : "xmm0", "xmm1");
  return (uint16_t)r;
}
static uint32_t cvtph2ps(uint16_t a) {
  uint32_t r, in = a;
  __asm__ volatile("vmovd %1, %%xmm1\n\tvcvtph2ps %%xmm1, %%xmm0\n\tvmovd %%xmm0, %0"
                   : "=m"(r) : "m"(in) : "xmm0", "xmm1");
  return r;
}
static uint64_t cvtss2si64(uint32_t a, int trunc) {
  uint64_t r;
  if (trunc)
    __asm__ volatile("movd %1, %%xmm1\n\tcvttss2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  else
    __asm__ volatile("movd %1, %%xmm1\n\tcvtss2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  return r;
}
static uint32_t cvtss2si32(uint32_t a, int trunc) {
  uint32_t r;
  if (trunc)
    __asm__ volatile("movd %1, %%xmm1\n\tcvttss2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  else
    __asm__ volatile("movd %1, %%xmm1\n\tcvtss2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  return r;
}
static uint64_t cvtsd2si64(uint64_t a, int trunc) {
  uint64_t r;
  if (trunc)
    __asm__ volatile("movq %1, %%xmm1\n\tcvttsd2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  else
    __asm__ volatile("movq %1, %%xmm1\n\tcvtsd2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  return r;
}
static uint32_t cvtsd2si32(uint64_t a, int trunc) {
  uint32_t r;
  if (trunc)
    __asm__ volatile("movq %1, %%xmm1\n\tcvttsd2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  else
    __asm__ volatile("movq %1, %%xmm1\n\tcvtsd2si %%xmm1, %0" : "=r"(r) : "m"(a) : "xmm1");
  return r;
}
static uint32_t cvtsi2ss32(uint32_t a) {
  uint32_t r;
  __asm__ volatile("cvtsi2ssl %1, %%xmm0\n\tmovd %%xmm0, %0" : "=m"(r) : "m"(a) : "xmm0");
  return r;
}
static uint32_t cvtsi2ss64(uint64_t a) {
  uint32_t r;
  __asm__ volatile("cvtsi2ssq %1, %%xmm0\n\tmovd %%xmm0, %0" : "=m"(r) : "m"(a) : "xmm0");
  return r;
}
static uint64_t cvtsi2sd32(uint32_t a) {
  uint64_t r;
  __asm__ volatile("cvtsi2sdl %1, %%xmm0\n\tmovq %%xmm0, %0" : "=m"(r) : "m"(a) : "xmm0");
  return r;
}
static uint64_t cvtsi2sd64(uint64_t a) {
  uint64_t r;
  __asm__ volatile("cvtsi2sdq %1, %%xmm0\n\tmovq %%xmm0, %0" : "=m"(r) : "m"(a) : "xmm0");
  return r;
}

/* x87 on 80-bit operands */
#define X87BIN(name, insn)                                                                 \
  static x80 name(x80 a, x80 b) {                                                          \
    x80 r;                                                                                 \
    __asm__ volatile("fldt %2\n\tfldt %1\n\t" insn "\n\tfstpt %0"                          \
                     : "=m"(r) : "m"(a), "m"(b) : "st", "st(1)");                          \
    return r;                                                                              \
  }
/* st(0) = a, st(1) = b; f*rp: st(1) = st(0) op st(1) reversed accordingly */
X87BIN(x87add, "faddp")
X87BIN(x87mul, "fmulp")
X87BIN(x87sub, "fsubp") /* GNU as: AT&T fsubp is Intel FSUBRP: st(1) = st(0) - st(1) = a - b */
X87BIN(x87div, "fdivp") /* GNU as: AT&T fdivp is Intel FDIVRP: st(1) = st(0) / st(1) = a / b */
static x80 x87sqrt(x80 a) {
  x80 r;
  __asm__ volatile("fldt %1\n\tfsqrt\n\tfstpt %0" : "=m"(r) : "m"(a) : "st");
  return r;
}
static x80 x87rndint(x80 a) {
  x80 r;
  __asm__ volatile("fldt %1\n\tfrndint\n\tfstpt %0" : "=m"(r) : "m"(a) : "st");
  return r;
}
/* IEEE remainder: FPREM1 until C2 = 0. st(0) = a, st(1) = b. */
static x80 x87rem(x80 a, x80 b) {
  x80 r;
  __asm__ volatile("fldt %2\n\tfldt %1\n"
                   "1:\n\tfprem1\n\tfnstsw %%ax\n\ttestw $0x400, %%ax\n\tjnz 1b\n\t"
                   "fstpt %0\n\tfstp %%st(0)"
                   : "=m"(r) : "m"(a), "m"(b) : "ax", "st", "st(1)");
  return r;
}
/* FUCOMI (quiet) / FCOMI (signaling): returns ZF, PF, CF */
static unsigned x87cmp(x80 a, x80 b, int signaling) {
  unsigned char zf, pf, cf;
  if (signaling)
    __asm__ volatile("fldt %4\n\tfldt %3\n\tfcomip %%st(1), %%st\n\tfstp %%st(0)\n\t"
                     "setz %0\n\tsetp %1\n\tsetc %2"
                     : "=r"(zf), "=r"(pf), "=r"(cf) : "m"(a), "m"(b) : "st", "st(1)", "cc");
  else
    __asm__ volatile("fldt %4\n\tfldt %3\n\tfucomip %%st(1), %%st\n\tfstp %%st(0)\n\t"
                     "setz %0\n\tsetp %1\n\tsetc %2"
                     : "=r"(zf), "=r"(pf), "=r"(cf) : "m"(a), "m"(b) : "st", "st(1)", "cc");
  if (pf) return 3;         /* unordered */
  if (zf) return 0;         /* equal */
  return cf ? 1 : 2;        /* less : greater */
}

static void put80(x80 v) { printf("%04X%016llX", v.hi, (unsigned long long)v.lo); }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: FUNCTION MODE [exact]\n"); return 2; }
  const char *fn = argv[1];
  unsigned rc = rc_of(argv[2]);
  int exact = argc > 3 && !strcmp(argv[3], "exact");
  mxcsr_base = 0x1F80 | (rc << 13); /* all exceptions masked, flags clear, DAZ/FTZ off */
  x87_cw = (uint16_t)(0x037F | (rc << 10)); /* masked, 64-bit precision */
  char line[256];
  while (fgets(line, sizeof line, stdin)) {
    char *tok[6];
    int n = 0;
    for (char *t = strtok(line, " \n"); t && n < 6; t = strtok(NULL, " \n")) tok[n++] = t;
    if (n < 3) continue;
    unsigned fl = 0;
#define B32(op) do { uint32_t a = hex(tok[0]), b = hex(tok[1]); sse_begin(); uint32_t z = op(a, b); \
    fl = sse_end(); printf("%08X %08X %08X %02X\n", a, b, z, fl); } while (0)
#define B64(op) do { uint64_t a = hex(tok[0]), b = hex(tok[1]); sse_begin(); uint64_t z = op(a, b); \
    fl = sse_end(); printf("%016llX %016llX %016llX %02X\n", (unsigned long long)a, \
    (unsigned long long)b, (unsigned long long)z, fl); } while (0)
#define C32(op) do { uint32_t a = hex(tok[0]), b = hex(tok[1]); sse_begin(); unsigned z = op(a, b); \
    fl = sse_end(); printf("%08X %08X %u %02X\n", a, b, z, fl); } while (0)
#define C64(op) do { uint64_t a = hex(tok[0]), b = hex(tok[1]); sse_begin(); unsigned z = op(a, b); \
    fl = sse_end(); printf("%016llX %016llX %u %02X\n", (unsigned long long)a, \
    (unsigned long long)b, z, fl); } while (0)
    if (!strcmp(fn, "f32_add")) B32(addss);
    else if (!strcmp(fn, "f32_sub")) B32(subss);
    else if (!strcmp(fn, "f32_mul")) B32(mulss);
    else if (!strcmp(fn, "f32_div")) B32(divss);
    else if (!strcmp(fn, "f32_x86min")) B32(minss);
    else if (!strcmp(fn, "f32_x86max")) B32(maxss);
    else if (!strcmp(fn, "f64_add")) B64(addsd);
    else if (!strcmp(fn, "f64_sub")) B64(subsd);
    else if (!strcmp(fn, "f64_mul")) B64(mulsd);
    else if (!strcmp(fn, "f64_div")) B64(divsd);
    else if (!strcmp(fn, "f64_x86min")) B64(minsd);
    else if (!strcmp(fn, "f64_x86max")) B64(maxsd);
    else if (!strcmp(fn, "f32_eq")) C32(cmp32_eq);
    else if (!strcmp(fn, "f32_lt")) C32(cmp32_lt);
    else if (!strcmp(fn, "f32_le")) C32(cmp32_le);
    else if (!strcmp(fn, "f32_eq_signaling")) C32(cmp32_eqs);
    else if (!strcmp(fn, "f32_lt_quiet")) C32(cmp32_ltq);
    else if (!strcmp(fn, "f32_le_quiet")) C32(cmp32_leq);
    else if (!strcmp(fn, "f64_eq")) C64(cmp64_eq);
    else if (!strcmp(fn, "f64_lt")) C64(cmp64_lt);
    else if (!strcmp(fn, "f64_le")) C64(cmp64_le);
    else if (!strcmp(fn, "f64_eq_signaling")) C64(cmp64_eqs);
    else if (!strcmp(fn, "f64_lt_quiet")) C64(cmp64_ltq);
    else if (!strcmp(fn, "f64_le_quiet")) C64(cmp64_leq);
    else if (!strcmp(fn, "f32_mulAdd") && n >= 5) {
      uint32_t a = hex(tok[0]), b = hex(tok[1]), c = hex(tok[2]);
      sse_begin(); uint32_t z = fmass(a, b, c); fl = sse_end();
      sse_begin(); uint32_t z1 = fmass132(a, b, c); unsigned f1 = sse_end();
      sse_begin(); uint32_t z2 = fmass231(a, b, c); unsigned f2 = sse_end();
      if (z1 != z || z2 != z || f1 != fl || f2 != fl) {
        form_mismatches++;
        fprintf(stderr, "FMA FORM MISMATCH %08X %08X %08X: 213 %08X/%02X 132 %08X/%02X 231 %08X/%02X\n",
                a, b, c, z, fl, z1, f1, z2, f2);
      }
      printf("%08X %08X %08X %08X %02X\n", a, b, c, z, fl);
    } else if (!strcmp(fn, "f64_mulAdd") && n >= 5) {
      uint64_t a = hex(tok[0]), b = hex(tok[1]), c = hex(tok[2]);
      sse_begin(); uint64_t z = fmasd(a, b, c); fl = sse_end();
      sse_begin(); uint64_t z1 = fmasd132(a, b, c); unsigned f1 = sse_end();
      sse_begin(); uint64_t z2 = fmasd231(a, b, c); unsigned f2 = sse_end();
      if (z1 != z || z2 != z || f1 != fl || f2 != fl) {
        form_mismatches++;
        fprintf(stderr, "FMA FORM MISMATCH %016llX %016llX %016llX\n", (unsigned long long)a,
                (unsigned long long)b, (unsigned long long)c);
      }
      printf("%016llX %016llX %016llX %016llX %02X\n", (unsigned long long)a,
             (unsigned long long)b, (unsigned long long)c, (unsigned long long)z, fl);
    } else if (!strcmp(fn, "f32_sqrt")) {
      uint32_t a = hex(tok[0]); sse_begin(); uint32_t z = sqrtss(a); fl = sse_end();
      printf("%08X %08X %02X\n", a, z, fl);
    } else if (!strcmp(fn, "f64_sqrt")) {
      uint64_t a = hex(tok[0]); sse_begin(); uint64_t z = sqrtsd(a); fl = sse_end();
      printf("%016llX %016llX %02X\n", (unsigned long long)a, (unsigned long long)z, fl);
    } else if (!strcmp(fn, "f32_roundToInt")) {
      uint32_t a = hex(tok[0]), z; sse_begin();
      unsigned k = rc + (exact ? 0 : 8);
      /* ROUNDSS direction bits: 0 nearest, 1 down, 2 up, 3 truncate = MXCSR.RC order */
      switch (k) { case 0: z = rss0(a); break; case 1: z = rss1(a); break; case 2: z = rss2(a); break;
        case 3: z = rss3(a); break; case 8: z = rss8(a); break; case 9: z = rss9(a); break;
        case 10: z = rss10(a); break; default: z = rss11(a); }
      fl = sse_end(); printf("%08X %08X %02X\n", a, z, fl);
    } else if (!strcmp(fn, "f64_roundToInt")) {
      uint64_t a = hex(tok[0]), z; sse_begin();
      unsigned k = rc + (exact ? 0 : 8);
      switch (k) { case 0: z = rsd0(a); break; case 1: z = rsd1(a); break; case 2: z = rsd2(a); break;
        case 3: z = rsd3(a); break; case 8: z = rsd8(a); break; case 9: z = rsd9(a); break;
        case 10: z = rsd10(a); break; default: z = rsd11(a); }
      fl = sse_end(); printf("%016llX %016llX %02X\n", (unsigned long long)a, (unsigned long long)z, fl);
    } else if (!strcmp(fn, "f32_to_f64")) {
      uint32_t a = hex(tok[0]); sse_begin(); uint64_t z = cvtss2sd(a); fl = sse_end();
      printf("%08X %016llX %02X\n", a, (unsigned long long)z, fl);
    } else if (!strcmp(fn, "f64_to_f32")) {
      uint64_t a = hex(tok[0]); sse_begin(); uint32_t z = cvtsd2ss(a); fl = sse_end();
      printf("%016llX %08X %02X\n", (unsigned long long)a, z, fl);
    } else if (!strcmp(fn, "f32_to_f16")) {
      uint32_t a = hex(tok[0]); sse_begin(); uint16_t z = cvtps2ph(a); fl = sse_end();
      printf("%08X %04X %02X\n", a, z, fl);
    } else if (!strcmp(fn, "f16_to_f32")) {
      uint16_t a = (uint16_t)hex(tok[0]); sse_begin(); uint32_t z = cvtph2ps(a); fl = sse_end();
      printf("%04X %08X %02X\n", a, z, fl);
    } else if (!strcmp(fn, "f32_to_i32") || !strcmp(fn, "f32_to_i64") ||
               !strcmp(fn, "f64_to_i32") || !strcmp(fn, "f64_to_i64")) {
      /* CVTT* truncates; CVT* uses MXCSR.RC. Both raise inexact (IEEE "exact" variant). */
      int trunc = rc == 3, d = fn[1] == '6', w64 = fn[8] == '6';
      uint64_t a = hex(tok[0]);
      sse_begin();
      uint64_t z = d ? (w64 ? cvtsd2si64(a, trunc) : cvtsd2si32(a, trunc))
                     : (w64 ? cvtss2si64((uint32_t)a, trunc) : cvtss2si32((uint32_t)a, trunc));
      fl = sse_end();
      if (d) printf("%016llX ", (unsigned long long)a); else printf("%08X ", (uint32_t)a);
      if (w64) printf("%016llX %02X\n", (unsigned long long)z, fl);
      else printf("%08X %02X\n", (uint32_t)z, fl);
    } else if (!strcmp(fn, "i32_to_f32")) {
      uint32_t a = hex(tok[0]); sse_begin(); uint32_t z = cvtsi2ss32(a); fl = sse_end();
      printf("%08X %08X %02X\n", a, z, fl);
    } else if (!strcmp(fn, "i64_to_f32")) {
      uint64_t a = hex(tok[0]); sse_begin(); uint32_t z = cvtsi2ss64(a); fl = sse_end();
      printf("%016llX %08X %02X\n", (unsigned long long)a, z, fl);
    } else if (!strcmp(fn, "i32_to_f64")) {
      uint32_t a = hex(tok[0]); sse_begin(); uint64_t z = cvtsi2sd32(a); fl = sse_end();
      printf("%08X %016llX %02X\n", a, (unsigned long long)z, fl);
    } else if (!strcmp(fn, "i64_to_f64")) {
      uint64_t a = hex(tok[0]); sse_begin(); uint64_t z = cvtsi2sd64(a); fl = sse_end();
      printf("%016llX %016llX %02X\n", (unsigned long long)a, (unsigned long long)z, fl);
    } else if (!strncmp(fn, "extF80_", 7)) {
      const char *op = fn + 7;
      x80 a = hex80(tok[0]), z;
      if (!strcmp(op, "sqrt") || !strcmp(op, "roundToInt")) {
        x87_begin(); z = op[0] == 's' ? x87sqrt(a) : x87rndint(a); fl = x87_end();
        put80(a); printf(" "); put80(z); printf(" %02X\n", fl);
      } else if (!strcmp(op, "eq") || !strcmp(op, "lt")) {
        x80 b = hex80(tok[1]);
        x87_begin(); unsigned c = x87cmp(a, b, op[0] == 'l'); fl = x87_end();
        unsigned r = op[0] == 'e' ? (c == 0) : (c == 1);
        put80(a); printf(" "); put80(b); printf(" %u %02X\n", r, fl);
      } else {
        x80 b = hex80(tok[1]);
        x87_begin();
        if (!strcmp(op, "add")) z = x87add(a, b);
        else if (!strcmp(op, "sub")) z = x87sub(a, b);
        else if (!strcmp(op, "mul")) z = x87mul(a, b);
        else if (!strcmp(op, "div")) z = x87div(a, b);
        else z = x87rem(a, b);
        fl = x87_end();
        put80(a); printf(" "); put80(b); printf(" "); put80(z); printf(" %02X\n", fl);
      }
    } else { fprintf(stderr, "unsupported function %s\n", fn); return 2; }
  }
  if (form_mismatches) {
    fprintf(stderr, "%lu vectors where VFMADD132/213/231 disagree\n", form_mismatches);
    return 3;
  }
  return 0;
}

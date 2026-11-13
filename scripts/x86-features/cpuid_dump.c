/* Dump the CPUID leaves and XCR0 that Features.FeatureSet.ofCpuid reads.
   Output: one line per (leaf, subleaf): "leaf subleaf eax ebx ecx edx" in hex,
   then "xcr0 <hex>" (0 when OSXSAVE is clear), then "gcc <features>": the
   features libgcc's __builtin_cpu_supports reports, as an independent check. */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>

static void dump(uint32_t leaf, uint32_t sub) {
  uint32_t a, b, c, d;
  __cpuid_count(leaf, sub, a, b, c, d);
  printf("%08x %08x %08x %08x %08x %08x\n", leaf, sub, a, b, c, d);
}

int main(void) {
  uint32_t a, b, c, d;
  dump(0, 0);
  dump(1, 0);
  dump(7, 0);
  dump(0x80000000u, 0);
  dump(0x80000001u, 0);
  __cpuid_count(1, 0, a, b, c, d);
  uint64_t xcr0 = 0;
  if (c & (1u << 27)) {
    uint32_t lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    xcr0 = ((uint64_t)hi << 32) | lo;
  }
  printf("xcr0 %016llx\n", (unsigned long long)xcr0);
  /* An independent oracle: libgcc's own CPUID/XGETBV feature detection. */
  __builtin_cpu_init();
  printf("gcc");
  if (__builtin_cpu_supports("sse")) printf(" sse");
  if (__builtin_cpu_supports("sse2")) printf(" sse2");
  if (__builtin_cpu_supports("sse3")) printf(" sse3");
  if (__builtin_cpu_supports("ssse3")) printf(" ssse3");
  if (__builtin_cpu_supports("sse4.1")) printf(" sse4.1");
  if (__builtin_cpu_supports("sse4.2")) printf(" sse4.2");
  if (__builtin_cpu_supports("popcnt")) printf(" popcnt");
  if (__builtin_cpu_supports("lzcnt")) printf(" lzcnt");
  if (__builtin_cpu_supports("bmi")) printf(" bmi");
  if (__builtin_cpu_supports("bmi2")) printf(" bmi2");
  if (__builtin_cpu_supports("adx")) printf(" adx");
  if (__builtin_cpu_supports("movbe")) printf(" movbe");
  if (__builtin_cpu_supports("rdrnd")) printf(" rdrnd");
  if (__builtin_cpu_supports("rdseed")) printf(" rdseed");
  if (__builtin_cpu_supports("aes")) printf(" aes");
  if (__builtin_cpu_supports("pclmul")) printf(" pclmul");
  if (__builtin_cpu_supports("sha")) printf(" sha");
  if (__builtin_cpu_supports("gfni")) printf(" gfni");
  if (__builtin_cpu_supports("avx")) printf(" avx");
  if (__builtin_cpu_supports("avx2")) printf(" avx2");
  if (__builtin_cpu_supports("fma")) printf(" fma");
  if (__builtin_cpu_supports("f16c")) printf(" f16c");
  if (__builtin_cpu_supports("vaes")) printf(" vaes");
  if (__builtin_cpu_supports("vpclmulqdq")) printf(" vpclmulqdq");
  if (__builtin_cpu_supports("avx512f")) printf(" avx512f");
  if (__builtin_cpu_supports("avx512cd")) printf(" avx512cd");
  if (__builtin_cpu_supports("avx512bw")) printf(" avx512bw");
  if (__builtin_cpu_supports("avx512dq")) printf(" avx512dq");
  if (__builtin_cpu_supports("avx512vl")) printf(" avx512vl");
  if (__builtin_cpu_supports("avx512ifma")) printf(" avx512ifma");
  if (__builtin_cpu_supports("avx512vbmi")) printf(" avx512vbmi");
  if (__builtin_cpu_supports("avx512vbmi2")) printf(" avx512vbmi2");
  if (__builtin_cpu_supports("avx512vnni")) printf(" avx512vnni");
  if (__builtin_cpu_supports("avx512bitalg")) printf(" avx512bitalg");
  if (__builtin_cpu_supports("avx512vpopcntdq")) printf(" avx512vpopcntdq");
  printf("\n");
  return 0;
}

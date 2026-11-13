/* A tiny freestanding C file compiled to wasm32 with clang (see build-wasm.sh).
 *
 * Every export is a total function on 32-bit integers: arithmetic is done on uint32_t, so it
 * wraps and has no undefined behaviour, and there are no divisions by zero, no memory traffic
 * and no calls. */
#include <stdint.h>

#define EXPORT(name) __attribute__((export_name(#name)))

/* Wrapping 32-bit addition. */
EXPORT(add) int32_t add(int32_t a, int32_t b) {
  return (int32_t)((uint32_t)a + (uint32_t)b);
}

/* Wrapping 32-bit multiplication. */
EXPORT(mul) int32_t mul(int32_t a, int32_t b) {
  return (int32_t)((uint32_t)a * (uint32_t)b);
}

/* Signed maximum. */
EXPORT(max) int32_t max(int32_t a, int32_t b) {
  return a < b ? b : a;
}

/* 2a + 1, wrapping: always odd. */
EXPORT(odd) int32_t odd(int32_t a) {
  return (int32_t)((uint32_t)a * 2u + 1u);
}

/* Number of set bits, by Kernighan's loop: clear the lowest set bit until none is left. */
EXPORT(popcount) int32_t popcount(uint32_t x) {
  int32_t n = 0;
  while (x != 0) {
    x &= x - 1u;
    n++;
  }
  return n;
}

/* Greatest common divisor of two unsigned 32-bit integers, by Euclid's algorithm.
 * gcd(0, 0) = 0. The remainder is only taken with a non-zero divisor. */
EXPORT(gcd) uint32_t gcd(uint32_t a, uint32_t b) {
  while (b != 0) {
    uint32_t t = a % b;
    a = b;
    b = t;
  }
  return a;
}

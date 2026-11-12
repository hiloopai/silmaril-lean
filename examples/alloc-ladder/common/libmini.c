/* libmini: the memory/string library TU every rung links.  It is rung 02's
   verification subject; other rungs consume it only through its contracts.

   Contracts (separation-logic style, informal; Lean statements pending):
     memcpy(d,s,n) : {d |-> _[n] * s |-> bs[n]} memcpy {ret = d. d |-> bs * s |-> bs}
                     (d and s disjoint; restrict)
     memmove(d,s,n): {d..d+n, s..s+n may overlap} result d[0..n) = old s[0..n)
     memset(d,c,n) : {d |-> _[n]} {d |-> replicate n (u8)c}
     memcmp(a,b,n) : read-only; sign of first differing byte (unsigned), else 0
     strlen(s)     : {s |-> cstr bs} {ret = |bs|}, read-only

   The loops are written byte-at-a-time on purpose: the target IR is
   "map/fold over a byte range", and -fno-tree-loop-distribute-patterns
   (see flags.sh) stops GCC from turning these loops back into calls to
   themselves. */
#include "rt.h"

void *memcpy(void *restrict d, const void *restrict s, usize n) {
  u8 *dp = d;
  const u8 *sp = s;
  for (usize i = 0; i < n; i++) dp[i] = sp[i];
  return d;
}

void *memmove(void *d, const void *s, usize n) {
  u8 *dp = d;
  const u8 *sp = s;
  if (dp == sp || n == 0) return d;
  if ((usize)(dp - sp) >= n) {          /* forward copy is safe */
    for (usize i = 0; i < n; i++) dp[i] = sp[i];
  } else {
    for (usize i = n; i-- > 0;) dp[i] = sp[i];
  }
  return d;
}

void *memset(void *d, int c, usize n) {
  u8 *dp = d;
  for (usize i = 0; i < n; i++) dp[i] = (u8)c;
  return d;
}

int memcmp(const void *a, const void *b, usize n) {
  const u8 *x = a, *y = b;
  for (usize i = 0; i < n; i++)
    if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return 0;
}

usize strlen(const char *s) {
  const char *p = s;
  while (*p) p++;
  return (usize)(p - s);
}

/* Rung 02 driver: exhaustive small-size/alignment tests of common/libmini.c
   (memcpy, memmove, memset, memcmp, strlen).  The subject TU is
   ../common/libmini.c; this rung verifies it, all later rungs reuse its
   contracts. */
#include "rt.h"

static u8 a[96], b[96], ref[96];

static void fill(u8 *p, usize n, u32 seed) {
  for (usize i = 0; i < n; i++) { seed = seed * 1103515245u + 12345u; p[i] = (u8)(seed >> 16); }
}

int cmain(long *sp) {
  for (usize off = 0; off < 8; off++)
    for (usize n = 0; n <= 40; n++) {
      fill(a, sizeof a, (u32)(n * 31 + off)); fill(b, sizeof b, 7);
      for (usize i = 0; i < sizeof b; i++) ref[i] = b[i];
      for (usize i = 0; i < n; i++) ref[off + i] = a[i];
      rt_check(memcpy(b + off, a, n) == b + off, "memcpy ret");
      int same = 1;
      for (usize i = 0; i < sizeof b; i++) same &= b[i] == ref[i];
      rt_check(same, "memcpy frame");
      rt_check(memcmp(b + off, a, n) == 0, "memcmp eq");
      if (n) { b[off + n - 1] ^= 0x80; rt_check(memcmp(b + off, a, n) != 0, "memcmp ne"); }
      /* overlapping memmove both directions */
      for (int dir = 0; dir < 2; dir++) {
        fill(a, sizeof a, (u32)n);
        for (usize i = 0; i < sizeof a; i++) ref[i] = a[i];
        usize s = dir ? off : 16, d = dir ? 16 : off;
        u8 tmp[64];
        for (usize i = 0; i < n; i++) tmp[i] = ref[s + i];
        for (usize i = 0; i < n; i++) ref[d + i] = tmp[i];
        memmove(a + d, a + s, n);
        int ok = 1;
        for (usize i = 0; i < sizeof a; i++) ok &= a[i] == ref[i];
        rt_check(ok, "memmove overlap");
      }
      memset(b, 0xaa, sizeof b);
      memset(b + off, (int)(0x100 + n), n);
      int ok = 1;
      for (usize i = 0; i < sizeof b; i++) ok &= b[i] == ((i >= off && i < off + n) ? (u8)n : 0xaa);
      rt_check(ok, "memset");
      for (usize i = 0; i < n; i++) b[off + i] = (u8)('a' + i % 26);
      b[off + n] = 0;
      rt_check(strlen((char *)b + off) == n, "strlen");
    }
  rt_check(memcmp("abc", "abd", 3) < 0 && memcmp("\xff", "\x01", 1) > 0, "memcmp unsigned");
  return rt_finish("02-mem-loops");
}

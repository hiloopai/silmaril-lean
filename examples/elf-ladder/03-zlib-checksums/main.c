/* Rung 03 driver: zlib 1.3.1 adler32.c and crc32.c, compiled verbatim with
   -DZ_SOLO (no libc), checked against published vectors, a bytewise
   reference CRC and the combine laws. */
#include "rt.h"
typedef unsigned long uLong;
typedef unsigned int uInt;
/* Under Z_SOLO zconf.h never defines Z_U4, so z_crc_t is `unsigned long`
   (8-byte table entries) and the W-braided code paths are compiled out. */
uLong adler32(uLong adler, const u8 *buf, uInt len);
uLong adler32_combine(uLong a1, uLong a2, long len2);
uLong crc32(uLong crc, const u8 *buf, uInt len);
uLong crc32_combine(uLong c1, uLong c2, long len2);
#ifndef Z_U4
typedef unsigned long crc_entry;
#else
typedef Z_U4 crc_entry;   /* braided build: -DZ_U4=unsigned -DZ_U8='unsigned long' */
#endif
const crc_entry *get_crc_table(void);

static u32 ref_crc(u32 c, const u8 *p, usize n) {
  c = ~c;
  for (usize i = 0; i < n; i++) { c ^= p[i]; for (int k = 0; k < 8; k++) c = (c >> 1) ^ (0xedb88320u & -(c & 1)); }
  return ~c;
}
static u32 ref_adler(u32 a, const u8 *p, usize n) {
  u32 s1 = a & 0xffff, s2 = a >> 16;
  for (usize i = 0; i < n; i++) { s1 = (s1 + p[i]) % 65521; s2 = (s2 + s1) % 65521; }
  return s2 << 16 | s1;
}

static u8 big[20000];

int cmain(long *sp) {
  const u8 *nine = (const u8 *)"123456789";
  rt_check(crc32(0, nine, 9) == 0xcbf43926u, "crc32 check value");
  rt_check(adler32(1, (const u8 *)"Wikipedia", 9) == 0x11e60398u, "adler32 Wikipedia");
  rt_check(crc32(0, 0, 0) == 0 && adler32(0, 0, 0) == 1, "null buffer init");
  u32 s = 1;
  for (usize i = 0; i < sizeof big; i++) { s = s * 69069u + 1; big[i] = (u8)(s >> 24); }
  /* adler32's NMAX=5552 inner unrolled loop and DO16 path; crc32's tail path */
  static const usize lens[] = {0, 1, 15, 16, 17, 255, 5551, 5552, 5553, 11104, 20000};
  for (unsigned i = 0; i < sizeof lens / sizeof lens[0]; i++) {
    usize n = lens[i];
    rt_check(adler32(1, big, (uInt)n) == ref_adler(1, big, n), "adler32 vs ref");
    rt_check(crc32(0, big, (uInt)n) == ref_crc(0, big, n), "crc32 vs ref");
    usize h = n / 3;
    rt_check(adler32_combine(adler32(1, big, (uInt)h), adler32(1, big + h, (uInt)(n - h)), (long)(n - h))
             == adler32(1, big, (uInt)n), "adler32_combine");
    rt_check(crc32_combine(crc32(0, big, (uInt)h), crc32(0, big + h, (uInt)(n - h)), (long)(n - h))
             == crc32(0, big, (uInt)n), "crc32_combine");
  }
  rt_check(get_crc_table()[1] == 0x77073096u, "crc table[1]");
  rt_puts("crc32(123456789)="); rt_put_hex((u32)crc32(0, nine, 9)); rt_puts("\n");
  return rt_finish("03-zlib-checksums");
}

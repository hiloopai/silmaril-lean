/* crc32: read stdin to end of file, then print its CRC-32 (IEEE 802.3: reflected polynomial
   0xEDB88320, initial value and final xor 0xFFFFFFFF) as 8 lower-case hex digits and a
   newline; exit 0, or 1 if a read or write fails (Silmaril/Compile/Examples/LPS/Crc32.lean). */
#include <unistd.h>

static unsigned char buf[4096];

int main(void) {
  unsigned int crc = 0xFFFFFFFFu;
  for (;;) {
    ssize_t n = read(0, buf, sizeof buf);
    if (n == 0) break;
    if (n < 0) return 1;
    for (ssize_t i = 0; i < n; i++) {
      crc ^= buf[i];
      for (int k = 0; k < 8; k++) crc = (crc >> 1) ^ (0xEDB88320u & (0u - (crc & 1u)));
    }
  }
  crc ^= 0xFFFFFFFFu;
  char out[9];
  for (int i = 0; i < 8; i++) out[i] = "0123456789abcdef"[(crc >> (28 - 4 * i)) & 15];
  out[8] = '\n';
  const char *p = out;
  size_t left = sizeof out;
  while (left > 0) {
    ssize_t w = write(1, p, left);
    if (w <= 0) return 1;
    p += w;
    left -= (size_t)w;
  }
  return 0;
}

/* wc: read stdin to end of file, then print "<lines> <words> <bytes>\n" in decimal (words
   are maximal runs of bytes other than space, \t, \n, \v, \f, \r); exit 0, or 1 if a read
   or write fails (Silmaril/Compile/Examples/LPS/Wc.lean). */
#include <unistd.h>

static char buf[4096];

static int is_space(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r';
}

static int put_all(const char *p, size_t n) {
  while (n > 0) {
    ssize_t w = write(1, p, n);
    if (w <= 0) return 1;
    p += w;
    n -= (size_t)w;
  }
  return 0;
}

static size_t put_dec(char *out, unsigned long v) {
  char tmp[24];
  size_t k = 0, i = 0;
  do { tmp[k++] = (char)('0' + v % 10); v /= 10; } while (v);
  while (k) out[i++] = tmp[--k];
  return i;
}

int main(void) {
  unsigned long lines = 0, words = 0, bytes = 0;
  int in_word = 0;
  for (;;) {
    ssize_t n = read(0, buf, sizeof buf);
    if (n == 0) break;
    if (n < 0) return 1;
    for (ssize_t i = 0; i < n; i++) {
      char c = buf[i];
      bytes++;
      if (c == '\n') lines++;
      if (is_space(c)) in_word = 0;
      else if (!in_word) { in_word = 1; words++; }
    }
  }
  char out[80];
  size_t len = put_dec(out, lines);
  out[len++] = ' ';
  len += put_dec(out + len, words);
  out[len++] = ' ';
  len += put_dec(out + len, bytes);
  out[len++] = '\n';
  return put_all(out, len);
}

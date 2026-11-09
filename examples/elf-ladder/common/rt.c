/* Freestanding runtime TU: syscall wrappers and the self-test reporter. */
#include "rt.h"

static int failures;

isize rt_write(int fd, const void *buf, usize n) {
  const u8 *p = buf;
  usize done = 0;
  while (done < n) {
    long r = sc3(1, fd, (long)(p + done), (long)(n - done));
    if (r == -4) continue;            /* EINTR */
    if (r <= 0) return r < 0 ? r : -5;
    done += (usize)r;
  }
  return (isize)done;
}

isize rt_read(int fd, void *buf, usize n) {
  long r;
  do r = sc3(0, fd, (long)buf, (long)n); while (r == -4);
  return r;
}

void rt_puts(const char *s) { rt_write(1, s, strlen(s)); }

void rt_put_hex(u32 v) {
  char b[8];
  for (int i = 7; i >= 0; i--) { b[i] = "0123456789abcdef"[v & 15]; v >>= 4; }
  rt_write(1, b, 8);
}

void rt_check(int ok, const char *what) {
  if (ok) return;
  failures++;
  rt_write(2, "FAIL ", 5);
  rt_write(2, what, strlen(what));
  rt_write(2, "\n", 1);
}

int rt_failures(void) { return failures; }

int rt_finish(const char *rung) {
  if (failures) { rt_puts("FAILED "); rt_puts(rung); rt_puts("\n"); return 1; }
  rt_puts("ok "); rt_puts(rung); rt_puts("\n");
  return 0;
}

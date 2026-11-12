/* Minimal freestanding runtime interface shared by the ladder rungs.
   Contracts (informal; the Lean statements are pending):
     sc3        : raw Linux syscall; the only `syscall` instruction.
     rt_write   : writes all n bytes of buf to fd or returns <0.
     rt_read    : one read(2); returns bytes read (0 = EOF) or <0.
     rt_puts    : rt_write of a NUL-terminated string.
     rt_put_hex : writes exactly 8 lowercase hex digits of v.
     rt_check   : if !ok, writes "FAIL <what>\n" and records a failure.
   Memory functions live in libmini.c (rung 02's subject). */
#ifndef ELF_LADDER_RT_H
#define ELF_LADDER_RT_H
typedef unsigned char      u8;
typedef unsigned short     u16;
typedef unsigned int       u32;
typedef unsigned long long u64;
typedef unsigned long      usize;
typedef long               isize;

long sc3(long nr, long a0, long a1, long a2);
isize rt_write(int fd, const void *buf, usize n);
isize rt_read(int fd, void *buf, usize n);
void rt_puts(const char *s);
void rt_put_hex(u32 v);
void rt_check(int ok, const char *what);
int rt_failures(void);
int rt_finish(const char *rung); /* prints "ok <rung>\n" or "FAILED <rung>\n"; returns exit status */

void *memcpy(void *restrict d, const void *restrict s, usize n);
void *memset(void *d, int c, usize n);
void *memmove(void *d, const void *s, usize n);
int memcmp(const void *a, const void *b, usize n);
usize strlen(const char *s);
#endif

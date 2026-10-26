/* sha256sum-min: a libc-free re-implementation of GNU coreutils 9.4
   `sha256sum`, for formal verification of the compiled x86-64 binary.

   Target behaviour: byte-for-byte GNU coreutils 9.4 sha256sum on GNU/Linux
   (O_BINARY == 0) in the C/POSIX locale -- stdout, stderr and exit status --
   for every option the 9.4 binary accepts: -b -c -t -w -z, --binary --check
   --ignore-missing --quiet --status --strict --tag --text --warn --zero
   --help --version, GNU getopt_long permutation and abbreviation (and
   POSIXLY_CORRECT), `--`, `-` as standard input, file-name escaping, both
   checksum-line formats, and the close_stdout write-error protocol.

   The SHA-256 compression function is NOT compiled from this file: it is the
   459-byte clang 18.1.3 -O2 `sha256_compress` image that Silmaril's pilot
   proof is about, linked from compress_clang_O2.S (or, in the all-gcc
   variant, xc_sha256.c's sha256_compress compiled by gcc).

   The structure of check mode, option validation and quoting is a close port
   of coreutils-9.4 src/digest.c, gnulib lib/quotearg.c, lib/closeout.c,
   lib/close-stream.c and glibc 2.39 posix/getopt.c, so that the spec can be
   read off either. Deliberate scope limits are listed in binary.md.

   System calls: read, write, openat, close, brk, exit_group (and getpid +
   kill only for argc == 0). All go through sc3 in start.S. */

#include <stddef.h>
#include <stdint.h>

#include "gen_tables.h"

/* ---------------------------------------------------------------- kernel */

long sc3(long nr, long a0, long a1, long a2);
void sha256_compress(uint32_t state[8], const uint8_t block[64]);

enum { SYS_read = 0, SYS_write = 1, SYS_close = 3, SYS_brk = 12,
       SYS_getpid = 39, SYS_kill = 62, SYS_exit_group = 231,
       SYS_openat = 257 };
enum { AT_FDCWD = -100, O_RDONLY = 0, SIGABRT = 6 };
enum { ENOENT = 2, EBADF = 9 };

static long sys_read(int fd, void *b, size_t n) { return sc3(SYS_read, fd, (long)b, (long)n); }
static long sys_write(int fd, const void *b, size_t n) { return sc3(SYS_write, fd, (long)b, (long)n); }
static long sys_close(int fd) { return sc3(SYS_close, fd, 0, 0); }
static long sys_open(const char *p) { return sc3(SYS_openat, AT_FDCWD, (long)p, O_RDONLY); }
static __attribute__((noreturn)) void sys_exit(int st)
{
  for (;;)
    sc3(SYS_exit_group, st, 0, 0);
}

/* gcc may emit calls to these even when freestanding. */
void *memcpy(void *d, const void *s, size_t n)
{
  unsigned char *dd = d;
  const unsigned char *ss = s;
  while (n--)
    *dd++ = *ss++;
  return d;
}
void *memset(void *d, int c, size_t n)
{
  unsigned char *dd = d;
  while (n--)
    *dd++ = (unsigned char)c;
  return d;
}

static size_t c_strlen(const char *s)
{
  size_t n = 0;
  while (s[n])
    n++;
  return n;
}
static int c_streq(const char *a, const char *b)
{
  while (*a && *a == *b)
    a++, b++;
  return *a == *b;
}
/* strncmp (a, b, n) == 0 */
static int c_strneq(const char *a, const char *b, size_t n)
{
  for (size_t i = 0; i < n; i++)
    {
      if (a[i] != b[i])
        return 0;
      if (!a[i])
        return 1;
    }
  return 1;
}
static int c_isxdigit(unsigned char c)
{
  return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}
static int c_tolower(unsigned char c) { return c >= 'A' && c <= 'Z' ? c + 32 : c; }
static int c_isprint(unsigned char c) { return c >= 0x20 && c < 0x7f; }

/* ---------------------------------------------------------------- heap */

static char *heap_cur, *heap_end;
static __attribute__((noreturn)) void xalloc_die(void);

static void *xmalloc(size_t n)
{
  n = (n + 15) & ~(size_t)15;
  if (!heap_end)
    heap_cur = heap_end = (char *)sc3(SYS_brk, 0, 0, 0);
  if ((size_t)(heap_end - heap_cur) < n)
    {
      size_t grow = n < (1u << 20) ? (1u << 20) : n;
      char *want = heap_end + grow;
      if (want < heap_end)
        xalloc_die();
      char *got = (char *)sc3(SYS_brk, (long)want, 0, 0);
      if (got < want)
        xalloc_die();
      heap_end = got;
    }
  void *p = heap_cur;
  heap_cur += n;
  return p;
}

/* A growable byte buffer (reused, never freed). */
struct buf { char *p; size_t len, cap; };
static void buf_reserve(struct buf *b, size_t need)
{
  if (need <= b->cap)
    return;
  size_t cap = b->cap ? b->cap : 128;
  while (cap < need)
    {
      if (cap > ((size_t)-1) / 2)
        xalloc_die();
      cap *= 2;
    }
  char *np = xmalloc(cap);
  memcpy(np, b->p, b->len);
  b->p = np;
  b->cap = cap;
}
static void buf_put(struct buf *b, char c)
{
  buf_reserve(b, b->len + 1);
  b->p[b->len++] = c;
}
static void buf_puts(struct buf *b, const char *s)
{
  while (*s)
    buf_put(b, *s++);
}

/* ---------------------------------------------------------------- stdio */

/* stdout: glibc line-buffered FILE (setvbuf _IOLBF), BUFSIZ-style 4096-byte
   buffer, discarded on a failed flush, sticky error flag. */
static char obuf[4096];
static size_t olen;
static int out_error;
/* stderr: unbuffered; sticky error flag only. */
static int err_error;

static int write_all(int fd, const char *p, size_t n)
{
  while (n)
    {
      long r = sys_write(fd, p, n);
      if (r < 0)
        return (int)-r;
      p += r;
      n -= (size_t)r;
    }
  return 0;
}

/* fflush (stdout): 0 or errno. */
static int out_flush(void)
{
  if (!olen)
    return 0;
  int e = write_all(1, obuf, olen);
  olen = 0;
  if (e)
    out_error = 1;
  return e;
}
static void out_putc(char c)
{
  if (olen == sizeof obuf)
    out_flush();
  obuf[olen++] = c;
  if (c == '\n')
    out_flush();
}
static void out_puts(const char *s)
{
  while (*s)
    out_putc(*s++);
}

static void err_write(const char *p, size_t n)
{
  if (write_all(2, p, n))
    err_error = 1;
}

static char *program_name;   /* program_name == program_invocation_name */
static char *getopt_argv0;   /* glibc getopt reports with argv[0] itself */

static void u64_dec(struct buf *b, uint64_t v)
{
  char t[21];
  int i = 0;
  do
    t[i++] = (char)('0' + v % 10);
  while (v /= 10);
  while (i)
    buf_put(b, t[--i]);
}

static const char *c_strerror(int e, struct buf *scratch)
{
  if (e > 0 && e < 134 && errtab[e])
    return errtab[e];
  scratch->len = 0;
  buf_puts(scratch, "Unknown error ");
  if (e < 0)
    {
      buf_put(scratch, '-');
      u64_dec(scratch, (uint64_t)-(int64_t)e);
    }
  else
    u64_dec(scratch, (uint64_t)e);
  buf_put(scratch, 0);
  return scratch->p;
}

/* glibc error (status, errnum, "%s", msg) with the message prebuilt. */
static struct buf ebuf, escratch;
static void close_stdout(void);
static void error_msg(int status, int errnum, const char *msg)
{
  out_flush();
  ebuf.len = 0;
  buf_puts(&ebuf, program_name);
  buf_puts(&ebuf, ": ");
  buf_puts(&ebuf, msg);
  if (errnum)
    {
      buf_puts(&ebuf, ": ");
      buf_puts(&ebuf, c_strerror(errnum, &escratch));
    }
  buf_put(&ebuf, '\n');
  err_write(ebuf.p, ebuf.len);
  if (status)
    {
      close_stdout();
      sys_exit(status);
    }
}

/* ---------------------------------------------------------------- quotef */

/* gnulib quotearg_buffer_restyled for the styles reachable from
   quotef (shell_escape_quoting_style with ':' in quote_these_too) in a
   unibyte (C) locale, with argsize == SIZE_MAX.  */
enum qstyle { Q_SHELL_ESCAPE, Q_SHELL_ESCAPE_ALWAYS, Q_SHELL_ALWAYS, Q_C };
static struct buf qbuf;

/* A literal port: the locals that gnulib does not reset at process_input
   (backslash_escapes, pending_shell_escape_end, encountered_single_quote,
   all_c_and_shell_quote_compat) are not reset here either. `len` counts
   STOREs; in the read-only scan (gnulib's buffersize == 0) nothing is kept. */
static void quote_restyled(const char *arg, enum qstyle style, int elide, int colon)
{
  size_t start = qbuf.len, len = 0;
  int scan_only = 0, scanned = 0;
  int backslash_escapes = 0, pending = 0, enc_sq = 0, all_compat = 1;
  const char *quote_string = 0;

#define STORE(ch) do { if (!scan_only) buf_put(&qbuf, (char)(ch)); len++; } while (0)
#define START_ESC() do { if (elide) goto force; escaping = 1; \
    if (style == Q_SHELL_ALWAYS && !pending) { STORE('\''); STORE('$'); STORE('\''); pending = 1; } \
    STORE('\\'); } while (0)
#define END_ESC() do { if (pending && !escaping) { STORE('\''); STORE('\''); pending = 0; } } while (0)

process_input:
  switch (style)
    {
    case Q_C:
      if (!elide)
        STORE('"');
      backslash_escapes = 1;
      quote_string = "\"";
      break;
    case Q_SHELL_ESCAPE:
      backslash_escapes = 1;
      elide = 1;
      /* fall through */
    case Q_SHELL_ESCAPE_ALWAYS:
      if (!elide)
        backslash_escapes = 1;
      /* fall through */
    case Q_SHELL_ALWAYS:
      style = Q_SHELL_ALWAYS;
      if (!elide)
        STORE('\'');
      quote_string = "'";
      break;
    }

  for (size_t i = 0; arg[i]; i++)
    {
      unsigned char c, esc = 0;
      int is_right_quote = 0, escaping = 0, compat = 0;

      if (backslash_escapes && style != Q_SHELL_ALWAYS && quote_string
          && arg[i] == quote_string[0])
        {
          if (elide)
            goto force;
          is_right_quote = 1;
        }
      c = (unsigned char)arg[i];
      switch (c)
        {
        case '?':
          if (style == Q_SHELL_ALWAYS && elide)
            goto force;
          break;
        case '\a': esc = 'a'; goto c_escape;
        case '\b': esc = 'b'; goto c_escape;
        case '\f': esc = 'f'; goto c_escape;
        case '\n': esc = 'n'; goto c_and_shell_escape;
        case '\r': esc = 'r'; goto c_and_shell_escape;
        case '\t': esc = 't'; goto c_and_shell_escape;
        case '\v': esc = 'v'; goto c_escape;
        case '\\':
          esc = c;
          if (style == Q_SHELL_ALWAYS)
            {
              if (elide)
                goto force;
              goto store_c;
            }
          if (backslash_escapes && elide && quote_string)
            goto store_c;
        c_and_shell_escape:
          if (style == Q_SHELL_ALWAYS && elide)
            goto force;
        c_escape:
          if (backslash_escapes)
            {
              c = esc;
              goto store_escape;
            }
          break;
        case '{': case '}':
          if (arg[1] != '\0')
            break;
          /* fall through */
        case '#': case '~':
          if (i != 0)
            break;
          /* fall through */
        case ' ':
          compat = 1;
          /* fall through */
        case '!': case '"': case '$': case '&': case '(': case ')': case '*':
        case ';': case '<': case '=': case '>': case '[': case '^': case '`':
        case '|':
          if (style == Q_SHELL_ALWAYS && elide)
            goto force;
          break;
        case '\'':
          enc_sq = 1;
          compat = 1;
          if (style == Q_SHELL_ALWAYS)
            {
              if (elide)
                goto force;
              if (!scanned && !scan_only)
                scan_only = 1;
              STORE('\'');
              STORE('\\');
              STORE('\'');
              pending = 0;
            }
          break;
        case '%': case '+': case ',': case '-': case '.': case '/':
        case '0': case '1': case '2': case '3': case '4': case '5':
        case '6': case '7': case '8': case '9': case ':':
        case 'A': case 'B': case 'C': case 'D': case 'E': case 'F':
        case 'G': case 'H': case 'I': case 'J': case 'K': case 'L':
        case 'M': case 'N': case 'O': case 'P': case 'Q': case 'R':
        case 'S': case 'T': case 'U': case 'V': case 'W': case 'X':
        case 'Y': case 'Z': case ']': case '_': case 'a': case 'b':
        case 'c': case 'd': case 'e': case 'f': case 'g': case 'h':
        case 'i': case 'j': case 'k': case 'l': case 'm': case 'n':
        case 'o': case 'p': case 'q': case 'r': case 's': case 't':
        case 'u': case 'v': case 'w': case 'x': case 'y': case 'z':
          compat = 1;
          break;
        default:
          {
            /* unibyte locale: m == 1 */
            int printable = c_isprint(c);
            compat = printable;
            if (backslash_escapes && !printable)
              {
                START_ESC();
                STORE('0' + (c >> 6));
                STORE('0' + ((c >> 3) & 7));
                c = (unsigned char)('0' + (c & 7));
                goto store_c;
              }
          }
          break;
        }

      if (!(((backslash_escapes && style != Q_SHELL_ALWAYS) || elide)
            && colon && c == ':')
          && !is_right_quote)
        goto store_c;

    store_escape:
      START_ESC();

    store_c:
      END_ESC();
      STORE(c);
      if (!compat)
        all_compat = 0;
    }

  if (len == 0 && style == Q_SHELL_ALWAYS && elide)
    goto force;

  if (style == Q_SHELL_ALWAYS && !elide && enc_sq)
    {
      if (all_compat)
        {
          qbuf.len = start;
          quote_restyled(arg, Q_C, 0, colon);
          return;
        }
      else if (scan_only)
        {
          scan_only = 0;
          scanned = 1;
          qbuf.len = start;
          len = 0;
          goto process_input;
        }
    }

  if (quote_string && !elide)
    for (const char *q = quote_string; *q; q++)
      STORE(*q);
  return;

force:
  qbuf.len = start;
  if (style == Q_SHELL_ALWAYS && backslash_escapes)
    style = Q_SHELL_ESCAPE_ALWAYS;
  quote_restyled(arg, style, 0, 0);
#undef STORE
#undef START_ESC
#undef END_ESC
}

/* quotef (s): result valid until the next call. */
static const char *quotef(const char *s)
{
  qbuf.len = 0;
  quote_restyled(s, Q_SHELL_ESCAPE, 1, 1);
  buf_put(&qbuf, 0);
  return qbuf.p;
}

/* ---------------------------------------------------------------- exit */

static void close_stdout(void)
{
  /* gnulib close_stream (stdout) */
  int some_pending = olen != 0;
  int prev_fail = out_error;
  int fe = 0, fclose_fail = 0;
  if (olen)
    {
      fe = out_flush();
      if (fe)
        fclose_fail = 1;
    }
  long r = sys_close(1);
  if (r < 0)
    {
      fclose_fail = 1;
      fe = (int)-r;
    }
  if (prev_fail || (fclose_fail && (some_pending || fe != EBADF)))
    {
      if (!fclose_fail)
        fe = 0;
      error_msg(0, fe, "write error");
      sys_exit(1);
    }
  /* close_stream (stderr) */
  r = sys_close(2);
  if (err_error || (r < 0 && -r != EBADF))
    sys_exit(1);
}

static __attribute__((noreturn)) void do_exit(int status)
{
  close_stdout();
  sys_exit(status);
}

static __attribute__((noreturn)) void xalloc_die(void)
{
  error_msg(1, 0, "memory exhausted");
  sys_exit(1);
}

static __attribute__((noreturn)) void usage(int status)
{
  if (status != 0)
    {
      ebuf.len = 0;
      buf_puts(&ebuf, "Try '");
      buf_puts(&ebuf, program_name);
      buf_puts(&ebuf, " --help' for more information.\n");
      err_write(ebuf.p, ebuf.len);
    }
  else
    {
      out_puts(help_pre);
      out_puts(program_name);
      out_puts(help_post);
    }
  do_exit(status);
}

/* ---------------------------------------------------------------- SHA-256 */

struct sha { uint32_t h[8]; uint8_t blk[64]; size_t blen; uint64_t total; };

static void sha_init(struct sha *s)
{
  static const uint32_t H0[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };
  for (int i = 0; i < 8; i++)
    s->h[i] = H0[i];
  s->blen = 0;
  s->total = 0;
}
static void sha_update(struct sha *s, const uint8_t *p, size_t n)
{
  s->total += n;
  while (n)
    {
      if (s->blen == 0 && n >= 64)
        {
          sha256_compress(s->h, p);
          p += 64;
          n -= 64;
          continue;
        }
      size_t k = 64 - s->blen;
      if (k > n)
        k = n;
      memcpy(s->blk + s->blen, p, k);
      s->blen += k;
      p += k;
      n -= k;
      if (s->blen == 64)
        {
          sha256_compress(s->h, s->blk);
          s->blen = 0;
        }
    }
}
static void sha_final(struct sha *s, uint8_t out[32])
{
  uint64_t bits = s->total << 3;
  s->blk[s->blen++] = 0x80;
  if (s->blen > 56)
    {
      memset(s->blk + s->blen, 0, 64 - s->blen);
      sha256_compress(s->h, s->blk);
      s->blen = 0;
    }
  memset(s->blk + s->blen, 0, 56 - s->blen);
  for (int i = 0; i < 8; i++)
    s->blk[56 + i] = (uint8_t)(bits >> (56 - 8 * i));
  sha256_compress(s->h, s->blk);
  for (int i = 0; i < 8; i++)
    {
      out[4 * i] = (uint8_t)(s->h[i] >> 24);
      out[4 * i + 1] = (uint8_t)(s->h[i] >> 16);
      out[4 * i + 2] = (uint8_t)(s->h[i] >> 8);
      out[4 * i + 3] = (uint8_t)s->h[i];
    }
}

static uint8_t iobuf[32768];

/* Hash fd to EOF: 0 or errno. */
static int digest_fd(int fd, uint8_t out[32])
{
  struct sha s;
  sha_init(&s);
  for (;;)
    {
      long r = sys_read(fd, iobuf, sizeof iobuf);
      if (r < 0)
        return (int)-r;
      if (r == 0)
        break;
      sha_update(&s, iobuf, (size_t)r);
    }
  sha_final(&s, out);
  return 0;
}

/* ---------------------------------------------------------------- state */

static int status_only, warn, quiet, strict, ignore_missing, have_read_stdin;
static int bsd_reversed = -1;
static char digest_delim = '\n';
#define DIGEST_HEX_BYTES 64
#define MIN_DIGEST_LINE_LENGTH (DIGEST_HEX_BYTES + 1 + 1)

static int problematic_chars(const char *s)
{
  for (; *s; s++)
    if (*s == '\\' || *s == '\n' || *s == '\r')
      return 1;
  return 0;
}

#define ISWHITE(c) ((c) == ' ' || (c) == '\t')

static char *filename_unescape(char *s, size_t s_len)
{
  char *dst = s;
  for (size_t i = 0; i < s_len; i++)
    {
      switch (s[i])
        {
        case '\\':
          if (i == s_len - 1)
            return 0;
          ++i;
          switch (s[i])
            {
            case 'n': *dst++ = '\n'; break;
            case 'r': *dst++ = '\r'; break;
            case '\\': *dst++ = '\\'; break;
            default: return 0;
            }
          break;
        case '\0':
          return 0;
        default:
          *dst++ = s[i];
          break;
        }
    }
  if (dst < s + s_len)
    *dst = '\0';
  return s;
}

static int valid_digits(const unsigned char *s, size_t len)
{
  if (len != DIGEST_HEX_BYTES)
    return 0;
  for (size_t i = 0; i < DIGEST_HEX_BYTES; i++)
    {
      if (!c_isxdigit(*s))
        return 0;
      ++s;
    }
  return *s == '\0';
}

static int bsd_split_3(char *s, size_t s_len, unsigned char **digest, size_t *d_len,
                       char **file_name, int escaped_filename)
{
  if (s_len == 0)
    return 0;
  size_t i = s_len - 1;
  while (i && s[i] != ')')
    i--;
  if (s[i] != ')')
    return 0;
  *file_name = s;
  if (escaped_filename && filename_unescape(s, i) == 0)
    return 0;
  s[i++] = '\0';
  while (ISWHITE(s[i]))
    i++;
  if (s[i] != '=')
    return 0;
  i++;
  while (ISWHITE(s[i]))
    i++;
  *digest = (unsigned char *)&s[i];
  *d_len = s_len - i;
  return valid_digits(*digest, *d_len);
}

static int split_3(char *s, size_t s_len, unsigned char **digest, size_t *d_len,
                   int *binary, char **file_name)
{
  int escaped_filename = 0;
  size_t i = 0;
  while (ISWHITE(s[i]))
    ++i;
  if (s[i] == '\\')
    {
      ++i;
      escaped_filename = 1;
    }
  if (c_strneq(s + i, "SHA256", 6))
    {
      i += 6;
      if (s[i] == ' ')
        ++i;
      if (s[i] == '(')
        {
          ++i;
          *binary = 0;
          return bsd_split_3(s + i, s_len - i, digest, d_len, file_name, escaped_filename);
        }
      return 0;
    }
  if (s_len - i < MIN_DIGEST_LINE_LENGTH + (s[i] == '\\'))
    return 0;
  *digest = (unsigned char *)&s[i];
  while (s[i] && !ISWHITE(s[i]))
    i++;
  if (i == s_len)
    return 0;
  *d_len = (size_t)(&s[i] - (char *)*digest);
  s[i++] = '\0';
  if (!valid_digits(*digest, *d_len))
    return 0;
  if ((s_len - i == 1) || (s[i] != ' ' && s[i] != '*'))
    {
      if (bsd_reversed == 0)
        return 0;
      bsd_reversed = 1;
    }
  else if (bsd_reversed != 1)
    {
      bsd_reversed = 0;
      *binary = (s[i++] == '*');
    }
  *file_name = &s[i];
  if (escaped_filename)
    return filename_unescape(&s[i], s_len - i) != 0;
  return 1;
}

static void print_filename(const char *file, int escape)
{
  if (!escape)
    {
      out_puts(file);
      return;
    }
  for (; *file; file++)
    switch (*file)
      {
      case '\n': out_puts("\\n"); break;
      case '\r': out_puts("\\r"); break;
      case '\\': out_puts("\\\\"); break;
      default: out_putc(*file); break;
      }
}

static const char hexd[] = "0123456789abcdef";

static void output_file(const char *file, int binary_file, const uint8_t *digest,
                        int tagged, char delim)
{
  int needs_escape = delim == '\n' && problematic_chars(file);
  if (needs_escape)
    out_putc('\\');
  if (tagged)
    {
      out_puts("SHA256 (");
      print_filename(file, needs_escape);
      out_puts(") = ");
    }
  for (int i = 0; i < 32; i++)
    {
      out_putc(hexd[digest[i] >> 4]);
      out_putc(hexd[digest[i] & 0xf]);
    }
  if (!tagged)
    {
      out_putc(' ');
      out_putc(binary_file ? '*' : ' ');
      print_filename(file, needs_escape);
    }
  out_putc(delim);
}

static int hex_equal(const unsigned char *hex, const uint8_t *bin)
{
  size_t cnt;
  for (cnt = 0; cnt < 32; ++cnt)
    if (c_tolower(hex[2 * cnt]) != hexd[bin[cnt] >> 4]
        || c_tolower(hex[2 * cnt + 1]) != hexd[bin[cnt] & 0xf])
      break;
  return cnt == 32;
}

/* fopen + DIGEST_STREAM + fclose of digest_file. */
static int digest_file(const char *filename, uint8_t *bin, int *missing)
{
  int is_stdin = c_streq(filename, "-");
  int fd, err;
  *missing = 0;
  if (is_stdin)
    {
      have_read_stdin = 1;
      fd = 0;
    }
  else
    {
      long r = sys_open(filename);
      if (r < 0)
        {
          if (ignore_missing && -r == ENOENT)
            {
              *missing = 1;
              return 1;
            }
          error_msg(0, (int)-r, quotef(filename));
          return 0;
        }
      fd = (int)r;
    }
  err = digest_fd(fd, bin);
  if (!is_stdin)
    {
      long r = sys_close(fd);
      if (r < 0 && !err)
        err = (int)-r;
    }
  if (err)
    {
      error_msg(0, err, quotef(filename));
      return 0;
    }
  return 1;
}

/* A getline reader over one descriptor (glibc getdelim semantics: a partial
   last line is returned; EOF and error flags are sticky). */
struct reader { int fd, eof, err; size_t pos, len; char b[4096]; };
static struct reader rd;
static struct buf line;

static int rd_fill(struct reader *r)
{
  if (r->eof || r->err)
    return 0;
  long n = sys_read(r->fd, r->b, sizeof r->b);
  if (n < 0)
    {
      r->err = (int)-n;
      return 0;
    }
  if (n == 0)
    {
      r->eof = 1;
      return 0;
    }
  r->pos = 0;
  r->len = (size_t)n;
  return 1;
}

/* Returns the line length (with '\n'), or -1. line.p is NUL-terminated. */
static long rd_getline(struct reader *r)
{
  line.len = 0;
  if (r->pos == r->len && !rd_fill(r))
    return -1;
  for (;;)
    {
      while (r->pos < r->len)
        {
          char c = r->b[r->pos++];
          buf_put(&line, c);
          if (c == '\n')
            goto done;
        }
      if (!rd_fill(r))
        break;
    }
done:
  buf_reserve(&line, line.len + 1);
  line.p[line.len] = '\0';
  return (long)line.len;
}

static struct buf nbuf;
static void warn_count(uint64_t n, const char *one, const char *many)
{
  nbuf.len = 0;
  buf_puts(&nbuf, "WARNING: ");
  u64_dec(&nbuf, n);
  buf_puts(&nbuf, n == 1 ? one : many);
  buf_put(&nbuf, 0);
  error_msg(0, 0, nbuf.p);
}

static int digest_check(const char *checkfile_name)
{
  uint64_t n_misformatted = 0, n_mismatched = 0, n_failures = 0;
  int properly_formatted = 0, matched = 0;
  uint8_t bin[32];
  uint64_t line_number = 0;
  int is_stdin = c_streq(checkfile_name, "-");

  rd.eof = rd.err = 0;
  rd.pos = rd.len = 0;
  if (is_stdin)
    {
      have_read_stdin = 1;
      checkfile_name = "standard input";
      rd.fd = 0;
    }
  else
    {
      long r = sys_open(checkfile_name);
      if (r < 0)
        {
          error_msg(0, (int)-r, quotef(checkfile_name));
          return 0;
        }
      rd.fd = (int)r;
    }

  do
    {
      char *filename;
      int binary;
      unsigned char *digest;
      long line_length;

      ++line_number;
      if (line_number == 0)
        {
          nbuf.len = 0;
          buf_puts(&nbuf, quotef(checkfile_name));
          buf_puts(&nbuf, ": too many checksum lines");
          buf_put(&nbuf, 0);
          error_msg(1, 0, nbuf.p);
        }
      line_length = rd_getline(&rd);
      if (line_length <= 0)
        break;
      char *l = line.p;
      if (l[0] == '#')
        continue;
      line_length -= l[line_length - 1] == '\n';
      line_length -= l[line_length - (0 < line_length)] == '\r';
      if (line_length == 0)
        continue;
      l[line_length] = '\0';

      size_t d_len;
      if (!(split_3(l, (size_t)line_length, &digest, &d_len, &binary, &filename)
            && !(is_stdin && c_streq(filename, "-"))))
        {
          ++n_misformatted;
          if (warn)
            {
              nbuf.len = 0;
              buf_puts(&nbuf, quotef(checkfile_name));
              buf_puts(&nbuf, ": ");
              u64_dec(&nbuf, line_number);
              buf_puts(&nbuf, ": improperly formatted SHA256 checksum line");
              buf_put(&nbuf, 0);
              error_msg(0, 0, nbuf.p);
            }
        }
      else
        {
          int ok, missing;
          int needs_escape = !status_only && problematic_chars(filename);
          properly_formatted = 1;
          ok = digest_file(filename, bin, &missing);
          if (!ok)
            {
              ++n_failures;
              if (!status_only)
                {
                  if (needs_escape)
                    out_putc('\\');
                  print_filename(filename, needs_escape);
                  out_puts(": FAILED open or read\n");
                }
            }
          else if (ignore_missing && missing)
            ;
          else
            {
              int match = d_len == DIGEST_HEX_BYTES && hex_equal(digest, bin);
              if (match)
                matched = 1;
              else
                ++n_mismatched;
              if (!status_only)
                {
                  if (!match || !quiet)
                    {
                      if (needs_escape)
                        out_putc('\\');
                      print_filename(filename, needs_escape);
                    }
                  if (!match)
                    out_puts(": FAILED\n");
                  else if (!quiet)
                    out_puts(": OK\n");
                }
            }
        }
    }
  while (!rd.eof && !rd.err);

  int err = rd.err ? 0 : -1;
  if (!is_stdin)
    {
      long r = sys_close(rd.fd);
      if (r < 0 && err < 0)
        err = (int)-r;
    }
  if (0 <= err)
    {
      if (err)
        error_msg(0, err, quotef(checkfile_name));
      else
        {
          nbuf.len = 0;
          buf_puts(&nbuf, quotef(checkfile_name));
          buf_puts(&nbuf, ": read error");
          buf_put(&nbuf, 0);
          error_msg(0, 0, nbuf.p);
        }
      return 0;
    }

  if (!properly_formatted)
    {
      nbuf.len = 0;
      buf_puts(&nbuf, quotef(checkfile_name));
      buf_puts(&nbuf, ": no properly formatted checksum lines found");
      buf_put(&nbuf, 0);
      error_msg(0, 0, nbuf.p);
    }
  else if (!status_only)
    {
      if (n_misformatted)
        warn_count(n_misformatted, " line is improperly formatted",
                   " lines are improperly formatted");
      if (n_failures)
        warn_count(n_failures, " listed file could not be read",
                   " listed files could not be read");
      if (n_mismatched)
        warn_count(n_mismatched, " computed checksum did NOT match",
                   " computed checksums did NOT match");
      if (ignore_missing && !matched)
        {
          nbuf.len = 0;
          buf_puts(&nbuf, quotef(checkfile_name));
          buf_puts(&nbuf, ": no file was verified");
          buf_put(&nbuf, 0);
          error_msg(0, 0, nbuf.p);
        }
    }
  return properly_formatted && matched && n_mismatched == 0 && n_failures == 0
         && (!strict || n_misformatted == 0);
}

/* ---------------------------------------------------------------- getopt */

enum { IGNORE_MISSING_OPTION = 256, STATUS_OPTION, QUIET_OPTION, STRICT_OPTION,
       TAG_OPTION, HELP_OPTION, VERSION_OPTION };
struct lopt { const char *name; int val; };
static const struct lopt long_options[] = {
  { "check", 'c' }, { "ignore-missing", IGNORE_MISSING_OPTION },
  { "quiet", QUIET_OPTION }, { "status", STATUS_OPTION }, { "warn", 'w' },
  { "strict", STRICT_OPTION }, { "tag", TAG_OPTION }, { "zero", 'z' },
  { "binary", 'b' }, { "text", 't' }, { "help", HELP_OPTION },
  { "version", VERSION_OPTION },
};
#define N_LONG (sizeof long_options / sizeof long_options[0])

static void getopt_err3(const char *a, const char *b, const char *c)
{
  ebuf.len = 0;
  buf_puts(&ebuf, getopt_argv0);
  buf_puts(&ebuf, a);
  buf_puts(&ebuf, b);
  buf_puts(&ebuf, c);
  err_write(ebuf.p, ebuf.len);
}

/* glibc process_long_option for "--" + text; returns option value or '?'. */
static int long_option(const char *text)
{
  size_t namelen = 0;
  while (text[namelen] && text[namelen] != '=')
    namelen++;
  for (size_t k = 0; k < N_LONG; k++)
    if (c_strneq(long_options[k].name, text, namelen)
        && namelen == c_strlen(long_options[k].name))
      return text[namelen] ? (getopt_err3(": option '--", long_options[k].name,
                                          "' doesn't allow an argument\n"), '?')
                           : long_options[k].val;
  int found = -1, ambig = 0;
  unsigned char set[N_LONG] = { 0 };
  for (size_t k = 0; k < N_LONG; k++)
    if (c_strneq(long_options[k].name, text, namelen))
      {
        if (found < 0)
          found = (int)k;
        else
          {
            ambig = 1;
            set[found] = 1;
            set[k] = 1;
          }
      }
  if (ambig)
    {
      ebuf.len = 0;
      buf_puts(&ebuf, getopt_argv0);
      buf_puts(&ebuf, ": option '--");
      buf_puts(&ebuf, text);
      buf_puts(&ebuf, "' is ambiguous; possibilities:");
      for (size_t k = 0; k < N_LONG; k++)
        if (set[k])
          {
            buf_puts(&ebuf, " '--");
            buf_puts(&ebuf, long_options[k].name);
            buf_put(&ebuf, '\'');
          }
      buf_put(&ebuf, '\n');
      err_write(ebuf.p, ebuf.len);
      return '?';
    }
  if (found < 0)
    {
      getopt_err3(": unrecognized option '--", text, "'\n");
      return '?';
    }
  if (text[namelen])
    {
      getopt_err3(": option '--", long_options[found].name, "' doesn't allow an argument\n");
      return '?';
    }
  return long_options[found].val;
}

/* ---------------------------------------------------------------- main */

static int do_check, prefix_tag, binary = -1;

static void option(int opt)
{
  switch (opt)
    {
    case 'c': do_check = 1; break;
    case STATUS_OPTION: status_only = 1; warn = 0; quiet = 0; break;
    case 'b': binary = 1; break;
    case 't': binary = 0; break;
    case 'w': status_only = 0; warn = 1; quiet = 0; break;
    case IGNORE_MISSING_OPTION: ignore_missing = 1; break;
    case QUIET_OPTION: status_only = 0; warn = 0; quiet = 1; break;
    case STRICT_OPTION: strict = 1; break;
    case TAG_OPTION: prefix_tag = 1; binary = 1; break;
    case 'z': digest_delim = '\0'; break;
    case HELP_OPTION: usage(0);
    case VERSION_OPTION: out_puts(version_text); do_exit(0);
    default: usage(1);
    }
}

static void usage_error(const char *msg)
{
  error_msg(0, 0, msg);
  usage(1);
}

static void set_program_name(char *argv0)
{
  char *slash = 0;
  for (char *p = argv0; *p; p++)
    if (*p == '/')
      slash = p;
  char *base = slash ? slash + 1 : argv0;
  if (base - argv0 >= 7 && c_strneq(base - 7, "/.libs/", 7))
    {
      argv0 = base;
      if (c_strneq(base, "lt-", 3))
        argv0 = base + 3;
    }
  program_name = argv0;
}

__attribute__((noreturn, used)) void cmain(long *sp)
{
  int argc = (int)sp[0];
  char **argv = (char **)(sp + 1);
  char **envp = argv + argc + 1;

  if (argc == 0 || !argv[0])
    {
      static const char m[] = "A NULL argv[0] was passed through an exec system call.\n";
      err_write(m, sizeof m - 1);
      sc3(SYS_kill, sc3(SYS_getpid, 0, 0, 0), SIGABRT, 0);
      sys_exit(134);
    }
  set_program_name(argv[0]);
  getopt_argv0 = argv[0];

  int posixly_correct = 0;
  for (char **e = envp; *e; e++)
    if (c_strneq(*e, "POSIXLY_CORRECT=", 16))
      posixly_correct = 1;

  /* getopt_long, PERMUTE (or REQUIRE_ORDER under POSIXLY_CORRECT).
     Operands are compacted in place into argv[0..n_operands), always below
     the read index (argv[0]'s pointer was saved above), so at most argc - 1
     slots are used and the default "-" always fits. So hashing needs no
     heap: brk is reached only by error messages, quotef and check mode. */
  char **operands = argv;
  int n_operands = 0, i = 1;
  for (; i < argc; i++)
    {
      char *a = argv[i];
      if (a[0] == '-' && a[1] == '-' && a[2] == '\0')
        {
          i++;
          break;
        }
      if (a[0] != '-' || a[1] == '\0')
        {
          if (posixly_correct)
            break;
          operands[n_operands++] = a;
          continue;
        }
      if (a[1] == '-')
        {
          option(long_option(a + 2));
          continue;
        }
      for (char *p = a + 1; *p; p++)
        {
          char c = *p;
          /* glibc: temp = strchr (optstring, c) */
          const char *t = "bctwz";
          while (*t && *t != c)
            t++;
          if (*t)
            option(c);
          else
            {
              char cs[2] = { c, 0 };
              getopt_err3(": invalid option -- '", cs, "'\n");
              option('?');
            }
        }
    }
  for (char **p = argv + i; p < argv + argc; p++)
    operands[n_operands++] = *p;

  if (prefix_tag && !binary)
    usage_error("--tag does not support --text mode");
  if (digest_delim != '\n' && do_check)
    usage_error("the --zero option is not supported when verifying checksums");
  if (prefix_tag && do_check)
    usage_error("the --tag option is meaningless when verifying checksums");
  if (0 <= binary && do_check)
    usage_error("the --binary and --text options are meaningless when verifying checksums");
  if (ignore_missing && !do_check)
    usage_error("the --ignore-missing option is meaningful only when verifying checksums");
  if (status_only && !do_check)
    usage_error("the --status option is meaningful only when verifying checksums");
  if (warn && !do_check)
    usage_error("the --warn option is meaningful only when verifying checksums");
  if (quiet && !do_check)
    usage_error("the --quiet option is meaningful only when verifying checksums");
  if (strict && !do_check)
    usage_error("the --strict option is meaningful only when verifying checksums");
  if (binary < 0)
    binary = 0;

  if (n_operands == 0)
    operands[n_operands++] = (char *)"-";

  int ok = 1;
  uint8_t bin[32];
  for (int k = 0; k < n_operands; k++)
    {
      char *file = operands[k];
      if (do_check)
        ok &= digest_check(file);
      else
        {
          int missing;
          if (!digest_file(file, bin, &missing))
            ok = 0;
          else
            output_file(file, binary, bin, prefix_tag, digest_delim);
        }
    }

  if (have_read_stdin)
    {
      long r = sys_close(0);
      if (r < 0)
        error_msg(1, (int)-r, "standard input");
    }
  do_exit(ok ? 0 : 1);
}

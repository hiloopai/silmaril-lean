/* A probe header for the clang -> normalized-header import
   (Silmaril.Data.Layout.Header.Import): one declaration of each kind, attribute and calling
   convention the import distinguishes, and some it keeps as unsupported. Not a library. */
#ifndef PROBE_H
#define PROBE_H
typedef unsigned int u32;
typedef struct pair { int a; long b; } pair_t;
struct fwd;
union u { int i; float f; };
enum color { RED, GREEN = 4 };
typedef int (*cmp_fn)(const void *, const void *);
typedef u32 vec4[4];
extern int counter;
extern const char *names[];
int plain(int x, u32 y);
long knr();
int vf(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
void die(const char *msg) __attribute__((noreturn));
_Noreturn void die2(void);
void *nn(void *p, void *q) __attribute__((nonnull(1)));
int old(int) __attribute__((deprecated));
int hidden(int) __attribute__((visibility("hidden")));
int renamed(int) __asm__("renamed_v2");
int __attribute__((ms_abi)) win(int a, int b);
int __attribute__((sysv_abi)) sysv(int a);
int __attribute__((regcall)) rc(int a);
pair_t by_value(pair_t p);
double fp(float x, long double y);
_Bool flag(void);
void sort(void *base, unsigned long n, cmp_fn cmp);
void arr(int a[4], int b[]);
struct fwd *mk(void);
enum color paint(enum color c);
static inline int inl(int x) { return x + 1; }
int plain(int x, u32 y);
#endif

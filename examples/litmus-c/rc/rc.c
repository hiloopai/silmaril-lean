/* A reference-counting library (Silmaril/X86/Concurrency/Cir/Rc).

   An `rc_t` is a 4-byte count and a 4-byte payload, allocated with malloc (the CIR allocator
   interface `Rc.Alloc` stands for malloc/free; Sep.Alloc.Iface is its x86 counterpart).

   rc_clone: C11 fetch_add(1, relaxed)                       -> x86 `lock add DWORD PTR [rdi],1`
   rc_drop:  C11 fetch_sub(1, release); on the last reference fence(acquire) and the outlined
             cold path rc_drop_slow, which frees              -> `lock sub [rdi],1; je cold; ret`
   The acquire fence compiles to nothing on x86 (the locked sub is a full barrier).

   The Lean side validates rc_clone, rc_drop and the two clients with inlined operations
   (rc_publish, rc_share2) into CIR's derived ops rcInc/rcDrop (Cir/Rc/Tv). rc_new (a call to
   malloc), rc_drop_slow (a tail call to free) and rc_dec_and_test (`sete`) are not validated. */
typedef struct { unsigned cnt; unsigned data; } rc_t;
extern void *malloc(unsigned long);
extern void free(void *);

rc_t *rc_new(unsigned v) {
  rc_t *r = malloc(sizeof *r);
  if (r) { r->cnt = 1; r->data = v; }
  return r;
}

static inline void rc_inc(rc_t *r) { __atomic_fetch_add(&r->cnt, 1, __ATOMIC_RELAXED); }

/* The outlined cold path of the last drop. */
__attribute__((noinline)) static void rc_drop_slow(rc_t *r) { free(r); }

static inline void rc_dec(rc_t *r) {
  if (__builtin_expect(__atomic_fetch_sub(&r->cnt, 1, __ATOMIC_RELEASE) == 1, 0)) {
    __atomic_thread_fence(__ATOMIC_ACQUIRE);
    rc_drop_slow(r);
  }
}

void rc_clone(rc_t *r) { rc_inc(r); }
void rc_drop(rc_t *r) { rc_dec(r); }

/* C11: atomic_fetch_sub_explicit(&r->cnt, 1, memory_order_release) == 1. */
int rc_dec_and_test(rc_t *r) { return __atomic_fetch_sub(&r->cnt, 1, __ATOMIC_RELEASE) == 1; }

/* Clients with inlined operations: read the payload through the reference and drop it; take
   two clones and drop one. */
void rc_publish(rc_t *r, unsigned *out) {
  *out = __atomic_load_n(&r->data, __ATOMIC_RELAXED);
  rc_dec(r);
}
void rc_share2(rc_t *r) { rc_inc(r); rc_inc(r); rc_dec(r); }

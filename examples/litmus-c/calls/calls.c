/* A caller of the mutex of examples/litmus-c/mutex, validated through its call sites
   (Silmaril/X86/Concurrency/Bridge/Crit).

   mutex_lock and mutex_unlock are those of examples/litmus-c/mutex/mutex.c, made static and
   noinline so that crit_add2 calls them with `call rel32` inside this object; their bytes are
   identical to the pinned ones. crit_add2 is a critical section in the shape of a Cir.Pool job
   (`lock(m); body; unlock(m)`): the body adds 2 to a shared counter with relaxed (plain)
   32-bit accesses.

   Compiled with the pinned gcc and flags (../toolchains.txt) plus -fno-optimize-sibling-calls,
   so the last call stays a `call` (not a tail `jmp`). gcc's IPA register allocation sees that
   the callees clobber only rax, rdx and the flags, so crit_add2 keeps `x` in rsi across the
   calls and needs no stack frame:

     crit_add2:  call mutex_lock ; mov eax,[rsi] ; add eax,2 ; mov [rsi],eax ;
                 call mutex_unlock ; ret

   The Lean side (Silmaril/X86/Concurrency/Bridge/Crit) checks the whole .text with the caller
   checker `Bridge.ltv`, the callees with the mutex's certificates. */
typedef struct { int v; int tok; } mutex_t;

__attribute__((noinline, noclone)) static void mutex_lock(mutex_t *m) {
  while (__atomic_exchange_n(&m->v, 1, __ATOMIC_ACQUIRE))
    while (__atomic_load_n(&m->v, __ATOMIC_RELAXED))
      __builtin_ia32_pause();
}

__attribute__((noinline, noclone)) static void mutex_unlock(mutex_t *m) {
  (void)__atomic_exchange_n(&m->v, 0, __ATOMIC_RELEASE);
}

void crit_add2(mutex_t *m, int *x) {
  mutex_lock(m);
  int v = __atomic_load_n(x, __ATOMIC_RELAXED);
  __atomic_store_n(x, v + 2, __ATOMIC_RELAXED);
  mutex_unlock(m);
}

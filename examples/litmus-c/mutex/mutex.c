/* A mutex meeting the CIR Mutex interface.

   The object is two 4-byte cells: the lock word `v` and a token cell `tok` that no code
   touches. The token cell is the CSL ownership token of the lock holder (Cir.Csl has no
   ghost state, so the token is a real, never-accessed cell).

   Acquire: test-and-test-and-set with an acquire exchange, byte-identical to sync-prims' spin_lock.
   Release: an exchange, which is a locked instruction on x86. Cir.Csl accepts a release only at
   a draining instruction; the plain `mov` of a C11 release store (sync-prims' spin_unlock) is not
   accepted (Task.movUnlock in Cir/Mutex/Defs.lean). Both C11 spellings below compile to
   `xor eax,eax; xchg [rdi],eax`. */
typedef struct { int v; int tok; } mutex_t;

void mutex_lock(mutex_t *m) {
  while (__atomic_exchange_n(&m->v, 1, __ATOMIC_ACQUIRE))
    while (__atomic_load_n(&m->v, __ATOMIC_RELAXED))
      __builtin_ia32_pause();
}

/* C11: atomic_exchange_explicit(&m->v, 0, memory_order_release). */
void mutex_unlock(mutex_t *m) { (void)__atomic_exchange_n(&m->v, 0, __ATOMIC_RELEASE); }

/* C11: atomic_store_explicit(&m->v, 0, memory_order_seq_cst). */
void mutex_unlock_sc(mutex_t *m) { __atomic_store_n(&m->v, 0, __ATOMIC_SEQ_CST); }

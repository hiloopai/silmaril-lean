/* Test-and-set spinlock. Acquire: xchg until the old value is 0, spinning on
   plain loads in between (test-and-test-and-set). Release: a plain release store. */
typedef struct { int v; } spin_t;

void spin_lock(spin_t *l) {
  while (__atomic_exchange_n(&l->v, 1, __ATOMIC_ACQUIRE))
    while (__atomic_load_n(&l->v, __ATOMIC_RELAXED))
      __builtin_ia32_pause();
}

void spin_unlock(spin_t *l) { __atomic_store_n(&l->v, 0, __ATOMIC_RELEASE); }

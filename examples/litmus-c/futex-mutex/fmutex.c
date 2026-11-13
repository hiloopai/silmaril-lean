/* Drepper's futex mutex (U. Drepper, "Futexes Are Tricky", mutex 2/3).

   The lock word `v` is 0 (unlocked), 1 (locked, no waiters) or 2 (locked, possible waiters).
   The object is two 4-byte cells, as examples/litmus-c/mutex's mutex_t: the lock word and a token cell `tok` that no
   code touches (Cir.Csl has no ghost state; the token is the holder's CSL ownership token).

   Lock (Drepper's mutex 2/3 lock, C11 atomics): try 0 -> 1 with a compare-and-swap; otherwise
   mark the lock contended (exchange in 2) and sleep on the word while it is 2.

   Two unlocks:
   - fmutex_unlock: exchange in 0 (release); wake one waiter if the old value was 2. This is the
     common form of Drepper's unlock (glibc's lll_unlock, Rust's std futex mutex). It compiles to
     `xchg`, a locked instruction, so Cir.Csl accepts it.
   - fmutex_unlock_dec: Drepper's original mutex 2 unlock: fetch_sub 1; if the old value was not
     1, store 0 (release) and wake one. The store is a plain `mov`, the case of the mutex's
     Task.movUnlock.

   futex(2) is called directly (number 202, FUTEX_WAIT_PRIVATE 128, FUTEX_WAKE_PRIVATE 129, null
   timeout), as in examples/litmus-c/futex/futex.h. */
typedef struct { int v; int tok; } fmutex_t;

static inline long sys_futex(int *a, long op, unsigned int val) {
  register long r10 __asm__("r10") = 0;
  long ret;
  __asm__ volatile("syscall"
                   : "=a"(ret)
                   : "0"(202L), "D"(a), "S"(op), "d"(val), "r"(r10)
                   : "rcx", "r11", "memory");
  return ret;
}

void fmutex_lock(fmutex_t *m) {
  int c = 0;
  if (!__atomic_compare_exchange_n(&m->v, &c, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED)) {
    if (c != 2)
      c = __atomic_exchange_n(&m->v, 2, __ATOMIC_ACQUIRE);
    while (c != 0) {
      sys_futex(&m->v, 128, 2);
      c = __atomic_exchange_n(&m->v, 2, __ATOMIC_ACQUIRE);
    }
  }
}

void fmutex_unlock(fmutex_t *m) {
  if (__atomic_exchange_n(&m->v, 0, __ATOMIC_RELEASE) == 2)
    sys_futex(&m->v, 129, 1);
}

void fmutex_unlock_dec(fmutex_t *m) {
  if (__atomic_fetch_sub(&m->v, 1, __ATOMIC_RELEASE) != 1) {
    __atomic_store_n(&m->v, 0, __ATOMIC_RELEASE);
    sys_futex(&m->v, 129, 1);
  }
}

/* Seqlock with one writer. The writer makes `seq` odd, writes the two data
   words, and makes `seq` even again. A reader retries until it saw the same even `seq`
   before and after reading the data. All data accesses are relaxed atomics (C11-race-free). */
typedef struct { unsigned seq, a, b; } seqlock_t;

void seq_write(seqlock_t *s, unsigned a, unsigned b) {
  unsigned q = __atomic_load_n(&s->seq, __ATOMIC_RELAXED);
  __atomic_store_n(&s->seq, q + 1, __ATOMIC_RELAXED);
  __atomic_thread_fence(__ATOMIC_RELEASE);
  __atomic_store_n(&s->a, a, __ATOMIC_RELAXED);
  __atomic_store_n(&s->b, b, __ATOMIC_RELAXED);
  __atomic_store_n(&s->seq, q + 2, __ATOMIC_RELEASE);
}

void seq_read(seqlock_t *s, unsigned *out) {
  unsigned q, a, b;
  do {
    q = __atomic_load_n(&s->seq, __ATOMIC_ACQUIRE);
    a = __atomic_load_n(&s->a, __ATOMIC_RELAXED);
    b = __atomic_load_n(&s->b, __ATOMIC_RELAXED);
    __atomic_thread_fence(__ATOMIC_ACQUIRE);
  } while ((q & 1) || q != __atomic_load_n(&s->seq, __ATOMIC_RELAXED));
  out[0] = a;
  out[1] = b;
}

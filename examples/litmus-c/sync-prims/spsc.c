/* Single-producer single-consumer ring of capacity 2, Lamport style: the
   producer owns `tail`, the consumer owns `head`; each reads the other's index with an
   acquire load and publishes its own with a release store. */
#define CAP 2
typedef struct { unsigned head, tail; unsigned buf[CAP]; } spsc_t;

int spsc_push(spsc_t *q, unsigned v) {
  unsigned t = __atomic_load_n(&q->tail, __ATOMIC_RELAXED);
  unsigned h = __atomic_load_n(&q->head, __ATOMIC_ACQUIRE);
  if (t - h == CAP) return 0;
  q->buf[t % CAP] = v;
  __atomic_store_n(&q->tail, t + 1, __ATOMIC_RELEASE);
  return 1;
}

int spsc_pop(spsc_t *q, unsigned *out) {
  unsigned h = __atomic_load_n(&q->head, __ATOMIC_RELAXED);
  unsigned t = __atomic_load_n(&q->tail, __ATOMIC_ACQUIRE);
  if (t == h) return 0;
  *out = q->buf[h % CAP];
  __atomic_store_n(&q->head, h + 1, __ATOMIC_RELEASE);
  return 1;
}

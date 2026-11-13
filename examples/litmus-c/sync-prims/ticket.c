/* Ticket lock. Acquire: take a ticket with fetch_add, wait until it is served.
   Release: the holder alone increments `serving`, with a plain release store. */
typedef struct { unsigned next, serving; } ticket_t;

void ticket_lock(ticket_t *l) {
  unsigned me = __atomic_fetch_add(&l->next, 1, __ATOMIC_RELAXED);
  while (__atomic_load_n(&l->serving, __ATOMIC_ACQUIRE) != me)
    __builtin_ia32_pause();
}

void ticket_unlock(ticket_t *l) {
  unsigned s = __atomic_load_n(&l->serving, __ATOMIC_RELAXED);
  __atomic_store_n(&l->serving, s + 1, __ATOMIC_RELEASE);
}

/* Single-producer single-consumer ring of capacity 2.
 *
 * The producer P0 sends 1, 2, 3; the consumer P1 receives three values into r1, r2, r3.
 * `tail` (written only by P0) counts the messages produced, `head` (written only by P1) the
 * messages consumed; message k (from 1) lives in slot (k - 1) % 2.
 *
 * send(k, v): wait until head >= k - 2 (a slot is free), write slot (k - 1) % 2, tail = k.
 * recv(k):    wait until tail >= k, read slot (k - 1) % 2, head = k.
 *
 * Compiled with -DSWAP, the producer publishes before it writes the payload (the mutant).
 */
#include "../chan.h"
#define S0 0x10000ul
#define S1 0x10040ul
#define TAIL 0x10080
#define HEAD 0x100c0
#define R1 0x10100
#define R2 0x10140
#define R3 0x10180
#define CAP 2u
#define SLOT(k) (((k) - 1u) % CAP == 0u ? S0 : S1)

static inline void send(unsigned k, unsigned v) {
  if (k > CAP)
    while (LD_ACQ(HEAD) < k - CAP)
      ;
#ifdef SWAP
  ST_REL(TAIL, k); /* mutant: publish before the payload is written */
  ST_NA(SLOT(k), v);
#else
  ST_NA(SLOT(k), v);
  ST_REL(TAIL, k);
#endif
}

static inline unsigned recv(unsigned k) {
  while (LD_ACQ(TAIL) < k)
    ;
  unsigned v = LD_NA(SLOT(k));
  ST_REL(HEAD, k);
  return v;
}

void P0(void) { send(1, 1); send(2, 2); send(3, 3); }

void P1(void) {
  unsigned a = recv(1);
  unsigned b = recv(2);
  unsigned c = recv(3);
  ST_NA(R1, a);
  ST_NA(R2, b);
  ST_NA(R3, c);
}

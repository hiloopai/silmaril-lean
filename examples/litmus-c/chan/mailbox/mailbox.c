/* One-slot mailbox with sequence numbers.
 *
 * The producer P0 sends 1, 2, 3; the consumer P1 receives three values and stores them in
 * r1, r2, r3. `seq` (written only by P0) counts the messages put in the slot, `ack` (written
 * only by P1) the messages taken out. Single-writer control words make the coherence order
 * of every cell forced by program order.
 *
 * send(k, v): wait until ack == k - 1 (the slot is empty), write the payload, publish seq = k.
 * recv(k):    wait until seq == k (message k is in the slot), read the payload, ack = k.
 *
 * Compiled with -DSWAP, the producer publishes before it writes the payload (the mutant).
 */
#include "../chan.h"
#define DATA 0x10000
#define SEQ 0x10040
#define ACK 0x10080
#define R1 0x100c0
#define R2 0x10100
#define R3 0x10140

static inline void send(unsigned k, unsigned v) {
  while (LD_ACQ(ACK) != k - 1)
    ;
#ifdef SWAP
  ST_REL(SEQ, k); /* mutant: publish before the payload is written */
  ST_NA(DATA, v);
#else
  ST_NA(DATA, v);
  ST_REL(SEQ, k);
#endif
}

static inline unsigned recv(unsigned k) {
  while (LD_ACQ(SEQ) != k)
    ;
  unsigned v = LD_NA(DATA);
  ST_REL(ACK, k);
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

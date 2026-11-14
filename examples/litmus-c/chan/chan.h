/* Fixed-address access macros for the channel C programs (tools/litmus-x86 `chan`,
 * Silmaril/X86/Concurrency/Cir/Tv/Chan).
 *
 * Every location is an unsigned int at a fixed data-page address (0x10000 + 64 k), so the
 * accesses compile to absolute [disp32] operands (no RIP-relative operands).
 *
 *   ST_NA / LD_NA   plain (non-atomic) payload accesses, protected by the protocol;
 *   ST_REL / LD_ACQ C11 release stores and acquire loads of the control words.
 *
 * Under the protocol every payload access is ordered with every conflicting one by
 * happens-before, so the plain payload accesses are not data races in C11.
 */
#ifndef SILMARIL_LITMUS_CHAN_H
#define SILMARIL_LITMUS_CHAN_H

#define AT(a) ((unsigned *)(a))
#define ST_NA(a, v) (*(volatile unsigned *)(a) = (v))
#define LD_NA(a) (*(volatile unsigned *)(a))
#define ST_REL(a, v) __atomic_store_n(AT(a), (v), __ATOMIC_RELEASE)
#define LD_ACQ(a) __atomic_load_n(AT(a), __ATOMIC_ACQUIRE)

#endif

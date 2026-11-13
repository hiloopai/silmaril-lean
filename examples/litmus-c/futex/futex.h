/* Raw futex system calls and fixed-address locations for the futex C litmus programs
 * (tools/litmus-x86 `cir-f`, Silmaril/X86/Concurrency/Cir/Tv/CFutex).
 *
 * FUTEX_WAIT(a, v) and FUTEX_WAKE(a, n) are the raw Linux system call futex(2) on the int at
 * address a (number 202 in rax; uaddr in rdi, op in rsi, val in rdx, a null timeout in r10),
 * with the private-futex flag. val is an unsigned int, as the kernel reads it (a u32), so passing
 * an int loaded from memory needs no sign extension. They are inline assembly, so the compiler emits exactly one
 * `syscall` and treats it as a compiler barrier ("memory" clobber); rcx and r11 are clobbered
 * as the syscall instruction does. Translation validation into CIR reads a `syscall` with
 * rax = 202 as CIR's futexWait / futexWake.
 *
 * LOC(a) is the int at the fixed data-page address a (0x10000 + 64 k), so accesses compile to
 * absolute [disp32] operands (no RIP-relative operands, no relocations).
 */
#ifndef SILMARIL_LITMUS_FUTEX_H
#define SILMARIL_LITMUS_FUTEX_H

#define LOC(a) (*(volatile int *)(a))
#define ALOC(a) ((int *)(a))

#define FUTEX_WAIT_PRIVATE 128
#define FUTEX_WAKE_PRIVATE 129

static inline long cir_futex(long a, long op, unsigned int val) {
  register long r10 __asm__("r10") = 0;
  long ret;
  __asm__ volatile("syscall"
                   : "=a"(ret)
                   : "0"(202L), "D"(a), "S"(op), "d"(val), "r"(r10)
                   : "rcx", "r11", "memory");
  return ret;
}

#define FUTEX_WAIT(a, v) cir_futex((a), FUTEX_WAIT_PRIVATE, (v))
#define FUTEX_WAKE(a, n) cir_futex((a), FUTEX_WAKE_PRIVATE, (n))

#endif

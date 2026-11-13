/* Spawn/join marker calls and fixed-address locations for the spawn/join C litmus programs
 * (tools/litmus-x86 `cir-c`, Silmaril/X86/Concurrency/Cir/Tv/CSpawn).
 *
 * SPAWN(t) and JOIN(t) compile to `call cir_spawn<t>` / `call cir_join<t>`: marker calls that
 * the translation validation into CIR reads as CIR's `spawn t` / `join t`. They are inline
 * assembly so that the compiler emits exactly one `call` (no tail call, no stack alignment
 * around it) and treats it as a compiler barrier ("memory" clobber). The stub is assumed to
 * keep every register; nothing here links or runs the stubs.
 *
 * LOC(a) is the int at the fixed data-page address a (0x10000 + 64 k), so the accesses compile
 * to absolute [disp32] operands, the form the `cir` decoder supports (no RIP-relative
 * operands).
 */
#ifndef SILMARIL_LITMUS_SPAWN_H
#define SILMARIL_LITMUS_SPAWN_H

#define LOC(a) (*(int *)(a))
#define SPAWN(t) __asm__ volatile("call cir_spawn" #t ::: "memory")
#define JOIN(t) __asm__ volatile("call cir_join" #t ::: "memory")

#endif

/* Access macros for the C11 litmus programs.
 *
 * Each program is compiled once per variant, selected with -DMODE=<n>:
 *   0  na   plain non-atomic accesses (racy: undefined behaviour in C11; kept to record
 *           what the compilers do with them)
 *   1  rlx  __ATOMIC_RELAXED everywhere
 *   2  ra   stores __ATOMIC_RELEASE, loads __ATOMIC_ACQUIRE, RMWs __ATOMIC_ACQ_REL
 *   3  sc   __ATOMIC_SEQ_CST everywhere
 * Fences (F_SC) are always __atomic_thread_fence(__ATOMIC_SEQ_CST).
 * The per-access C11 mode of every variant is also written down in each program's
 * litmus.txt; tools/litmus-x86 (`c11` mode) checks that the compiled accesses match it.
 *
 * Results go to plain int globals r0, r1, ... that only one thread writes; they are read
 * after the threads have joined, so they are not racy.
 */
#ifndef SILMARIL_LITMUS_C11_H
#define SILMARIL_LITMUS_C11_H

#ifndef MODE
#error "compile with -DMODE=0..3"
#endif

#if MODE == 0
#define ST(p, v) (*(p) = (v))
#define LD(p) (*(p))
#define FADD(p, v) __extension__({ int o_ = *(p); *(p) = o_ + (v); o_; })
#elif MODE == 1
#define ST(p, v) __atomic_store_n(p, v, __ATOMIC_RELAXED)
#define LD(p) __atomic_load_n(p, __ATOMIC_RELAXED)
#define FADD(p, v) __atomic_fetch_add(p, v, __ATOMIC_RELAXED)
#elif MODE == 2
#define ST(p, v) __atomic_store_n(p, v, __ATOMIC_RELEASE)
#define LD(p) __atomic_load_n(p, __ATOMIC_ACQUIRE)
#define FADD(p, v) __atomic_fetch_add(p, v, __ATOMIC_ACQ_REL)
#elif MODE == 3
#define ST(p, v) __atomic_store_n(p, v, __ATOMIC_SEQ_CST)
#define LD(p) __atomic_load_n(p, __ATOMIC_SEQ_CST)
#define FADD(p, v) __atomic_fetch_add(p, v, __ATOMIC_SEQ_CST)
#else
#error "MODE must be 0..3"
#endif

#define F_SC() __atomic_thread_fence(__ATOMIC_SEQ_CST)

#endif

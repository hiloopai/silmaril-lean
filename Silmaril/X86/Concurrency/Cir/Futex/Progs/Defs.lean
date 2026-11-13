module

public import Silmaril.X86.Concurrency.Cir.Futex.Defs

/-!
# The CIR programs of the futex C tests

One CIR program per C source of `examples/litmus-c/futex/`, written
statement by statement from the C (the `.c` files and the CIR here are meant to be read side
by side). `Cir.Tv.FTest.tvOk` checks, by bounded trace inclusion, that the compiled x86 code of
every thread has no trace that the CIR thread lacks.

Modes record the C11 intent (`acq` loads and exchanges, `rel` stores and the unlock's
`fetch_sub`, `na` for plain data). Loops are bounded by `n` iterations; the x86 side is bounded
by its instruction budget, and the inclusion check fails if the budget allows more iterations
than the CIR bound.

| program | threads |
| --- | --- |
| `flag n` | `P0: data = 1; flag :=rel 1; wake(flag, 1)` · `P1: while (flag ==acq 0) wait(flag, 0); r0 = data; done = 1` |
| `flagLate n` | as `flag`, but `P0` wakes before it sets the flag (a lost wake-up) |
| `mutex n` | two threads `lock(); c = c + 1; unlock(); dᵢ = 1` with Drepper's futex mutex |
| `mutexRacy n` | as `mutex`, with a lock that tests the word and then stores `1` |
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Futex.Progs

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Loc)

/-- A 4-byte load. -/
def ld (r : Reg) (m : Mode) (a : Nat) : Stmt := .load r m 4 .wb (.lit a)

/-- A 4-byte store of an expression. -/
def st (m : Mode) (a : Nat) (v : Expr) : Stmt := .store m 4 .wb (.lit a) v

/-- `r != v`. -/
def ne (r : Reg) (v : Nat) : Expr := .bin .ne (.reg r) (.lit v)

/-- `r == v`. -/
def eq (r : Reg) (v : Nat) : Expr := .bin .eq (.reg r) (.lit v)

/-- A thread from a list of statements. -/
def th (l : List Stmt) : Thread := ⟨Stmt.block l, false⟩

/-! ## The event flag -/

abbrev data : Nat := 0x10000
abbrev flagW : Nat := 0x10040
abbrev r0 : Nat := 0x10080
abbrev done : Nat := 0x100c0

/-- The locations of the event-flag tests, with the flag's queue byte. -/
def flagLocs : List Loc :=
  [⟨"data", data, 4, 0⟩, ⟨"flag", flagW, 4, 0⟩, ⟨"r0", r0, 4, 0⟩, ⟨"done", done, 4, 0⟩,
    ⟨"q", qAddr flagW, 1, 0⟩]

/-- The waiter: sleep on the flag until it is set, then read the data and finish. -/
def waiter (n : Nat) : Thread :=
  th [ld .rax .acq flagW,
    .loop n (eq .rax 0) (Stmt.block [.futexWait .rcx (.lit flagW) (.lit 0), ld .rax .acq flagW]),
    ld .rbx .na data, st .na r0 (.reg .rbx), st .na done (.lit 1)]

/-- **The one-shot event flag.** -/
def flag (n : Nat) : Prog :=
  ⟨flagLocs,
    [th [st .na data (.lit 1), st .rel flagW (.lit 1), .futexWake (.lit flagW) (.lit 1)], waiter n]⟩

/-- The event flag with the wake before the flag store (a lost wake-up). -/
def flagLate (n : Nat) : Prog :=
  ⟨flagLocs,
    [th [st .na data (.lit 1), .futexWake (.lit flagW) (.lit 1), st .rel flagW (.lit 1)], waiter n]⟩

/-! ## The mutex -/

abbrev mW : Nat := 0x10000
abbrev cnt : Nat := 0x10040
abbrev d0 : Nat := 0x10080
abbrev d1 : Nat := 0x100c0

/-- The locations of the mutex tests, with the mutex word's queue byte. -/
def mutexLocs : List Loc :=
  [⟨"m", mW, 4, 0⟩, ⟨"c", cnt, 4, 0⟩, ⟨"d0", d0, 4, 0⟩, ⟨"d1", d1, 4, 0⟩, ⟨"q", qAddr mW, 1, 0⟩]

/-- `c = c + 1` (a plain load and store). -/
def incr : List Stmt := [ld .rbx .na cnt, st .na cnt (.bin .add (.reg .rbx) (.lit 1))]

/-- Drepper's lock: `cas(m, 0, 1)`; on failure exchange in `2` (unless already `2`) and sleep
while the old value is not `0`. -/
def lock (n : Nat) : Stmt :=
  Stmt.block [.rmw .rax .acq 4 (.cas (.lit 0)) (.lit mW) (.lit 1),
    .ite (ne .rax 0)
      (Stmt.block [.ite (ne .rax 2) (.rmw .rax .acq 4 .xchg (.lit mW) (.lit 2)) .skip,
        .loop n (ne .rax 0) (Stmt.block [.futexWait .rcx (.lit mW) (.lit 2),
          .rmw .rax .acq 4 .xchg (.lit mW) (.lit 2)])])
      .skip]

/-- Drepper's unlock: `fetch_sub(m, 1)`; if the old value was not `1`, store `0` and wake one. -/
def unlock : Stmt :=
  Stmt.block [.rmw .rax .rel 4 (.op .sub) (.lit mW) (.lit 1),
    .ite (ne .rax 1) (Stmt.block [st .rel mW (.lit 0), .futexWake (.lit mW) (.lit 1)]) .skip]

/-- A mutex thread: lock, increment, unlock, record that it finished. -/
def mThread (n d : Nat) : Thread := th ([lock n] ++ incr ++ [unlock, st .na d (.lit 1)])

/-- **Two threads increment a counter under Drepper's futex mutex.** -/
def mutex (n : Nat) : Prog := ⟨mutexLocs, [mThread n d0, mThread n d1]⟩

/-- The racy lock: read the word, sleep while it is not `0`, then store `1`. -/
def racyLock (n : Nat) : Stmt :=
  Stmt.block [ld .rax .rlx mW,
    .loop n (ne .rax 0) (Stmt.block [.futexWait .rcx (.lit mW) (.reg .rax), ld .rax .rlx mW]),
    st .rlx mW (.lit 1)]

/-- The racy unlock: store `0`, wake one. -/
def racyUnlock : Stmt := Stmt.block [st .rlx mW (.lit 0), .futexWake (.lit mW) (.lit 1)]

/-- A racy-mutex thread. -/
def rThread (n d : Nat) : Thread := th ([racyLock n] ++ incr ++ [racyUnlock, st .na d (.lit 1)])

/-- Two threads increment a counter under the racy mutex. -/
def mutexRacy (n : Nat) : Prog := ⟨mutexLocs, [rThread n d0, rThread n d1]⟩

end Silmaril.X86.Concurrency.Cir.Futex.Progs

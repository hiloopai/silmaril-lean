module

public import Silmaril.X86.Concurrency.Cir.Prim.Mutants.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Sym.Defs

/-!
# Scaling the CIR checks: `N`-thread clients with loop bound `k`

The lock clients have two
threads and loop bound `2` (`Prim.Clients`). Here the same translation-validated function bodies
(`SpinLock.cert.body k`, …) are instantiated for `N` threads and any bound `k`:

* `spinN N k`: `N` threads, each `spin_lock; x = x + 1 (plain); spin_unlock`;
* `tickN N k`: the same with the ticket lock;
* `ttsN N k`: the test-then-set mutant (`ttsC`), which must lose an increment.

Every thread runs the same code from the same registers, so the threads are interchangeable and
`Robust.symCheck` explores each configuration once up to a renaming of the threads.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Scale

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients (regs cs)

/-- A spinlock thread with loop bound `k`. -/
def spinTk (k : Nat) : Stmt := Tv.chain ([SpinLock.cert.body k] ++ cs ++ [SpinUnlock.cert.body k])

/-- A ticket-lock thread with loop bound `k`. -/
def tickTk (k : Nat) : Stmt :=
  Tv.chain ([TicketLock.cert.body k] ++ cs ++ [TicketUnlock.cert.body k])

/-- The test-then-set lock (the mutant) with loop bound `k`. -/
def ttsLockK (k : Nat) : Stmt :=
  Tv.chain [.assign .rdx (.lit 1), SpinLock.ld,
    .loop k (TvCfg.notE (zTest .rax)) SpinLock.ld,
    .store .rlx 4 .wb (at_ .rdi 0) (.reg .rdx)]

/-- A thread of the test-then-set mutant with loop bound `k`. -/
def ttsTk (k : Nat) : Stmt := Tv.chain ([ttsLockK k] ++ cs ++ [SpinUnlock.cert.body k])

/-- `N` copies of a thread with `rdi` at the lock word `0x100`. -/
def copies (N : Nat) (s : Stmt) : List (Stmt × Regs) :=
  (List.range N).map fun _ => (s, regs [(.rdi, 0x100)])

/-- **The `N`-thread spinlock client.** -/
def spinN (N k : Nat) : CSt := start (copies N (spinTk k)) [(0x100, 0), (0x200, 0)]

/-- **The `N`-thread ticket-lock client.** -/
def tickN (N k : Nat) : CSt := start (copies N (tickTk k)) [(0x100, 0), (0x104, 0), (0x200, 0)]

/-- **The `N`-thread test-then-set mutant.** -/
def ttsN (N k : Nat) : CSt := start (copies N (ttsTk k)) [(0x100, 0), (0x200, 0)]

/-- The counter is `n`. -/
def countIs (n : Nat) (c : CSt) : Bool := memOf c.mem 0x200 == some n

/-- Fuel for the explorations (the checks verify closure). -/
def fuel : Nat := 100000

end Silmaril.X86.Concurrency.Cir.Scale

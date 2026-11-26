module

public import Silmaril.X86.Concurrency.Cir.Sync.Defs

/-!
# CIR futexes: wake edges, blocked waiters, lost wake-ups

`Cir.Defs` lowers
`futexWait` and `futexWake` with a ghost one-byte **waiter queue** `qAddr a` per futex word `a`
(see the module docstring there):

| label | events |
| --- | --- |
| `fwait a e s _`, `s ≠ e` (EAGAIN) | `mfence; load a = s; mfence` |
| `fwait a e e r` (returns `0`) | `mfence; store q 1; mfence; load a = e; rmw q r → 0` |
| `fwake a n q` | `mfence; rmw q q → 0; mfence` |
| `fblock a e` (never returns) | `mfence; store q 1; mfence; load a = e` |

So:

* **the kernel check is sequentially consistent**: the load of the word sits between full
  barriers (an `mfence` before it, an `mfence` or a locked RMW after it);
* **spurious wake-ups are allowed**: a wait whose check saw `e` may return with `r = 1`, read
  from its own enqueue, without any wake;
* **a wake synchronises with the wait it wakes**: a woken wait's dequeue reads `r = 0` from a
  wake's locked write of the queue byte. `Exec.fsw` is that `rf` edge, and `Exec.fswHb`
  (`po? ; fsw ; po?`) its happens-before closure. `ScF`/`TsoF`/`XlF` add it to the models.
  As for the spawn/join edges, the edge is a path of each model's own order, so the
  synchronising models equal the plain ones (`Cir.Futex.Thms`).

## Blocked threads (`Prog.btraces`)

A thread can also **block forever** in a wait whose check saw the expected value. Its trace is
then a prefix of a run, cut at that wait, whose last label is `fblock a e`
(`blockPrefixes`). `Prog.btraces` gives every thread its runs and its blocked prefixes, and
`BBehavIn` the behaviours over them. A blocked thread's registers are not meaningful
(`Regs.zero`); a test observes blocking through memory (a `done` flag the thread would have
set).

The futex queue byte makes a **lost wake-up** a final-state property: a blocked waiter whose
enqueue is coherence-last on the queue byte (final value `1`) was not followed by any wake.
With at most one waiter per futex word at a time this is exact; with several, a later
waiter's dequeue also writes `0`, so the queue byte under-reports blocked waiters.

**The Dekker handshake** (`Exec.futex_dekker_xl`): enqueue (`store q 1`), `mfence`, check
(`load a`) on the waiter's side, and `store a`, then a wake's locked `rmw q` on the waker's
side. If the wake's queue write is coherence-before the enqueue, the check cannot read a value
older than the store. This is why "set the flag, then wake" never loses the waiter.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Futex

/-- A futex queue byte: at or above `qAddr 0`. -/
def isQAddr (a : Nat) : Bool := decide (qAddr 0 ≤ a)

end Silmaril.X86.Concurrency.Cir.Futex

namespace Silmaril.X86.MemoryModel.Axiomatic.Exec
variable (x : Exec)

/-- **A wake synchronises with the wait it wakes**: an external `rf` edge between two locked
units of futex queue bytes (a wake's locked write of `0`, read by a woken wait's dequeue). -/
def fsw : BRel x.n := fun w r =>
  x.rfe w r && (x.ev w).isA && (x.ev r).isA &&
    Silmaril.X86.Concurrency.Cir.Futex.isQAddr (x.ev w).addr &&
    Silmaril.X86.Concurrency.Cir.Futex.isQAddr (x.ev r).addr

/-- **The happens-before edges of futex wake-ups**: between memory units, `po? ; fsw ; po?`. -/
def fswHb : BRel x.n := fun a b =>
  (x.ev a).isM && (x.ev b).isM && ((x.poq.seq x.fsw).seq x.poq) a b

/-- SC with the wake edges. -/
def ScF : Prop := x.Sc ∧ BRel.Acyclic (x.scRel.union x.fswHb)

/-- x86-TSO with the wake edges. -/
def TsoF : Prop := x.Tso ∧ BRel.Acyclic (x.ghb.union x.fswHb)

/-- XL with the wake edges. -/
def XlF : Prop := x.Xl ∧ BRel.Acyclic (x.ghbXl.union x.fswHb)

end Silmaril.X86.MemoryModel.Axiomatic.Exec

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (Final XTrace XAct AxReach uniq)

/-! ## Blocked threads -/

/-- The blocked prefixes of a trace: for each wait whose check saw the expected value, the
labels before it followed by `fblock` (the wait never returns). -/
def blockPrefixes : List Lab → List (List Lab)
  | [] => []
  | l :: ls =>
    (match l with
      | .fwait a e s _ => if s = e then [[.fblock a e]] else []
      | _ => []) ++ (blockPrefixes ls).map (l :: ·)

/-- The memory actions of a blocked trace of thread `i`: its start event if it is spawned, and
no end event. -/
def Thread.bacts (th : Thread) (i : Nat) (tr : List Lab) : List XAct :=
  (if th.spawned then [ctlAct i 1 2] else []) ++ tr.flatMap Lab.acts

/-- A blocked trace of thread `i` as a trace (registers zero: not meaningful). -/
def Thread.bxtrace (th : Thread) (i : Nat) (tr : List Lab) : XTrace :=
  ⟨[⟨th.bacts i tr, coreOf Regs.zero⟩], coreOf Regs.zero⟩

/-- The blocked traces of a thread over `dom`, without repetition. -/
def Thread.blocked (th : Thread) (dom : List Nat) : List (List Lab) :=
  uniq ((run dom th.body Regs.zero).flatMap fun p => blockPrefixes p.1)

/-- **The traces of every thread with blocking**: its runs, then its blocked prefixes. -/
def Prog.btraces (P : Prog) (dom : List Nat) : List (List XTrace) :=
  P.threads.mapIdx fun i th =>
    (run dom th.body Regs.zero).map (th.xtrace i) ++ (th.blocked dom).map (th.bxtrace i)

/-- **Behaviours with blocking over a domain**: as `BehavIn`, but a thread may also stop for
ever in a wait whose check saw the expected value. -/
def BBehavIn (P : Prog) (dom : List Nat) (M : Exec → Prop) (f : Final) : Prop :=
  AxReach P.memTest (P.btraces dom) M f

end Silmaril.X86.Concurrency.Cir

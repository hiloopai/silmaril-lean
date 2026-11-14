module

public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Defs

/-!
# The release-store mutex interfaces on every buffered model: statements

`Mutex.link_any_mutexR` and
`link_any_mutexG` are TSO-only because the release rule is
(`Csl.Rel.rel_tso`). For **tame** programs, whose stores are all write-back, the CIR-native XL
machine has the same runs as TSO (`Csl.Tame.reach_tso_of_wb`), so the guarantees hold on every
buffered model. The tameness is split between the two sides of the interface, so it composes:

* `Client.WbIn`: the client's bodies are tame whenever the holes are filled with tame code;
* `IfaceR.WbCode`, `IfaceG.WbCode`: the mutex's lock and unlock code is tame, for every loop
  bound.

`movUnlockXl`, `decUnlockXl`, `ticketIfaceXl` are the three restated Tasks `Mutex.Task.movUnlock`,
`Futex.Task.decUnlock`, `Futex.Task.ticketIface` for every `M : Csl.OModel`, for `WbIn`
clients. All are PROVED in `Mutex/Xl/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- **A tame client**: filling its holes with tame code gives tame bodies. -/
def Client.WbIn (C : Client) : Prop :=
  ∀ lk ul : Expr → Stmt, (∀ a, (lk a).wbStores = true) → (∀ a, (ul a).wbStores = true) →
    ∀ t, (C.body lk ul t).wbStores = true

/-- **A tame `IfaceR` mutex**: its lock and unlock code pass `Stmt.wbStores` for every loop
bound. -/
def IfaceR.WbCode (M : IfaceR) : Prop :=
  ∀ L, (M.lockCode L).wbStores = true ∧ (M.unlockCode L).wbStores = true

/-- **A tame `IfaceG` mutex.** -/
def IfaceG.WbCode (M : IfaceG) : Prop :=
  ∀ L, (M.lockCode L).wbStores = true ∧ (M.unlockCode L).wbStores = true

/-- **`Task.movUnlock` on every buffered model** (PROVED, `Mutex.movUnlockXl_holds`): every tame
client proved against `IfaceR` gets its goal with the spin lock and the `mov` unlock on `OStep M`,
`M = .tso` or `.xl`. -/
def movUnlockXl : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Heap → Prop), C.ProvedR goal → C.WbIn → 8 ≤ C.slot →
    ∀ (L : Nat) (M : OModel) (Cf : OCfg),
      OReach M C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (movUnlockCode L))
        (C.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

end Silmaril.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.X86.Concurrency.Cir

/-- **`Futex.Task.decUnlock` on every buffered model** (PROVED, `Futex.decUnlockXl_holds`):
Drepper's mutex with its `fetch_sub` unlock, for tame clients proved against `IfaceR`. -/
def decUnlockXl : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.ProvedR goal → C.WbIn →
    8 ≤ C.slot → ∀ (L : Nat) (M : Csl.OModel) (Cf : Csl.OCfg),
      Csl.OReach M C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Lock.cert.body L))
        (fun a => .seq (.assign .rdi a) (UnlockDec.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (Spin.init l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

/-- **`Futex.Task.ticketIface` on every buffered model** (PROVED, `Futex.ticketIfaceXl_holds`):
the ticket lock, for tame clients proved against `IfaceG`. -/
def ticketIfaceXl : Prop :=
  ∀ (C : Client) (goal : (Nat → Regs) → Csl.Heap → Prop), C.ProvedG goal → C.WbIn →
    8 ≤ C.slot → C.N < 2 ^ 32 → ∀ (L : Nat) (M : Csl.OModel) (Cf : Csl.OCfg),
      Csl.OReach M C.N (C.startWith
        (fun a => .seq (.assign .rdi a) (Prim.TicketLock.cert.body L))
        (fun a => .seq (.assign .rdi a) (Prim.TicketUnlock.cert.body L))
        (C.locks.foldr (fun l h => Csl.Heap.union (ticketInit l) h) Csl.Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < C.N, (Cf.ts t).1 = .skip) → goal (fun t => (Cf.ts t).2) Cf.mem

end Silmaril.X86.Concurrency.Cir.Mutex.Futex

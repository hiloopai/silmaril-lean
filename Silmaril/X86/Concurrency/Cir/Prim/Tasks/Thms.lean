module

public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spin
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Ticket
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.TicketWit
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Seq
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spsc
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex
import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SeqRun

/-!
# The synchronisation primitives' goals for every client: what is proved

PROVED (standard axioms
only):

* **`spinMutexTso_holds : Task.spinMutexTso`**: the spinlock (the `spin_lock`, and
  `spin_unlock`, a plain `mov` of `0`) is a lock on TSO for every number of threads, every loop
  bound and every critical section that is CSL-safe from `R` back to `R` and keeps `rdi`: every
  finished, drained TSO state has the lock word `0` and contains a heap satisfying `R`. Proof:
  the release rule of `Csl.Rel` (`rel_tso`), with a ghost token in the lock invariant
  (`lockInvG`); the acquire is `spinLock_acquireR`, the unlock `spinUnlock_release`.
* `spinLock_acquireR`, `spinUnlock_release`: the two halves as `SafeR` specs, for reuse.

* **`seqlockTso_holds : Task.seqlockTso`**: one writer with any list of writes (fewer than
  `2 ^ 31`) and any number of readers with disjoint output pairs, every loop bound: at every
  finished, drained TSO state each reader's output is `(0, 0)` or one of the written pairs.
* **`spscFifoTsoPrim_false : ¬ spscFifoTsoPrim`**: the SPSC statement is false, because a push
  into a full ring drops its value (`vs = [1, 2, 3, 4]`, three pops, outputs `[1, 2, 4]`).
* **`spscFifoTso_holds : Task.spscFifoTso`** (the restatement): with the push results
  recorded, the popped values followed by the values left in the ring are exactly the pushed
  values, in order, on TSO, for any pushes, pops and loop bound.

* Non-vacuity: `seqlock_finishes` and `spscRec_finishes` are finished TSO runs from the
  Tasks' starts for small instances (scheduled CIR explorer steps, kernel `decide`).

The proofs of the two seqlock and SPSC results use a thread-modular logic for single-writer
cells on the TSO machine (`Proofs/…/Prim/Tasks/Sw.lean`, `Sw.sw_final`), not the release rule.

The ticket lock, PROVED (standard axioms only):

* **`ticketMutexTso_holds : Task.ticketMutexTso`**: the ticket lock (the `ticket_lock`, a
  `lock xadd` and a plain-load wait, and `ticket_unlock`, a plain `mov` of `serving + 1`) is a
  lock on TSO for every number `N < 2 ^ 32` of threads, every loop bound and every critical
  section as above: every finished, drained TSO state has `next = serving = N` and contains a
  heap satisfying `R`. Proof: the release rule (`rel_tsoG`) with the ghost invariant
  `ticketInvG` (ticket tokens, turn tokens, receipts and permits; see `Prim/Tasks/Defs.lean`);
* `ticketMutexTso_nonvacuous`: a real two-thread run meets the hypotheses;
* `ticketLock_acquireR`, `ticketUnlock_rel`: the two halves as `SafeR` specs, for reuse (the
  Mutex interface with ghost state, `Mutex.ticketMutexG`).

No Task of this header stays open.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Clients

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

/-- **Acquire** (`SafeR`, every loop bound): from nothing, `spin_lock` ends owning `R` and the
token, with `rdi` unchanged. -/
theorem spinLock_acquireR (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (hl : (rs .rdi).toNat = l) :
    SafeR (spinInvG l R) (fun p rs' h g => p = false ∧ rs' .rdi = rs .rdi ∧ R h ∧ g = spinTk)
      false (Prim.SpinLock.cert.body L) rs Heap.empty Heap.empty :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.spinLock_acquireR l R L rs hl

/-- **Release by a plain `mov`**: `spin_unlock` gives `R` and the token back to the invariant. -/
theorem spinUnlock_release (l : Nat) (R : HProp) (L : Nat) (rs : Regs) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hR : R h) :
    SafeR (spinInvG l R) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) false
      (Prim.SpinUnlock.cert.body L) rs h spinTk :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.spinUnlock_release l R L rs h hl hR

/-- **Ticket acquire** (`SafeR`, every loop bound, either pending flag): from a permit `u < B`
and receipts `F`, `ticket_lock` ends owning `R` and a turn `k`, with `rdi` unchanged. -/
theorem ticketLock_acquireR (l B : Nat) (R : HProp) (L : Nat) (rs : Regs) (p : Bool) (u : Nat)
    (F : Nat → Prop) (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64) (hB : B < 2 ^ 32)
    (hu : u < B) :
    SafeR (ticketInvG l B R) (fun p' rs' h g => p' = false ∧ rs' .rdi = rs .rdi ∧ R h ∧
      ∃ k u', u' < B ∧ g = gsetL l (tkHeld k u' F)) p (Prim.TicketLock.cert.body L) rs
      Heap.empty (gsetL l (tkReady u F)) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.ticketLock_acquireR l B R L rs p u F hl h4 hB hu

/-- **Ticket release by a plain `mov`**: `ticket_unlock` gives `R` and turn `k` back to the
invariant; the thread keeps its permit and gains the receipt `k`. -/
theorem ticketUnlock_rel (l B : Nat) (R : HProp) (L : Nat) (rs : Regs) (h : Heap) (k u : Nat)
    (F : Nat → Prop) (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64) (hR : R h) :
    SafeR (ticketInvG l B R) (fun _ _ h' g' => h' = Heap.empty ∧
      g' = gsetL l (tkReady u (fun j => F j ∨ j = k))) false (Prim.TicketUnlock.cert.body L) rs
      h (gsetL l (tkHeld k u F)) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.ticketUnlock_rel l B R L rs h k u F hl h4 hR

/-! ### Ghost-cell facts for the Mutex interface with ghost state -/

theorem gsetL_isSome {l : Nat} {P : Nat → Nat → Prop} {a : Nat} :
    (gsetL l P a).isSome ↔ ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.gsetL_isSome

theorem tk_gdom {l : Nat} {P : Nat → Nat → Prop} {a : Nat} (e : (gsetL l P a).isSome) :
    (Nat.unpair a).1 = l :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.tk_gdom e

theorem tk_ready_disj (l : Nat) {t u : Nat} (ne : t ≠ u) :
    Heap.Disjoint (gsetL l (tkReady t (fun _ => False))) (gsetL l (tkReady u (fun _ => False))) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.tk_ready_disj l ne

theorem tk_init_ready_disj (l t : Nat) :
    Heap.Disjoint (gsetL l (tkSet 0 0 ∅ false)) (gsetL l (tkReady t (fun _ => False))) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.tk_init_ready_disj l t

theorem tk_init_inv (l B : Nat) (R : HProp) (hR : Heap) (r : R hR)
    (d : Heap.Disjoint (Heap.union (Heap.single l 0) (Heap.single (l + 4) 0)) hR) :
    ticketInvG l B R (Heap.union (Heap.union (Heap.single l 0) (Heap.single (l + 4) 0)) hR)
      (gsetL l (tkSet 0 0 ∅ false)) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.tk_init_inv l B R hR r d

/-- **The ticket token is exclusive relative to the invariant.** -/
theorem tk_locked_excl (l B : Nat) (R : HProp) (h g : Heap) :
    ¬ gsep (gsep (tkLockedG l B) (tkLockedG l B)) (ticketInvG l B R) h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.tk_locked_excl l B R h g

/-- **`Task.ticketMutexTso` is proved**. -/
theorem ticketMutexTso_holds : Task.ticketMutexTso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.ticketMutexTso_holds

/-- **Non-vacuity of `Task.ticketMutexTso`**: two threads, an empty critical
section, loop bound 2: the start reaches a finished, drained TSO state (the explorer), where
`next = serving = 2`. -/
theorem ticketMutexTso_nonvacuous : ∃ C : OCfg, OReach .tso 2
      (lockCfg (Prim.TicketLock.cert.body 2) (Prim.TicketUnlock.cert.body 2) 2 0x100
        (fun _ => .skip) (heapOf [(0x100, 0), (0x104, 0)] Heap.empty)).toO C ∧
    C.Drained ∧ (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x100 = some 2 ∧ C.mem 0x104 = some 2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.ticketMutexTso_nonvacuous

/-- **`Task.spinMutexTso` is proved.** -/
theorem spinMutexTso_holds : Task.spinMutexTso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.spinMutexTso_holds

/-- **`Task.seqlockTso` is proved**. -/
theorem seqlockTso_holds : Task.seqlockTso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Seq.seqlockTso_holds

/-- **The SPSC statement is false**: a full ring drops the pushed value. -/
theorem spscFifoTsoPrim_false : ¬ spscFifoTsoPrim :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex.spscFifoTsoPrim_false

/-- **`Task.spscFifoTso` is proved**: FIFO, nothing lost, nothing duplicated. -/
theorem spscFifoTso_holds : Task.spscFifoTso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spsc.spscFifoTso_holds

/-- **The seqlock client finishes** (non-vacuity of `Task.seqlockTso`): `L = 2`, `s = 0x100`,
`ws = [(1, 1)]`, one reader at `0x200`, which returns `(1, 1)`. -/
theorem seqlock_finishes : ∃ C : Csl.OCfg, Csl.OReach .tso 2 (⟨fun t =>
      if t = 0 then (Tv.chain ([((1 : Nat), (1 : Nat))].map fun p =>
        Tv.chain [.assign .rsi (.lit p.1), .assign .rdx (.lit p.2), SeqWrite.cert.body 2]),
        regs [(.rdi, 0x100)])
      else if t < 2 then (SeqRead.cert.body 2, regs [(.rdi, 0x100), (.rsi, [0x200].getD (t - 1) 0)])
      else (.skip, Regs.zero),
      heapOf ([(0x100, 0), (0x100 + 4, 0), (0x100 + 8, 0)] ++
        [0x200].flatMap fun o => [(o, 0), (o + 4, 0)]) Csl.Heap.empty⟩ :
        Csl.Cfg).toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SeqRun.seqlock_finishes

/-- **The restated SPSC client finishes** (non-vacuity of `Task.spscFifoTso`): `L = 2`,
`q = 0x100`, `out = 0x200`, `res = 0x300`, `k = 3`, `vs = [1, 2, 3, 4]`; the pops return
`[1, 2, 4]` and the third push reports a full ring. -/
theorem spscRec_finishes : ∃ C : Csl.OCfg, Csl.OReach .tso 2 (⟨fun t =>
      if t = 0 then (Tv.chain ((List.range [1, 2, 3, 4].length).map fun j =>
        Tv.chain [.assign .rsi (.lit ([1, 2, 3, 4].getD j 0)), SpscPush.cert.body 2,
          .store .na 4 .wb (.lit (0x300 + 4 * j)) (.reg .rax)]), regs [(.rdi, 0x100)])
      else if t = 1 then (Tv.chain ((List.range 3).map fun i =>
        Tv.chain [.assign .rsi (.lit (0x200 + 4 * i)), SpscPop.cert.body 2]), regs [(.rdi, 0x100)])
      else (.skip, Regs.zero),
      heapOf ([(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0)] ++
        ((List.range 3).map fun i => (0x200 + 4 * i, 0)) ++
        (List.range [1, 2, 3, 4].length).map fun j => (0x300 + 4 * j, 0)) Csl.Heap.empty⟩ :
        Csl.Cfg).toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 2 ∧
    C.mem 0x208 = some 4 ∧ C.mem 0x308 = some 0 ∧ C.mem 0x30c = some 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex.spscRec_finishes

end Silmaril.X86.Concurrency.Cir.Prim.Clients

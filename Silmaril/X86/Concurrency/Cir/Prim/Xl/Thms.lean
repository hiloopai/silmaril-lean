module

public import Silmaril.X86.Concurrency.Cir.Prim.Xl.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Thms

/-!
# The synchronisation primitives on every buffered model: proofs

PROVED (standard axioms only):

* `spinMutexXl_holds`, `ticketMutexXl_holds`, `seqlockXl_holds`, `spscFifoXl_holds`: the four
  synchronisation primitive goals on every buffered model `M` (`.tso`, `.xl`). Each is the TSO
  theorem of
  `Prim/Tasks/Thms.lean` composed with `Csl.Tame.reach_tso_of_wb`: the start is tame
  (`Stmt.wbStores`), so its `OStep M` runs are TSO runs.
* `spinMutexXl_skip`: its hypotheses are met (two threads, empty critical sections) at `.xl`.
* `spinLock_wb`, `spinUnlock_wb`, `ticketLock_wb`, `ticketUnlock_wb`, `seqWrite_wb`,
  `seqRead_wb`, `spscPush_wb`, `spscPop_wb`: the primitives' code passes the check, for every
  loop bound.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Clients

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Csl.Tame (wbStores_gcert wbStores_chain reach_tso_of_wb)

theorem spinLock_wb (L : Nat) : (SpinLock.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem spinUnlock_wb (L : Nat) : (SpinUnlock.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem ticketLock_wb (L : Nat) : (TicketLock.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem ticketUnlock_wb (L : Nat) : (TicketUnlock.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem seqWrite_wb (L : Nat) : (SeqWrite.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem seqRead_wb (L : Nat) : (SeqRead.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem spscPush_wb (L : Nat) : (SpscPush.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide
theorem spscPop_wb (L : Nat) : (SpscPop.cert.body L).wbStores = true := by
  rw [wbStores_gcert]; decide

/-- A lock client's start is tame when its lock, unlock and critical sections are. -/
theorem lockCfg_wb {lock unlock : Stmt} {N l : Nat} {cs : Nat → Stmt} {mem : Csl.Heap}
    (hl : lock.wbStores = true) (hu : unlock.wbStores = true)
    (hcs : ∀ t, (cs t).wbStores = true) : (lockCfg lock unlock N l cs mem).WbStores N := by
  intro t ht
  simp [lockCfg, ht, wbStores_chain, hl, hu, hcs t]

/-- **`spinMutexXl` is proved.** -/
theorem spinMutexXl_holds : spinMutexXl := by
  intro N L l R hR0 cs h1 h2 h3 h4 hw h5 M C hr hd hf
  exact spinMutexTso_holds N L l R hR0 cs h1 h2 h3 h4 h5 C
    (reach_tso_of_wb (lockCfg_wb (spinLock_wb L) (spinUnlock_wb L) hw) hr) hd hf

/-- **`ticketMutexXl` is proved.** -/
theorem ticketMutexXl_holds : ticketMutexXl := by
  intro N L l R hR0 cs h0 h1 h2 h3 h4 h5 hw h6 M C hr hd hf
  exact ticketMutexTso_holds N L l R hR0 cs h0 h1 h2 h3 h4 h5 h6 C
    (reach_tso_of_wb (lockCfg_wb (ticketLock_wb L) (ticketUnlock_wb L) hw) hr) hd hf

/-- **Non-vacuity of `spinMutexXl`'s hypotheses**: two threads with empty
critical sections and the empty resource meet every hypothesis, so every finished, drained XL
run leaves the lock free. -/
theorem spinMutexXl_skip (L : Nat) {C : Csl.OCfg}
    (hr : Csl.OReach .xl 2 (lockCfg (SpinLock.cert.body L) (SpinUnlock.cert.body L) 2 0x1000
      (fun _ => .skip) (heapOf [(0x1000, 0)] Csl.Heap.empty)).toO C)
    (hd : C.Drained) (hf : ∀ t < 2, (C.ts t).1 = .skip) : C.mem 0x1000 = some 0 :=
  (spinMutexXl_holds 2 L 0x1000 (fun h => h = Csl.Heap.empty) Csl.Heap.empty (fun _ => .skip)
    (by decide) rfl rfl (fun _ => by simp [Stmt.writes]) (fun _ => rfl)
    (fun _ _ _ hh => Csl.safe_skip hh) .xl C hr hd hf).1

/-- **`seqlockXl` is proved.** -/
theorem seqlockXl_holds : seqlockXl := by
  intro L s ws outs h1 h2 h3 h4 h5 _ _ _ M C hr hd hf
  refine seqlockTso_holds L s ws outs h1 h2 h3 h4 h5 C (reach_tso_of_wb ?_ hr) hd hf
  intro t ht
  by_cases h0 : t = 0
  · simp [h0, wbStores_chain, seqWrite_wb, Stmt.wbStores]
  · simp [h0, ht, seqRead_wb]

/-- **`spscFifoXl` is proved.** -/
theorem spscFifoXl_holds : spscFifoXl := by
  intro L q out res k vs h1 h2 h3 h4 h5 h6 h7 _ _ _ M C hr hd hf
  refine spscFifoTso_holds L q out res k vs h1 h2 h3 h4 h5 h6 h7 C (reach_tso_of_wb ?_ hr) hd hf
  intro t ht
  by_cases h0 : t = 0
  · simp [h0, wbStores_chain, spscPush_wb, Stmt.wbStores]
  · by_cases h1 : t = 1
    · simp [h1, wbStores_chain, spscPop_wb, Stmt.wbStores]
    · simp [h0, h1, Stmt.wbStores]

end Silmaril.X86.Concurrency.Cir.Prim.Clients

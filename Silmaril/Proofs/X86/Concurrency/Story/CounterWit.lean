module

public import Silmaril.X86.Concurrency.Story.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.Proofs.X86.Concurrency.Story.Counter

/-!
# Proofs: the counter instance finishes, and needs its lock

`Story.Counter.Inst.spinC` is the counter client with two threads linked with the spin mutex at
loop bound 2 (`spinC_cfg`), and the explorer finds a finished, drained TSO state of it whose
counter is `2` (`spin_fin`). So the hypotheses of `Story.Counter.counter_spin` are met by a real
run, and the theorem is not vacuous. Without the lock (`racyC`, both holes empty) the explorer
finds a finished, drained TSO state with counter `1`: an update is lost (`racy_lost`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Story

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Story.Counter

set_option maxRecDepth 100000 in
theorem spin_fin : (tsoStates 2 Prim.Clients.fuel Inst.spinC).any
    (fun c => c.doneB 2 && c.drainedB && Inst.countIs 2 c) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem racy_lost : (tsoStates 2 Prim.Clients.fuel Inst.racyC).any
    (fun c => c.doneB 2 && c.drainedB && Inst.countIs 1 c) = true := by decide +kernel

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

theorem memOf_cons (p : Nat × Nat) (l : List (Nat × Nat)) (a : Nat) :
    memOf (p :: l) a = if p.1 = a then some p.2 else memOf l a := by
  simp only [memOf, List.find?_cons]
  split <;> simp_all

theorem memOf_nil (a : Nat) : memOf [] a = none := rfl

theorem spinC_mem (a : Nat) :
    memOf Inst.cells a =
      Heap.union (mem 2) (Heap.union (Mutex.Spin.init m) Heap.empty) a := by
  by_cases hS : a = x ∨ a = m ∨ a = m + 4 ∨ a = permit 0 ∨ a = receipt 0 ∨ a = permit 1 ∨
      a = receipt 1
  · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [not_or] at hS
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hS
    have hT : ¬ (a = x ∨ isTok 2 a) := by
      simp only [isTok, x, permit, receipt, tb] at h1 h4 h5 h6 h7 ⊢; omega
    have e1 : memOf Inst.cells a = none := by
      simp [Inst.cells, memOf_cons, memOf_nil, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
        Ne.symm h5, Ne.symm h6, Ne.symm h7]
    rw [e1]
    simp only [union_apply, mem, hT, ite_false, Option.none_or, Mutex.Spin.init, Mutex.Spin.tok,
      single_apply, h2, h3, Heap.empty]

theorem spinC_th : Inst.spinC.th = fun t =>
    (if t < 2 then body (Mutex.spinMutex.lock 2) (Mutex.spinMutex.unlock 2) t else .skip,
      Regs.zero) := by
  funext t
  rcases t with _ | _ | t <;> simp [CSt.th, start, Inst.spinC, rget_rlist] <;> rfl

theorem racyC_th : Inst.racyC.th = fun t =>
    (if t < 2 then body Mutex.Inst.noOp Mutex.Inst.noOp t else .skip, Regs.zero) := by
  funext t
  rcases t with _ | _ | t <;> simp [CSt.th, start, Inst.racyC, rget_rlist]

/-- **The explorer instance is the linked counter client.** -/
theorem spinC_cfg : Inst.spinC.cfg = (client 2).link Mutex.spinMutex 2 := by
  simp only [CSt.cfg, Mutex.Client.link, Mutex.Client.startWith]
  congr 1
  · rw [spinC_th]; rfl
  · funext a; exact spinC_mem a

theorem racyC_mem (a : Nat) :
    memOf Inst.ownCells a = Heap.union (mem 2) Heap.empty a := by
  by_cases hS : a = x ∨ a = permit 0 ∨ a = receipt 0 ∨ a = permit 1 ∨ a = receipt 1
  · rcases hS with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [not_or] at hS
    obtain ⟨h1, h4, h5, h6, h7⟩ := hS
    have hT : ¬ (a = x ∨ isTok 2 a) := by
      simp only [isTok, x, permit, receipt, tb] at h1 h4 h5 h6 h7 ⊢; omega
    have e1 : memOf Inst.ownCells a = none := by
      simp [Inst.ownCells, memOf_cons, memOf_nil, Ne.symm h1, Ne.symm h4,
        Ne.symm h5, Ne.symm h6, Ne.symm h7]
    rw [e1]
    simp only [union_apply, mem, hT, ite_false, Option.none_or, Heap.empty]

/-- **The racy instance is the client with empty holes.** -/
theorem racyC_cfg :
    Inst.racyC.cfg = (client 2).startWith Mutex.Inst.noOp Mutex.Inst.noOp Heap.empty := by
  simp only [CSt.cfg, Mutex.Client.startWith]
  congr 1
  · rw [racyC_th]; rfl
  · funext a; exact racyC_mem a

end Silmaril.Proofs.X86.Concurrency.Story

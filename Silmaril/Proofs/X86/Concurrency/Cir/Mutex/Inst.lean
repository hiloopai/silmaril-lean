module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Spin

/-!
# Proofs: the explorer instances are the linked programs

The concrete configurations of `Mutex.Inst` (for the explorer) stand for the configurations of
`Mutex.Client`: `linkC` is `Even.client` linked with `spinMutex` at loop bound 2, `movC` the
start of `Task.movUnlock` for `Even.client`, and `racyC` `Even.client` with empty holes.
`rget_rlist` and `memOf_cons` are restated from `Proofs/…/Robust/Step.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Robust

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

theorem memOf_cons (p : Nat × Nat) (l : List (Nat × Nat)) (x : Nat) :
    memOf (p :: l) x = if p.1 = x then some p.2 else memOf l x := by
  simp only [memOf, List.find?_cons]
  split <;> simp_all

theorem memOf_nil (x : Nat) : memOf [] x = none := rfl

theorem start_th (lk ul : Expr → Stmt) (mem : List (Nat × Nat)) :
    (start (Inst.threads lk ul) mem).th =
      fun t => (if t < 2 then Even.body lk ul t else .skip, Regs.zero) := by
  funext t
  rcases t with _ | _ | t <;>
    simp [CSt.th, start, Inst.threads, rget_rlist]

/-- The five cells of the linked instances. -/
theorem mem5 (a : Nat) :
    memOf (Inst.cells ++ [(Even.m, 0), (Spin.tok Even.m, 0)]) a =
      Heap.union Even.mem (Heap.union (Spin.init Even.m) Heap.empty) a := by
  by_cases hS : a = 0x200 ∨ a = 0x300 ∨ a = 0x308 ∨ a = 0x100 ∨ a = 0x104
  · rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [not_or] at hS
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS
    simp [Inst.cells, memOf_cons, memOf_nil, Even.mem, Spin.init, Spin.tok, union_apply,
      single_apply, Heap.empty, Even.x, Even.out, Even.m, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4, Ne.symm h5, h1, h2, h3, h4, h5]

theorem linkC_cfg : Inst.linkC.cfg = Even.client.link spinMutex Inst.L := by
  simp only [CSt.cfg, Inst.linkC, Client.link, Client.startWith]
  congr 1
  · rw [start_th]; rfl
  · funext a; exact mem5 a

theorem movC_cfg : Inst.movC.cfg = Even.client.startWith
    (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body Inst.L))
    (fun a => .seq (.assign .rdi a) (movUnlockCode Inst.L))
    (Even.client.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty) := by
  simp only [CSt.cfg, Inst.movC, Client.startWith]
  congr 1
  · rw [start_th]; rfl
  · funext a; exact mem5 a

theorem racyC_cfg : Inst.racyC.cfg = Even.client.startWith Inst.noOp Inst.noOp Heap.empty := by
  simp only [CSt.cfg, Inst.racyC, Client.startWith]
  congr 1
  · rw [start_th]; rfl
  · funext a
    show memOf Inst.cells a = Heap.union Even.mem Heap.empty a
    rw [union_empty_right]
    by_cases hS : a = 0x200 ∨ a = 0x300 ∨ a = 0x308
    · rcases hS with rfl | rfl | rfl <;> rfl
    · simp only [not_or] at hS
      obtain ⟨h1, h2, h3⟩ := hS
      simp [Inst.cells, memOf_cons, memOf_nil, Even.mem, Even.x, Even.out, Ne.symm h1,
        Ne.symm h2, Ne.symm h3, h1, h2, h3]

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

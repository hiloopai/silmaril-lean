module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Static

/-!
# Process-level threads: the fork-join example

The hypotheses of `refines` hold for `Ex.forkJoin` (well-formed,
statically sync-safe), and the lowered process does take the `clone` step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)
open Silmaril.X86.Concurrency.Cir.Proc

theorem forkJoin_body (u : Nat) (h : 2 ≤ u) : Ex.forkJoin.body u = .skip := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [SProg.body, Ex.forkJoin]

theorem forkJoin_wf : Ex.forkJoin.Wf := by
  refine ⟨by decide, fun u => ?_, fun u => ?_, by decide⟩
  · rcases u with _ | _ | u
    · decide
    · decide
    · rw [forkJoin_body _ (by omega)]; rfl
  · show Ex.heap (ctlAddr u) = none
    unfold Ex.heap
    split
    · rename_i h; simp only [Ex.x, ctlAddr] at h; omega
    · rfl

theorem forkJoin_static : Ex.forkJoin.Static [Ex.x] := by
  refine ⟨fun a ha => ?_, by decide, by decide, by decide, by decide, by decide, by decide⟩
  simp only [List.mem_singleton] at ha; subst ha; simp [Ex.forkJoin, Ex.heap]

/-- The refinement applies to fork-join. -/
theorem forkJoin_refines (base : Base) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (Ex.forkJoin.code Ex.layout)).St}
    (h : PReach (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C) :
    ∃ A, SReach Ex.forkJoin Ex.forkJoin.init A ∧ Rel Ex.forkJoin Ex.layout C A :=
  refines forkJoin_wf (syncSafe_of_static forkJoin_static) tid0 tp0 h

/-- The lowered fork-join process takes the `clone` step: a new thread `tid0 + 1` with thread
pointer `tls 1` and `clear_child_tid = ctl 1`, whose tid is written at `ctl 1`. -/
theorem forkJoin_clone (base : Base) (tid0 : Nat) (h0 : tid0 + 1 < pidMax) (tp0 : Word) :
    ∃ C', PStep (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C' ∧
      (∃ r, C'.th (tid0 + 1) = some r ∧ r.tp = BitVec.ofNat 64 (Ex.layout.tls 1) ∧
        r.ctid = some (ctlAddr 1)) ∧ C'.mem (ctlAddr 1) = some (tid0 + 1) := by
  have hfl : CloneOk (BitVec.ofNat 64 cloneMusl) := Or.inl (by decide)
  have hct : (BitVec.ofNat 64 (ctlAddr 1)).toNat = ctlAddr 1 := by decide
  have hpt : (Ex.forkJoin.pheap (BitVec.ofNat 64 (ctlAddr 1)).toNat).isSome := by
    rw [hct, pheap_ctl (by decide) (by decide)]; rfl
  have hs : ∃ k ch, PTStep (Ex.forkJoin.code Ex.layout) tp0 (mainCode Ex.layout (Ex.forkJoin.body 0))
      Regs.zero (.sys nrClone [BitVec.ofNat 64 cloneMusl, BitVec.ofNat 64 (Ex.layout.stk 1),
        BitVec.ofNat 64 (ctlAddr 1), BitVec.ofNat 64 (ctlAddr 1), BitVec.ofNat 64 (Ex.layout.tls 1)]
        k ch) :=
    ⟨_, _, Or.inr ⟨_, Or.inr ⟨_, rfl, rfl⟩, rfl⟩⟩
  obtain ⟨k, ch, hs⟩ := hs
  have ht : (Ex.forkJoin.pinit Ex.layout tid0 tp0).th tid0 =
      some ⟨.run (mainCode Ex.layout (Ex.forkJoin.body 0), Regs.zero), tp0, none⟩ := by
    simp [SProg.pinit, PCfg.init]
  have hfresh : (Ex.forkJoin.pinit Ex.layout tid0 tp0).th (tid0 + 1) = none := by
    simp [SProg.pinit, PCfg.init]
  have step := @PStep.clone (pIsa (Ex.forkJoin.code Ex.layout)) base
    (Ex.forkJoin.pinit Ex.layout tid0 tp0) tid0
    ⟨.run (mainCode Ex.layout (Ex.forkJoin.body 0), Regs.zero), tp0, none⟩
    (mainCode Ex.layout (Ex.forkJoin.body 0), Regs.zero) _ _ _ _ _ [] k ch (tid0 + 1) rfl ht rfl
    hs hfl hfresh (by omega) h0 hpt
  refine ⟨_, step, ⟨_, by simp only [setTh, upd]; rfl, rfl, by simp only [hct]⟩, ?_⟩
  show heapPut Ex.forkJoin.pheap (BitVec.ofNat 64 (ctlAddr 1)).toNat (tid0 + 1) (ctlAddr 1) = _
  simp [heapPut, hct]

end Silmaril.Proofs.X86.Concurrency.Cir.Proc

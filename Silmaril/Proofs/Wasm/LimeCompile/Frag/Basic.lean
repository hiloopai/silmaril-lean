module

public import Silmaril.Wasm.LimeCompile.Container.Thms
public import Silmaril.Wasm.LimeCompile.Direct.Thms

/-!
# The numeric-select fragment and the two host conditions: proofs

* `selL_lowerL`, `selM_lowerModule`: erasing every `select` annotation after the direct lowering
  (which erases the numeric ones) is erasing every annotation;
* `selM_eq_of_lower`: so a module whose lowering is a Lime1 image `L.toCore` erases to `L.toCore`;
* `direct_compile_of_lower`: and the direct compiler returns `L` on it;
* `hostResp_of_parametric`: a code-parametric host respects `select` erasure (instantiate
  `HostParametric` at the reflexive relation "equal after erasure").

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Frag

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Select Silmaril.Wasm.LimeCompile.Direct
open Silmaril.Proofs.Wasm.LimeCompile.Select (selI_block selI_loop selI_if selI_tryTable selL_cons)

set_option linter.unusedTactic false in
mutual
/-- Erasure after lowering is erasure. -/
theorem selI_lowerI (i : Instr) : selI (lowerI i) = selI i := by
  cases i with
  | select ts =>
    cases ts with
    | none => rw [lowerI] <;> simp
    | some ts =>
      rw [lowerI]
      split <;> rfl
  | block bt b => rw [lowerI, selI_block, selI_block, selL_lowerL b]
  | loop bt b => rw [lowerI, selI_loop, selI_loop, selL_lowerL b]
  | if_ bt b₁ b₂ => rw [lowerI, selI_if, selI_if, selL_lowerL b₁, selL_lowerL b₂]
  | tryTable bt cs b => rw [lowerI, selI_tryTable, selI_tryTable, selL_lowerL b]
  | _ => rw [lowerI] <;> simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

theorem selL_lowerL (es : List Instr) : selL (lowerL es) = selL es := by
  cases es with
  | nil => rw [lowerL]
  | cons i es => rw [lowerL, selL_cons, selL_cons, selI_lowerI i, selL_lowerL es]
termination_by sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

/-- Erasure after lowering is erasure, on modules. -/
theorem selM_lowerModule (m : Module) : selM (lowerModule m) = selM m := by
  have hf : ∀ f : Func, selFn (lowerFunc f) = selFn f := fun f => by
    show (⟨f.type, f.locals, selL (lowerL f.body)⟩ : Func) = ⟨f.type, f.locals, selL f.body⟩
    rw [selL_lowerL]
  simp only [selM, lowerModule, List.map_map]
  congr 1
  exact List.map_congr_left fun f _ => hf f

/-- A module whose lowering is a Lime1 image erases to that image. -/
theorem selM_eq_of_lower {m : Module} {L : Lime1.Module} (h : L.toCore = lowerModule m) :
    L.toCore = selM m := by
  rw [← selM_lowerModule, ← h, Silmaril.Proofs.Wasm.LimeCompile.Container.selM_toCore]

/-- The direct compiler returns `L` on a module whose lowering is `L.toCore`. -/
theorem direct_compile_of_lower {m : Module} {L : Lime1.Module} (h : L.toCore = lowerModule m) :
    Silmaril.Wasm.LimeCompile.Direct.compile m = some L := by
  have hl := compile_lime L
  have hid : lowerModule L.toCore = L.toCore := (compile_toCore hl).symm
  unfold Silmaril.Wasm.LimeCompile.Direct.compile at hl ⊢
  rw [hid] at hl
  rw [← h]
  exact hl

/-! ## The two host conditions -/

variable {H : Type}

theorem forall₂_of_map_eq {α β : Type _} (f : α → β) :
    ∀ {l l' : List α}, l.map f = l'.map f → List.Forall₂ (fun a b => f a = f b) l l'
  | [], [], _ => .nil
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq f h.2)

theorem map_eq_of_forall₂ {α β : Type _} (f : α → β) :
    ∀ {l l' : List α}, List.Forall₂ (fun a b => f a = f b) l l' → l.map f = l'.map f
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.map_cons, List.map_cons, h, map_eq_of_forall₂ f t]

/-- Function instances equal after erasure. -/
abbrev SelF (f g : FuncInst H) : Prop := selFI f = selFI g

theorem storeRel_of_sel {s t : Store H} (h : selS s = selS t) : Sim.StoreRel SelF s t := by
  have hf : s.funcs.map selFI = t.funcs.map selFI := congrArg Store.funcs h
  refine ⟨?_, ?_, forall₂_of_map_eq selFI hf⟩
  · have := congrArg (List.map (FuncInst.type (H := H))) hf
    simpa [List.map_map, Function.comp_def, selFI] using this
  · have := congrArg (fun x : Store H => ({ x with funcs := [] } : Store H)) h
    simpa [selS] using this

theorem sel_of_storeRel {s t : Store H} (h : Sim.StoreRel SelF s t) : selS s = selS t := by
  have hf := map_eq_of_forall₂ selFI h.funcs
  have ho := h.other
  cases s
  cases t
  simp only [selS, Store.mk.injEq] at ho ⊢
  simp_all

/-- **A code-parametric host respects `select` erasure.** -/
theorem hostResp_of_parametric {host : HostSemantics H} (hp : Sim.HostParametric host) :
    HostResp host := by
  intro h s t vs o hst ho
  obtain ⟨o', ho', hr⟩ := hp SelF (fun _ => rfl) h s t vs o (storeRel_of_sel hst) ho
  refine ⟨o', ho', ?_⟩
  cases o with
  | diverged => cases o' <;> simp_all [Sim.OutcomeRel]
  | returned s₁ r =>
    cases o' with
    | diverged => simp_all [Sim.OutcomeRel]
    | returned s₂ r' =>
      simp only [Sim.OutcomeRel, Silmaril.Wasm.Execution.Host.Outcome.Sim] at hr ⊢
      exact ⟨sel_of_storeRel hr.1, hr.2⟩

end Silmaril.Proofs.Wasm.LimeCompile.Frag

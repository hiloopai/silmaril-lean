module

public import Silmaril.Wasm.Binaryen.MergeBackContext

@[expose] public section

/-! # Exact reference-rule matching for module merging

Reference tests and casts must take the same branch on both sides. Source
annotation scope makes their instantiated types equal, and related stores agree
on `RefOk`. This preserves the target's actual result without determinism.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

private theorem refTest_instRef {mode : Mode} {left right : ModuleInst}
    {rt₀ rt : RefType} (view : View mode left right)
    (rewrite : Instruction mode (.refTest rt₀) (.refTest rt))
    (scope : XI left (.refTest rt₀)) : left.instRef rt₀ = right.instRef rt := by
  cases mode with
  | same =>
    cases view
    change Instr.refTest rt₀ = Instr.refTest rt at rewrite
    cases rewrite
    rfl
  | relocated r =>
    cases view with
    | relocated views =>
      simp only [Instruction, instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
      obtain ⟨rt', hrt, heq⟩ := rewrite
      cases heq
      exact (ControlViews.closed_ref_type views hrt
        (by simpa only [CodeScope.Instruction] using scope.1)).symm

private theorem refCast_instRef {mode : Mode} {left right : ModuleInst}
    {rt₀ rt : RefType} (view : View mode left right)
    (rewrite : Instruction mode (.refCast rt₀) (.refCast rt))
    (scope : XI left (.refCast rt₀)) : left.instRef rt₀ = right.instRef rt := by
  cases mode with
  | same =>
    cases view
    change Instr.refCast rt₀ = Instr.refCast rt at rewrite
    cases rewrite
    rfl
  | relocated r =>
    cases view with
    | relocated views =>
      simp only [Instruction, instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
      obtain ⟨rt', hrt, heq⟩ := rewrite
      cases heq
      exact (ControlViews.closed_ref_type views hrt
        (by simpa only [CodeScope.Instruction] using scope.1)).symm

/-- Reconstruct the target's exact reference-rule result, including the chosen
success or failure of scoped reference tests and casts. -/
theorem reference_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target target' : Config H} (step : RefStep target target')
    (matching : Simulation.Matching mode source target)
    (scope : XAs source.frame.module source.code) :
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target' := by
  obtain ⟨s₀, f₀, X⟩ := source
  obtain ⟨s, f, Y⟩ := target
  have hco := matching.code
  cases step with
  | refNull ht =>
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain ⟨h₀, rfl⟩ := inv_refNull hr
    exact ⟨_, .reference (.refNull h₀), matching.stores, matching.frames, .ref .nil⟩
  | refFunc ha =>
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain ⟨x, rfl, hx⟩ := inv_refFunc matching.frames.view hr
      (xi_of_mem scope (by simp)) ha
    exact ⟨_, .reference (.refFunc hx), matching.stores, matching.frames, .ref .nil⟩
  | refI31 n =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.refI31 n), matching.stores, matching.frames, .ref .nil⟩
  | isNullTrue =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference .isNullTrue, matching.stores, matching.frames, .val .nil⟩
  | isNullFalse hn =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.isNullFalse hn), matching.stores, matching.frames, .val .nil⟩
  | asNonNullNull =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference .asNonNullNull, matching.stores, matching.frames, .trap .nil⟩
  | asNonNullAddr hn =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.asNonNullAddr hn), matching.stores, matching.frames, .ref .nil⟩
  | eqNull =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference .eqNull, matching.stores, matching.frames, .val .nil⟩
  | eqTrue hn =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.eqTrue hn), matching.stores, matching.frames, .val .nil⟩
  | eqFalse hn =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.eqFalse hn), matching.stores, matching.frames, .val .nil⟩
  | testTrue hok =>
    inv_head hco i hr
    obtain ⟨rt₀, rfl⟩ := inv_refTest hr
    have types := refTest_instRef matching.frames.view hr (xi_of_mem scope (by simp))
    have hok₀ := matching.stores.refOk_reverse hok
    rw [← types] at hok₀
    exact ⟨_, .reference (.testTrue hok₀), matching.stores, matching.frames, .val .nil⟩
  | @testFalse _ _ r rt hok =>
    inv_head hco i hr
    obtain ⟨rt₀, rfl⟩ := inv_refTest hr
    have types := refTest_instRef matching.frames.view hr (xi_of_mem scope (by simp))
    have hok₀ : ¬ RefOk s₀ r (f₀.module.instRef rt₀) := by
      rw [types]
      exact fun h => hok (matching.stores.refOk h)
    exact ⟨_, .reference (.testFalse hok₀), matching.stores, matching.frames, .val .nil⟩
  | castSucceed hok =>
    inv_head hco i hr
    obtain ⟨rt₀, rfl⟩ := inv_refCast hr
    have types := refCast_instRef matching.frames.view hr (xi_of_mem scope (by simp))
    have hok₀ := matching.stores.refOk_reverse hok
    rw [← types] at hok₀
    exact ⟨_, .reference (.castSucceed hok₀), matching.stores, matching.frames, .ref .nil⟩
  | @castFail _ _ r rt hok =>
    inv_head hco i hr
    obtain ⟨rt₀, rfl⟩ := inv_refCast hr
    have types := refCast_instRef matching.frames.view hr (xi_of_mem scope (by simp))
    have hok₀ : ¬ RefOk s₀ r (f₀.module.instRef rt₀) := by
      rw [types]
      exact fun h => hok (matching.stores.refOk h)
    exact ⟨_, .reference (.castFail hok₀), matching.stores, matching.frames, .trap .nil⟩
  | i31GetNull sx =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.i31GetNull sx), matching.stores, matching.frames, .trap .nil⟩
  | i31GetNum sx n =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.i31GetNum sx n), matching.stores, matching.frames, .val .nil⟩
  | externConvertNull =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference .externConvertNull, matching.stores, matching.frames, .ref .nil⟩
  | externConvertAddr hn =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.externConvertAddr hn), matching.stores, matching.frames, .ref .nil⟩
  | anyConvertNull =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference .anyConvertNull, matching.stores, matching.frames, .ref .nil⟩
  | anyConvertAddr r =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .reference (.anyConvertAddr r), matching.stores, matching.frames, .ref .nil⟩

theorem BackwardStep.reference {P : Profile} {host : HostSemantics H}
    {target target' : Config H} (step : RefStep target target') :
    BackwardStep P host target target' := by
  intro mode source matching scope
  exact reference_back_matching step matching scope

end Silmaril.Wasm.Binaryen.MergeUntyped

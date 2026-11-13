module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.Fwd

/-!
# Exception renaming for `StepFX'`: reading renamed code back

The backward simulation starts from a step of a renamed configuration, whose code is given as
the shape of a rule, `shape = rnL n L`. These lemmas read such an equation back, one piece of
the shape at a time: `L` has the same shape, with renamed pieces (`inv_app`, `inv_fv_app`,
`inv_one`, `inv_two`, `inv_label`, …).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV Silmaril.Wasm.Models.FXRenameVSim
open Silmaril.Proofs.Wasm.Models.FXRenameSim (rnAdmin_eq_constI32_iff rnAdmin_eq_trap_iff
  rnAdmin_eq_ref_iff rnRef_eq_null_iff rnRef_eq_func_iff)

variable {n : Nat} {L : List AdminFX} {a : AdminFX}

theorem inv_app {A B : List AdminFX} (h : A ++ B = rnL n L) :
    ∃ L₁ L₂, L = L₁ ++ L₂ ∧ A = rnL n L₁ ∧ B = rnL n L₂ := by
  obtain ⟨L₁, L₂, hL, h₁, h₂⟩ := rnL_eq_append_iff.mp h.symm
  exact ⟨L₁, L₂, hL, h₁.symm, h₂.symm⟩

theorem inv_fv {vs : List FVal} (h : fvals vs = rnL n L) :
    ∃ vs₀, L = fvals vs₀ ∧ vs = vs₀.map (rnFV n) := by
  obtain ⟨vs₀, hL, hv⟩ := rnL_eq_fvals_iff.mp h.symm
  exact ⟨vs₀, hL, hv.symm⟩

theorem inv_fv_app {vs : List FVal} {T : List AdminFX} (h : fvals vs ++ T = rnL n L) :
    ∃ vs₀ L', L = fvals vs₀ ++ L' ∧ vs = vs₀.map (rnFV n) ∧ T = rnL n L' := by
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := inv_app h
  obtain ⟨vs₀, rfl, hv⟩ := inv_fv h₁
  exact ⟨vs₀, L₂, rfl, hv, h₂⟩

theorem inv_cv {vs : List Val} (h : cvals vs = rnL n L) :
    ∃ vs₀, L = cvals vs₀ ∧ vs = vs₀.map (rnVal n) := by
  obtain ⟨vs₀, hL, hv⟩ := rnL_eq_cvals_iff.mp h.symm
  exact ⟨vs₀, hL, hv.symm⟩

theorem inv_cthrowing {b : Nat} (h : cthrowing b = rnL n L) :
    ∃ a₀, L = cthrowing a₀ ∧ b = rnIdx n a₀ := by
  obtain ⟨a₀, hL, hb⟩ := rnL_eq_cthrowing_iff.mp h.symm
  exact ⟨a₀, hL, hb.symm⟩

theorem inv_instrs {b : List InstrFX} (h : b.map InstrFX.toAdmin = rnL n L) :
    L = b.map InstrFX.toAdmin :=
  rnL_eq_instrs_iff.mp h.symm

theorem inv_nil (h : [] = rnL n L) : L = [] := rnL_eq_nil_iff.mp h.symm

theorem inv_one {b : AdminFX} (h : [b] = rnL n L) : ∃ a₀, L = [a₀] ∧ b = rnA n a₀ := by
  obtain ⟨a₀, hL, ha⟩ := rnL_eq_singleton_iff.mp h.symm
  exact ⟨a₀, hL, ha.symm⟩

theorem inv_two {b c : AdminFX} (h : [b, c] = rnL n L) :
    ∃ a₀ c₀, L = [a₀, c₀] ∧ b = rnA n a₀ ∧ c = rnA n c₀ := by
  obtain ⟨a₀, L₀, rfl, ha, hL⟩ := rnL_eq_cons_iff.mp h.symm
  obtain ⟨c₀, rfl, hc⟩ := rnL_eq_singleton_iff.mp hL
  exact ⟨a₀, c₀, rfl, ha.symm, hc.symm⟩

theorem inv_plain {i : Instr} (h : AdminFX.core (.plain i) = rnA n a) : a = .core (.plain i) :=
  rnA_eq_plain_iff.mp h.symm

theorem inv_const {c : BitVec 32} (h : AdminFX.core (constI32 c) = rnA n a) :
    a = .core (constI32 c) := by
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_core_iff.mp h.symm
  rw [rnAdmin_eq_constI32_iff.mp hb]

theorem inv_trap (h : AdminFX.core .trap = rnA n a) : a = .core .trap := by
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_core_iff.mp h.symm
  rw [rnAdmin_eq_trap_iff.mp hb]

theorem inv_refNull (h : AdminFX.core (.ref .null) = rnA n a) : a = .core (.ref .null) := by
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_core_iff.mp h.symm
  obtain ⟨r₀, rfl, hr⟩ := rnAdmin_eq_ref_iff.mp hb
  rw [rnRef_eq_null_iff.mp hr]

theorem inv_refFunc {fa : Nat} (h : AdminFX.core (.ref (.func fa)) = rnA n a) :
    a = .core (.ref (.func fa)) := by
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_core_iff.mp h.symm
  obtain ⟨r₀, rfl, hr⟩ := rnAdmin_eq_ref_iff.mp hb
  rw [rnRef_eq_func_iff.mp hr]

theorem inv_fx {i : FXInstr} (h : AdminFX.fx i = rnA n a) : a = .fx i := rnA_eq_fx_iff.mp h.symm

theorem inv_contRef {k : Nat} (h : AdminFX.contRef k = rnA n a) : a = .contRef k :=
  rnA_eq_contRef_iff.mp h.symm

theorem inv_block {bt : BlockType} {b : List InstrFX} (h : AdminFX.block bt b = rnA n a) :
    a = .block bt b := rnA_eq_block_iff.mp h.symm

theorem inv_loop {bt : BlockType} {b : List InstrFX} (h : AdminFX.loop bt b = rnA n a) :
    a = .loop bt b := rnA_eq_loop_iff.mp h.symm

theorem inv_if {bt : BlockType} {b₁ b₂ : List InstrFX} (h : AdminFX.if_ bt b₁ b₂ = rnA n a) :
    a = .if_ bt b₁ b₂ := rnA_eq_if_iff.mp h.symm

theorem inv_label {m : Nat} {k : List InstrFX} {B : List AdminFX}
    (h : [AdminFX.label m k B] = rnL n L) : ∃ B₀, L = [.label m k B₀] ∧ B = rnL n B₀ := by
  obtain ⟨a₀, rfl, ha⟩ := inv_one h
  obtain ⟨B₀, rfl, hB⟩ := rnA_eq_label_iff.mp ha.symm
  exact ⟨B₀, rfl, hB.symm⟩

theorem inv_frame {m : Nat} {fi : Frame} {B : List AdminFX}
    (h : [AdminFX.frame m fi B] = rnL n L) :
    ∃ fi₀ B₀, L = [.frame m fi₀ B₀] ∧ fi = rnFrame n fi₀ ∧ B = rnL n B₀ := by
  obtain ⟨a₀, rfl, ha⟩ := inv_one h
  obtain ⟨fi₀, B₀, rfl, hfi, hB⟩ := rnA_eq_frame_iff.mp ha.symm
  exact ⟨fi₀, B₀, rfl, hfi.symm, hB.symm⟩

theorem inv_handler {hs : List HClause} {B : List AdminFX}
    (h : [AdminFX.handler hs B] = rnL n L) : ∃ B₀, L = [.handler hs B₀] ∧ B = rnL n B₀ := by
  obtain ⟨a₀, rfl, ha⟩ := inv_one h
  obtain ⟨B₀, rfl, hB⟩ := rnA_eq_handler_iff.mp ha.symm
  exact ⟨B₀, rfl, hB.symm⟩

/-- Renamed code `fvals vs ++ [x]` is `fvals vs₀ ++ [x₀]`. -/
theorem inv_fv_one {vs : List FVal} {b : AdminFX} (h : fvals vs ++ [b] = rnL n L) :
    ∃ vs₀ a₀, L = fvals vs₀ ++ [a₀] ∧ vs = vs₀.map (rnFV n) ∧ b = rnA n a₀ := by
  obtain ⟨vs₀, L', rfl, hv, hL⟩ := inv_fv_app h
  obtain ⟨a₀, rfl, ha⟩ := inv_one hL
  exact ⟨vs₀, a₀, rfl, hv, ha⟩

/-- Renamed code `fvals vs ++ [x, y]` is `fvals vs₀ ++ [x₀, y₀]`. -/
theorem inv_fv_two {vs : List FVal} {b c : AdminFX} (h : fvals vs ++ [b, c] = rnL n L) :
    ∃ vs₀ a₀ c₀, L = fvals vs₀ ++ [a₀, c₀] ∧ vs = vs₀.map (rnFV n) ∧ b = rnA n a₀ ∧
      c = rnA n c₀ := by
  obtain ⟨vs₀, L', rfl, hv, hL⟩ := inv_fv_app h
  obtain ⟨a₀, c₀, rfl, ha, hc⟩ := inv_two hL
  exact ⟨vs₀, a₀, c₀, rfl, hv, ha, hc⟩

/-- Renamed code `fvals vs ++ [x] ++ rest` is `fvals vs₀ ++ [x₀] ++ rest₀`. -/
theorem inv_fv_one_app {vs : List FVal} {b : AdminFX} {R : List AdminFX}
    (h : fvals vs ++ [b] ++ R = rnL n L) :
    ∃ vs₀ a₀ R₀, L = fvals vs₀ ++ [a₀] ++ R₀ ∧ vs = vs₀.map (rnFV n) ∧ b = rnA n a₀ ∧
      R = rnL n R₀ := by
  obtain ⟨L₁, R₀, rfl, h₁, hR⟩ := inv_app h
  obtain ⟨vs₀, a₀, rfl, hv, ha⟩ := inv_fv_one h₁
  exact ⟨vs₀, a₀, R₀, rfl, hv, ha, hR⟩

/-- Renamed code `fvals vs ++ cthrowing a ++ rest`. -/
theorem inv_fv_throw_app {vs : List FVal} {b : Nat} {R : List AdminFX}
    (h : fvals vs ++ cthrowing b ++ R = rnL n L) :
    ∃ vs₀ a₀ R₀, L = fvals vs₀ ++ cthrowing a₀ ++ R₀ ∧ vs = vs₀.map (rnFV n) ∧
      b = rnIdx n a₀ ∧ R = rnL n R₀ := by
  obtain ⟨L₁, R₀, rfl, h₁, hR⟩ := inv_app h
  obtain ⟨vs₀, L₂, rfl, hv, h₂⟩ := inv_fv_app h₁
  obtain ⟨a₀, rfl, hb⟩ := inv_cthrowing h₂
  exact ⟨vs₀, a₀, R₀, rfl, hv, hb, hR⟩

/-- Renamed code under a context: `[handler hs (E.plug X)]`. -/
theorem inv_handler_plug {hs : List HClause} {E : CtxV} {X : List AdminFX}
    (h : [AdminFX.handler hs (E.plug X)] = rnL n L) :
    ∃ E₀ X₀, L = [.handler hs (E₀.plug X₀)] ∧ E = rnCtx n E₀ ∧ X = rnL n X₀ := by
  obtain ⟨B₀, rfl, hB⟩ := inv_handler h
  obtain ⟨E₀, X₀, rfl, hE, hX⟩ := rnL_eq_plug_iff hB.symm
  exact ⟨E₀, X₀, rfl, hE.symm, hX.symm⟩

theorem map_rnFV_ne_nil {vs : List FVal} : vs.map (rnFV n) ≠ [] ↔ vs ≠ [] := by simp

end Silmaril.Proofs.Wasm.Models.FXRenameVSim

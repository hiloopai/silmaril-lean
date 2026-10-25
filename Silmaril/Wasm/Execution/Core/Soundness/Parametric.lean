module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.PureRedex

@[expose] public section

/-! # Soundness, parametric family

Preservation of `ParametricStep` (a pure family: store and frame unchanged) and
progress for `ParametricInstrOk`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- **Preservation (parametric).** A pure redex and its reduct have the same type. -/
theorem ParametricStep.preservation {s : Store H} {f : Frame} {C : Context}
    {is is' : List Admin} {it : InstrType} (_hst : StateOk s f C)
    (hty : AdminsOk s C is it) (h : ParametricStep is is') : AdminsOk s C is' it := by
  cases h with
  | unreachable =>
    refine AdminsOk.pure_redex (vs := []) (i := .unreachable) (by intros; simp) ?_ hty
    intro C A' tvs it xs₂ B hi hp hf D
    cases hf
    cases hi <;> rename_i hi <;> cases hi
    rename_i hok
    · simp only [List.append_nil] at hp; subst hp
      exact AdminsOk.trap_cons hok.1 hok.2.1 D
  | nop =>
    refine AdminsOk.pure_redex (vs := []) (i := .nop) (by intros; simp) ?_ hty
    intro C A' tvs it xs₂ B hi hp hf D
    cases hf
    cases hi <;> rename_i hi <;> cases hi
    · simp only [List.append_nil] at hp; subst hp
      exact D
  | drop v =>
    refine AdminsOk.pure_redex (vs := [v]) (i := .drop) ?_ ?_ hty
    · intro C it hi
      cases hi <;> rename_i hi <;> cases hi
      simp
    · intro C A' tvs it xs₂ B hi hp hf D
      cases hi <;> rename_i hi <;> cases hi
      · obtain ⟨rfl, rfl⟩ := params_split hp (by simp [← hf.length_eq])
        exact D
  | selectTrue hc =>
    rename_i v₁ v₂ c ts
    refine AdminsOk.pure_redex (vs := [v₁, v₂, Val.i32 c]) (i := .select ts) ?_ ?_ hty
    · intro C it hi
      cases hi <;> rename_i hi <;> cases hi <;> simp
    · intro C A' tvs it xs₂ B hi hp hf D
      cases hi <;> rename_i hi <;> cases hi
      all_goals
        obtain ⟨rfl, rfl⟩ := params_split hp (by simp [← hf.length_eq])
        simp only [List.forall₂_cons] at hf
        exact AdminsOk.fits_cons hf.1 D
  | selectFalse v₁ v₂ ts =>
    refine AdminsOk.pure_redex (vs := [v₁, v₂, Val.i32 0]) (i := .select ts) ?_ ?_ hty
    · intro C it hi
      cases hi <;> rename_i hi <;> cases hi <;> simp
    · intro C A' tvs it xs₂ B hi hp hf D
      cases hi <;> rename_i hi <;> cases hi
      all_goals
        obtain ⟨rfl, rfl⟩ := params_split hp (by simp [← hf.length_eq])
        simp only [List.forall₂_cons] at hf
        exact AdminsOk.fits_cons hf.2.1 D

/-- **Progress (parametric).** A well-typed instruction of this family, applied to
operands of its parameter types, reduces. -/
theorem ParametricInstrOk.progress {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val}
    (_hst : StateOk s f C) (hi : ParametricInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | nop => cases hvs; exact ⟨_, .parametric .nop⟩
  | unreachable _ => exact Step.under_vals vs (.parametric .unreachable)
  | drop _ =>
    rcases hvs with _ | ⟨_, _ | _⟩
    exact ⟨_, .parametric (.drop _)⟩
  | selectExpl _ =>
    rcases hvs with _ | ⟨_, _ | ⟨_, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨b, rfl⟩ := ValOk.num_inv (nt := .int .i32) h3
    by_cases hb : b = 0
    · subst hb; exact ⟨_, .parametric (.selectFalse _ _ _)⟩
    · exact ⟨_, .parametric (.selectTrue hb)⟩
  | selectImpl _ _ _ =>
    rcases hvs with _ | ⟨_, _ | ⟨_, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨b, rfl⟩ := ValOk.num_inv (nt := .int .i32) h3
    by_cases hb : b = 0
    · subst hb; exact ⟨_, .parametric (.selectFalse _ _ _)⟩
    · exact ⟨_, .parametric (.selectTrue hb)⟩

end Silmaril.Wasm.Execution.Core

module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Hyp

/-!
# Progress for `envP`: canonical forms and steps in context

* `vty_int`, `vty_exn`, `vty_cont`, `vty_val`, `vty_ntP`: the values at a type of `envP`.
* `valsTy_split`, `valsTy_append`: typed value sequences split along their types.
* `step_ctx`: a step of `fvals vs₂ ++ w` is a step under more values and more code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {s : Store H} {Γ : List TypeIdx}

/-! ## Canonical forms -/

theorem ctI_val_out {w : Val} {t : FTy} (h : CtI s w.toAdmin [] [t]) :
    (∃ it x, w = .num ⟨.int it, x⟩ ∧ t = intTy it) ∨
      (∃ a, w = .ref (.exn a) ∧ a < s.exns.length ∧ t = exnTy) := by
  cases w with
  | num nv =>
    obtain ⟨ty, x⟩ := nv
    cases ty with
    | int it =>
      cases h with
      | intConst => exact .inl ⟨it, x, rfl, rfl⟩
    | float ft => cases h
  | vec b => cases h
  | ref r =>
    cases r <;> cases h
    exact .inr ⟨_, rfl, by assumption, rfl⟩

theorem intTy_ne_exnTy {it : IntType} : intTy it ≠ exnTy := by
  intro h
  simp only [intTy, exnTy, FTy.val.injEq] at h
  cases h

theorem vty_int {v : FVal} {it : IntType} (h : VTy (envP m₀) s Γ v (intTy it)) :
    ∃ x, v = .val (.num ⟨.int it, x⟩) := by
  cases v with
  | val w =>
    rcases ctI_val_out h with ⟨it', x, rfl, he⟩ | ⟨a, -, -, he⟩
    · simp only [intTy, FTy.val.injEq, Ty.num.injEq, NumType.int.injEq] at he
      subst he
      exact ⟨x, rfl⟩
    · exact absurd he intTy_ne_exnTy
  | cont k =>
    obtain ⟨ct, -, he⟩ := h
    simp [intTy] at he

theorem vty_exn {v : FVal} (h : VTy (envP m₀) s Γ v exnTy) :
    ∃ a, v = .val (.ref (.exn a)) ∧ a < s.exns.length := by
  cases v with
  | val w =>
    rcases ctI_val_out h with ⟨it, x, -, he⟩ | ⟨a, rfl, ha, -⟩
    · exact absurd he.symm intTy_ne_exnTy
    · exact ⟨a, rfl, ha⟩
  | cont k =>
    obtain ⟨ct, -, he⟩ := h
    simp [exnTy] at he

theorem vty_cont {v : FVal} {ct : TypeIdx} (h : VTy (envP m₀) s Γ v (.cont ct)) :
    ∃ k, v = .cont k ∧ Γ[k]? = some ct := by
  cases v with
  | val w =>
    rcases ctI_val_out h with ⟨it, x, -, he⟩ | ⟨a, -, -, he⟩ <;> simp [intTy, exnTy] at he
  | cont k =>
    obtain ⟨ct', hk, he⟩ := h
    cases he
    exact ⟨k, rfl, hk⟩

theorem vty_val {v : FVal} {t : CValType} (h : VTy (envP m₀) s Γ v (.val t)) :
    ∃ w, v = .val w := by
  cases v with
  | val w => exact ⟨w, rfl⟩
  | cont k =>
    obtain ⟨ct, -, he⟩ := h
    cases he

theorem vty_ntP {v : FVal} {ct : TypeIdx} (h : VTy (envP m₀) s Γ v (ntP ct)) : False := by
  cases v with
  | val w =>
    rcases ctI_val_out h with ⟨it, x, -, he⟩ | ⟨a, -, -, he⟩ <;>
      simp only [intTy, exnTy, ntP, FTy.val.injEq] at he <;> cases he
  | cont k =>
    obtain ⟨ct', -, he⟩ := h
    simp [ntP] at he

/-- Values typed by `vtys` are Core values. -/
theorem valsTy_core {vs : List FVal} {ts : List CValType}
    (h : ValsTy (envP m₀) s Γ vs (vtys ts)) : ∃ ws, vs = liftV ws := by
  induction ts generalizing vs with
  | nil =>
    cases h
    exact ⟨[], rfl⟩
  | cons t ts ih =>
    cases h with
    | cons hv hr =>
      obtain ⟨w, rfl⟩ := vty_val hv
      obtain ⟨ws, rfl⟩ := ih hr
      exact ⟨w :: ws, rfl⟩

/-! ## Value sequences -/

theorem valsTy_split {vs : List FVal} {a b : List FTy} (h : ValsTy (envP m₀) s Γ vs (a ++ b)) :
    ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ ValsTy (envP m₀) s Γ vs₁ a ∧ ValsTy (envP m₀) s Γ vs₂ b := by
  induction a generalizing vs with
  | nil => exact ⟨[], vs, rfl, .nil, h⟩
  | cons t a ih =>
    cases h with
    | cons hv hr =>
      obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := ih hr
      exact ⟨_ :: vs₁, vs₂, rfl, .cons hv h₁, h₂⟩

theorem valsTy_append {vs₁ vs₂ : List FVal} {a b : List FTy}
    (h₁ : ValsTy (envP m₀) s Γ vs₁ a) (h₂ : ValsTy (envP m₀) s Γ vs₂ b) :
    ValsTy (envP m₀) s Γ (vs₁ ++ vs₂) (a ++ b) :=
  List.rel_append h₁ h₂

theorem valsTy_length {vs : List FVal} {a : List FTy} (h : ValsTy (envP m₀) s Γ vs a) :
    vs.length = a.length :=
  h.length_eq

/-! ## Steps in context -/

variable {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- A step of a window is a step under more values before it and more code after it. -/
theorem step_ctx {K : List (Option ContFX)} {f : Frame} {w : List AdminFX}
    (vs : List FVal) (rest : List AdminFX)
    (h : ∃ c', StepFXS P host fx ⟨s, K, f, w⟩ c') :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs ++ w ++ rest⟩ c' := by
  obtain ⟨⟨s', K', f', w'⟩, hw⟩ := h
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact ⟨_, .seq hw hne⟩
  · have hvs : vs = [] ∧ rest = [] := by simpa using hne
    obtain ⟨rfl, rfl⟩ := hvs
    exact ⟨_, by simpa [fvals] using hw⟩

theorem fvals_append (a b : List FVal) : fvals (a ++ b) = fvals a ++ fvals b :=
  List.map_append

end Silmaril.Proofs.Wasm.Models.FXPresI

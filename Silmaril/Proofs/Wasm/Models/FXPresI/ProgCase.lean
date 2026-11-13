module

public import Silmaril.Proofs.Wasm.Models.FXPresI.ProgBase

/-!
# Progress for `envP`: the instruction cases

`PG ... code i`: for every frame of module `m₀` and values `vs` typed by `i`, `fvals vs ++ code`
halts (`Halt`) or steps. One lemma per head instruction of `TL`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {s : Store H} {Γ : List TypeIdx}
  {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} {K : List (Option ContFX)}

/-- The progress motive. -/
def PG (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (m₀ : ModuleInst)
    (s : Store H) (Γ : List TypeIdx) (K : List (Option ContFX)) (code : List AdminFX)
    (i : List FTy) : Prop :=
  ∀ (f : Frame) (vs : List FVal), f.module = m₀ → ValsTy (envP m₀) s Γ vs i →
    Halt s K f (fvals vs ++ code) ∨ ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs ++ code⟩ c'

theorem pg_nil {i : List FTy} : PG P host fx m₀ s Γ K [] i :=
  fun _ vs _ _ => .inl (by simpa using Halt.vals vs)

/-- A value: push it. -/
theorem pg_push {v : FVal} {t : FTy} {as : List AdminFX} {i : List FTy}
    (hv : VTy (envP m₀) s Γ v t) (ih : PG P host fx m₀ s Γ K as (i ++ [t])) :
    PG P host fx m₀ s Γ K (v.toAdmin :: as) i := by
  intro f vs hf hvs
  have h := ih f (vs ++ [v]) hf (valsTy_append hvs (.cons hv .nil))
  simpa [fvals_append, fvals] using h

/-- An instruction whose operands step. -/
theorem pg_win {x : AdminFX} {as : List AdminFX} {pre i₀ : List FTy}
    (hw : ∀ (f : Frame) (vs₂ : List FVal), f.module = m₀ → ValsTy (envP m₀) s Γ vs₂ i₀ →
      ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [x]⟩ c') :
    PG P host fx m₀ s Γ K (x :: as) (pre ++ i₀) := by
  intro f vs hf hvs
  obtain ⟨vs₁, vs₂, rfl, -, h₂⟩ := valsTy_split hvs
  have h := step_ctx vs₁ as (hw f vs₂ hf h₂)
  right
  simpa [fvals_append, List.append_assoc] using h

/-- An instruction that steps on its own, under any operands. -/
theorem pg_alone {x : AdminFX} {as : List AdminFX} {i : List FTy}
    (hw : ∀ (f : Frame), ∃ c', StepFXS P host fx ⟨s, K, f, [x]⟩ c') :
    PG P host fx m₀ s Γ K (x :: as) i := by
  have h := pg_win (as := as) (pre := []) (i₀ := i) (m₀ := m₀) (s := s) (Γ := Γ) (K := K)
    (P := P) (host := host) (fx := fx) fun f vs₂ _ _ => by
      simpa using step_ctx vs₂ [] (hw f)
  simpa using h

/-! ## Core instructions -/

theorem step_unop {f : Frame} {t : IntType} {op : IntUnOp} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [intTy t]) :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [.core (.plain (.intUnOp t op))]⟩ c' := by
  obtain ⟨v, rfl⟩ : ∃ v, vs₂ = [v] := by cases h with | cons _ h => cases h; exact ⟨_, rfl⟩
  obtain ⟨x, rfl⟩ := vty_int (List.forall₂_cons.1 h).1
  exact ⟨_, .core (cs := [.plain (.intConst t x), .plain (.intUnOp t op)]) (.numeric .intUnOp)⟩

theorem step_testop {f : Frame} {t : IntType} {op : IntTestOp} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [intTy t]) :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [.core (.plain (.intTestOp t op))]⟩ c' := by
  obtain ⟨v, rfl⟩ : ∃ v, vs₂ = [v] := by cases h with | cons _ h => cases h; exact ⟨_, rfl⟩
  obtain ⟨x, rfl⟩ := vty_int (List.forall₂_cons.1 h).1
  exact ⟨_, .core (cs := [.plain (.intConst t x), .plain (.intTestOp t op)]) (.numeric .intTestOp)⟩

theorem two_ints {t : IntType} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [intTy t, intTy t]) :
    ∃ x y, vs₂ = [.val (.num ⟨.int t, x⟩), .val (.num ⟨.int t, y⟩)] := by
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ h =>
      cases h
      obtain ⟨x, rfl⟩ := vty_int h₁
      obtain ⟨y, rfl⟩ := vty_int h₂
      exact ⟨x, y, rfl⟩

theorem step_binop {f : Frame} {t : IntType} {op : IntBinOp} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [intTy t, intTy t]) :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [.core (.plain (.intBinOp t op))]⟩ c' := by
  obtain ⟨x, y, rfl⟩ := two_ints h
  cases hr : Silmaril.Wasm.Numerics.intBinOp t op x y with
  | ok z => exact ⟨_, .core (cs := [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]) (.numeric (.intBinOp hr))⟩
  | error e => exact ⟨_, .core (cs := [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]) (.numeric (.intBinOpTrap hr))⟩

theorem step_relop {f : Frame} {t : IntType} {op : IntRelOp} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [intTy t, intTy t]) :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [.core (.plain (.intRelOp t op))]⟩ c' := by
  obtain ⟨x, y, rfl⟩ := two_ints h
  exact ⟨_, .core (cs := [.plain (.intConst t x), .plain (.intConst t y),
    .plain (.intRelOp t op)]) (.numeric .intRelOp)⟩

theorem step_drop {f : Frame} {x : FTy} {vs₂ : List FVal}
    (h : ValsTy (envP m₀) s Γ vs₂ [x]) :
    ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs₂ ++ [.core (.plain .drop)]⟩ c' := by
  obtain ⟨v, rfl⟩ : ∃ v, vs₂ = [v] := by cases h with | cons _ h => cases h; exact ⟨_, rfl⟩
  cases v with
  | val w => exact ⟨_, .core (cs := [w.toAdmin, .plain .drop]) (.parametric (.drop w))⟩
  | cont k => exact ⟨_, .dropCont⟩

/-- `trap`: halts alone, otherwise discards its context. -/
theorem pg_trap {as : List AdminFX} {i : List FTy} :
    PG P host fx m₀ s Γ K (.core .trap :: as) i := by
  intro f vs _ _
  by_cases hne : vs ≠ [] ∨ as ≠ []
  · have hs := StepFXS.trapSeq (P := P) (host := host) (fx := fx) (s := s) (K := K) (f := f)
      (vs := vs) (rest := as) hne
    exact .inr ⟨_, by simpa using hs⟩
  · have hvs : vs = [] ∧ as = [] := by simpa using hne
    obtain ⟨rfl, rfl⟩ := hvs
    exact .inl (by simpa [fvals] using Halt.trap (s := s) (K := K) (f := f))

/-- `throw_ref` on `ref.exn a`: halts alone, otherwise discards its context. -/
theorem pg_throwRef {as : List AdminFX} {pre i₁ : List FTy} :
    PG P host fx m₀ s Γ K (.core (.plain .throwRef) :: as) (pre ++ (i₁ ++ [exnTy])) := by
  intro f vs _ hvs
  rw [← List.append_assoc] at hvs
  obtain ⟨vs₁, vs₂, rfl, -, h₂⟩ := valsTy_split hvs
  obtain ⟨v, rfl⟩ : ∃ v, vs₂ = [v] := by cases h₂ with | cons _ h => cases h; exact ⟨_, rfl⟩
  obtain ⟨a, rfl, -⟩ := vty_exn (List.forall₂_cons.1 h₂).1
  have hcode : fvals (vs₁ ++ [.val (.ref (.exn a))]) ++ .core (.plain .throwRef) :: as =
      fvals vs₁ ++ cthrowing a ++ as := by simp [fvals, cthrowing, FVal.toAdmin, Val.toAdmin]
  rw [hcode]
  by_cases hne : vs₁ ≠ [] ∨ as ≠ []
  · exact .inr ⟨_, .throwSeq hne⟩
  · have hvs : vs₁ = [] ∧ as = [] := by simpa using hne
    obtain ⟨rfl, rfl⟩ := hvs
    exact .inl (by simpa [fvals] using Halt.throw (s := s) (K := K) (f := f) a)

end Silmaril.Proofs.Wasm.Models.FXPresI

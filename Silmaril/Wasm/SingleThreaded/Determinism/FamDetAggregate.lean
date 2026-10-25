module

public import Silmaril.Wasm.SingleThreaded.Determinism.FamDet

@[expose] public section

/-! # Determinism of the `AggregateStep` family in the deterministic profile -/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

variable {H : Type}

set_option maxHeartbeats 4000000 in
theorem AggregateStep.det {s : Store H} {f : Frame}
    {l₁ l₂ : List Admin} {c₁ c₂ : Config H} {p : List Val}
    (h₁ : AggregateStep ⟨s, f, l₁⟩ c₁) (h₂ : AggregateStep ⟨s, f, l₂⟩ c₂) (hl : l₁ = vals p ++ l₂) :
    p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂
  all_goals try (fam_pre <;> fam_post)
  case structNew.structNew =>
    rename_i x₁ d₁ fs₁ vs₁ he₁ hn₁ hp₁ hd₁ x₂ d₂ fs₂ vs₂ he₂ hn₂ hp₂ hd₂
    rw [← List.append_assoc, ← vals_append, append_singleton_inj] at hl
    obtain ⟨hv, hx⟩ := hl
    simp only [Admin.plain.injEq, Instr.structNew.injEq] at hx
    subst hx
    rw [vals_inj] at hv
    subst hv
    rw [hd₁] at hd₂
    cases hd₂
    cases Expand.det he₁ he₂
    have hp : p = [] := by
      simp only [List.length_append] at hn₁
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    exact ⟨rfl, rfl⟩
  case arrayNewFixed.arrayNewFixed =>
    rename_i x₁ n₁ d₁ ft₁ vs₁ he₁ hn₁ hp₁ hd₁ x₂ n₂ d₂ ft₂ vs₂ he₂ hn₂ hp₂ hd₂
    rw [← List.append_assoc, ← vals_append, append_singleton_inj] at hl
    obtain ⟨hv, hx⟩ := hl
    simp only [Admin.plain.injEq, Instr.arrayNewFixed.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    rw [vals_inj] at hv
    subst hv
    rw [hd₁] at hd₂
    cases hd₂
    cases Expand.det he₁ he₂
    have hp : p = [] := by
      simp only [List.length_append] at hn₁
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    exact ⟨rfl, rfl⟩


end Silmaril.Wasm.SingleThreaded.Det

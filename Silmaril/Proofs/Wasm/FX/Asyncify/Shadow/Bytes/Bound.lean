module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Bytes.Defs
public import Mathlib.Data.Set.Basic

/-!
# A machine that traps when a check after a step fails

`step₂` runs `step₁` and traps when the configuration reached is not `good`. Every run of
`step₂` is a run of `step₁` or ends in a trap (`runN_guard`), so its behaviours are among those
of `step₁` and the trap (`beh_guard_sub`); when every reachable configuration is good, the two
have the same behaviours (`beh_guard_eq`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

open Silmaril.Wasm.Models.FXAsync

variable {C V : Type}

/-- `step₁`, trapping when the next configuration is not good. -/
def guardStep (step₁ : C → Res C V) (good : C → Bool) (x : C) : Res C V :=
  match step₁ x with
  | .next y => if good y then .next y else .stop .trap
  | .stop o => .stop o

variable {step₁ : C → Res C V} {good : C → Bool}

theorem runN_next_succ {step : C → Res C V} {x y : C} (h : step x = .next y) (n : Nat) :
    runN step (n + 1) x = runN step n y := by
  simp only [runN, h]

/-- A run of the guarded machine is a run of `step₁`, or it stops with a trap. -/
theorem runN_guard : ∀ (n : Nat) (x : C),
    (∀ y, runN (guardStep step₁ good) n x = .next y → runN step₁ n x = .next y) ∧
    (∀ o, runN (guardStep step₁ good) n x = .stop o → runN step₁ n x = .stop o ∨ o = .trap)
  | 0, x => ⟨fun _ h => h, fun _ h => by cases h⟩
  | n + 1, x => by
    cases h1 : step₁ x with
    | stop o' =>
      have hg : guardStep step₁ good x = .stop o' := by simp [guardStep, h1]
      simp only [runN, hg, h1]
      exact ⟨fun _ h => h, fun _ h => .inl h⟩
    | next y =>
      by_cases hy : good y = true
      · have hg : guardStep step₁ good x = .next y := by simp [guardStep, h1, hy]
        rw [runN_next_succ hg, runN_next_succ h1]
        exact runN_guard n y
      · have hg : guardStep step₁ good x = .stop .trap := by simp [guardStep, h1, hy]
        simp only [runN, hg]
        exact ⟨fun _ h => (by cases h), fun _ h => Or.inr (by cases h; rfl)⟩

/-- **The guarded machine's behaviours are among `step₁`'s and the trap.** -/
theorem beh_guard_sub (x : C) :
    beh (guardStep step₁ good) x ⊆ beh step₁ x ∪ {.trap} := by
  rintro b (⟨n, o, h, rfl⟩ | ⟨rfl, hd⟩)
  · rcases (runN_guard n x).2 o h with h' | rfl
    · exact .inl (.inl ⟨n, o, h', rfl⟩)
    · exact .inr rfl
  · refine .inl (.inr ⟨rfl, fun n => ?_⟩)
    obtain ⟨y, hy⟩ := hd n
    exact ⟨y, (runN_guard n x).1 y hy⟩

/-- When every reachable configuration is good, the runs agree. -/
theorem runN_guard_eq : ∀ (n : Nat) {x : C}, (∀ m y, runN step₁ m x = .next y → good y = true) →
    runN (guardStep step₁ good) n x = runN step₁ n x
  | 0, _, _ => rfl
  | n + 1, x, hall => by
    cases h1 : step₁ x with
    | stop o =>
      have hg : guardStep step₁ good x = .stop o := by simp [guardStep, h1]
      simp only [runN, hg, h1]
    | next y =>
      have hy : good y = true := hall 1 y (by rw [runN_next_succ h1]; rfl)
      have hg : guardStep step₁ good x = .next y := by simp [guardStep, h1, hy]
      rw [runN_next_succ hg, runN_next_succ h1]
      exact runN_guard_eq n fun m z hz => hall (m + 1) z (by rw [runN_next_succ h1]; exact hz)

/-- **When every reachable configuration is good, the same behaviours.** -/
theorem beh_guard_eq {x : C} (hall : ∀ m y, runN step₁ m x = .next y → good y = true) :
    beh (guardStep step₁ good) x = beh step₁ x := by
  ext b
  simp only [beh, Set.mem_union, Set.mem_ofPred_eq, runN_guard_eq _ hall]

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

module

public import Silmaril.Net.Http.Status.Defs

@[expose] public section

/-!
# HTTP status codes: theorems

PROVED (standard axioms):

* `class?_isSome_iff`: a code has a class exactly when it is valid (§15: `100..599`);
* `registered_valid`: every registered code is valid and its class is its first digit;
* `registered_nodup`: the registry has one entry per code;
* `allowsContent_isFinal`: a code that allows content is final.
-/

namespace Silmaril.Net.Http.Status

theorem class?_isSome_iff (s : Nat) : (class? s).isSome = true ↔ isValid s = true := by
  have hv : isValid s = true ↔ 100 ≤ (s : Nat) ∧ (s : Nat) ≤ 599 := by
    simp [isValid]
  rw [hv]
  have h : s / 100 = 0 ∨ s / 100 = 1 ∨ s / 100 = 2 ∨ s / 100 = 3 ∨ s / 100 = 4 ∨
      s / 100 = 5 ∨ 6 ≤ s / 100 := by omega
  rcases h with h | h | h | h | h | h | h
  · have h' : class? s = none := by simp [class?, h]
    simp only [h', Option.isSome_none, Bool.false_eq_true, false_iff]; omega
  all_goals try (simp only [class?, h, Option.isSome_some, true_iff]; omega)
  · have h' : class? s = none := by
      unfold class?; split <;> first | rfl | omega
    simp only [h', Option.isSome_none, Bool.false_eq_true, false_iff]; omega

theorem registered_valid : ∀ p ∈ registered, isValid p.1 = true := by decide

theorem registered_nodup : (registered.map (·.1)).Nodup := by decide

theorem allowsContent_isFinal {s : Status} (h : allowsContent s = true) : isFinal s = true := by
  simp only [allowsContent, Bool.and_eq_true] at h
  exact h.1.1

theorem reason?_ok : reason? ok = some "OK" := by decide

theorem reason?_notFound : reason? notFound = some "Not Found" := by decide

end Silmaril.Net.Http.Status

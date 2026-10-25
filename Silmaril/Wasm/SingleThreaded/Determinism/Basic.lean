module

public import Silmaril.Wasm.SingleThreaded.Thread
public import Silmaril.Wasm.SingleThreaded.Determinism.Vals

@[expose] public section

/-! # Determinism toolkit: values, value prefixes and the first non-value

List lemmas about `vals`, `Val.toAdmin` and `splitVals` used by the determinism
proof (`Determinism/*.lean`) and by the interface lemmas.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core

theorem toAdmin_val?_ne_none (v : Val) : v.toAdmin.val? ≠ none := by simp

theorem splitVals_nonval {a : Admin} (h : a.val? = none) (l : List Admin) :
    splitVals (a :: l) = ([], a :: l) := by
  simp [splitVals, h]

theorem splitVals_val (v : Val) (l : List Admin) :
    splitVals (v.toAdmin :: l) = (v :: (splitVals l).1, (splitVals l).2) := by
  simp [splitVals]

theorem splitVals_vals_append (vs : List Val) (l : List Admin) :
    splitVals (vals vs ++ l) = (vs ++ (splitVals l).1, (splitVals l).2) := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [splitVals_val, ih]

theorem splitVals_vals (vs : List Val) : splitVals (vals vs) = (vs, []) := by
  simpa [splitVals] using splitVals_vals_append vs []

theorem splitVals_vals_cons {vs : List Val} {a : Admin} (h : a.val? = none) (l : List Admin) :
    splitVals (vals vs ++ a :: l) = (vs, a :: l) := by
  simp [splitVals_vals_append, splitVals_nonval h]

theorem vals_append_vals_cons_inj {k₁ k₂ : List Val} {e₁ e₂ : Admin} {t₁ t₂ : List Admin}
    {vs₁ vs₂ : List Val}
    (h : vals vs₁ ++ (vals k₁ ++ e₁ :: t₁) = vals vs₂ ++ (vals k₂ ++ e₂ :: t₂))
    (h₁ : e₁.val? = none) (h₂ : e₂.val? = none) :
    vs₁ ++ k₁ = vs₂ ++ k₂ ∧ e₁ = e₂ ∧ t₁ = t₂ := by
  rw [← List.append_assoc, ← List.append_assoc, ← vals_append, ← vals_append] at h
  exact vals_append_cons_inj h h₁ h₂

end Silmaril.Wasm.SingleThreaded.Det

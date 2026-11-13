module

public import Silmaril.Net.Http2.Settings.Defs

/-!
# HTTP/2 settings and flow control: proofs

For `Silmaril.Net.Http2.Settings.Thms` (RFC 9113 §6.5.2, §6.9).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http2

open Silmaril.Net.Http2

theorem apply_valid {s s' : Settings} {id v : Nat} (hs : s.Valid) (h : s.apply id v = .ok s') :
    s'.Valid := by
  unfold Settings.apply at h
  obtain ⟨h1, h2, h3⟩ := hs
  split at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Except.ok.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Settings.Valid] <;> omega

theorem applyAll_valid {s s' : Settings} {ps : List (Nat × Nat)} (hs : s.Valid)
    (h : s.applyAll ps = .ok s') : s'.Valid := by
  induction ps generalizing s with
  | nil => simp only [Settings.applyAll, Except.ok.injEq] at h; subst h; exact hs
  | cons p ps ih =>
    obtain ⟨id, v⟩ := p
    simp only [Settings.applyAll] at h
    split at h
    · next s₁ h₁ => exact ih (apply_valid hs h₁) h
    · cases h

theorem consume_ok {w w' : Int} {n : Nat} (h : consume w n = .ok w') : w' = w - n ∧ 0 ≤ w' := by
  unfold consume at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; omega
  · cases h

theorem increment_ok {w w' : Int} {k : Nat} (h : increment w k = .ok w') :
    w' = w + k ∧ w' ≤ maxWindow := by
  unfold increment at h
  split at h
  · cases h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; omega
    · cases h

theorem runFlow_eq {w w' : Int} {es : List FlowEvent} (h : runFlow w es = .ok w') :
    w' = w + credit es - dataSent es ∧ (w ≤ maxWindow → w' ≤ maxWindow) := by
  induction es generalizing w with
  | nil => simp only [runFlow, Except.ok.injEq] at h; subst h; simp [credit, dataSent]
  | cons e es ih =>
    cases e with
    | data n =>
      simp only [runFlow] at h
      split at h
      · next w₁ h₁ =>
        have := consume_ok h₁; have := ih h
        simp only [credit, dataSent, Int.natCast_add]; omega
      · cases h
    | update k =>
      simp only [runFlow] at h
      split at h
      · next w₁ h₁ =>
        have := increment_ok h₁; have := ih h
        simp only [credit, dataSent, Int.natCast_add]; omega
      · cases h

theorem runFlow_nonneg {w w' : Int} {es : List FlowEvent} (hw : 0 ≤ w)
    (h : runFlow w es = .ok w') : 0 ≤ w' := by
  induction es generalizing w with
  | nil => simp only [runFlow, Except.ok.injEq] at h; subst h; exact hw
  | cons e es ih =>
    cases e with
    | data n =>
      simp only [runFlow] at h
      split at h
      · next w₁ h₁ => exact ih (consume_ok h₁).2 h
      · cases h
    | update k =>
      simp only [runFlow] at h
      split at h
      · next w₁ h₁ => have := increment_ok h₁; exact ih (by omega) h
      · cases h

end Silmaril.Proofs.Net.Http2

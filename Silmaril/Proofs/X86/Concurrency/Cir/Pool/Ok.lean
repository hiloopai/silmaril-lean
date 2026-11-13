module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Heap

/-!
# Proofs: the layout check decides the layout conditions
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir.Pool

theorem placedB_iff {P : Wp} {a : Nat} :
    P.placedB a = true ↔ a < 2 ^ 64 ∧ (a < P.m ∨ P.m + P.slot ≤ a) := by
  simp [Wp.placedB]

/-- The item checks of `okB`, at a footprint address. -/
theorem okB_fp {P : Wp}
    (hown : ∀ j ∈ List.range P.n, (match P.items[j]? with
      | some it => it.fp.all fun a => P.owner a == some j && P.placedB a
      | none => true) = true)
    {j a : Nat} (h : P.fpB j a = true) :
    P.owner a = some j ∧ P.placedB a = true := by
  have hj := Wp.fpB_lt h
  have H := hown j (List.mem_range.mpr hj)
  unfold Wp.fpB at h
  cases e : P.items[j]? with
  | none => rw [e] at h; cases h
  | some it =>
    rw [e] at h H
    have ha : a ∈ it.fp := by simpa using h
    have := List.all_eq_true.mp H a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this

/-- **`okB` decides `Ok`.** -/
theorem ok_of_okB {P : Wp} (h : P.okB = true) : P.Ok := by
  simp only [Wp.okB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hn⟩, hK⟩, hm⟩, hown⟩, hctl⟩, hnd⟩, harg⟩ := h
  have hown' := List.all_eq_true.mp hown
  have hctl' := List.all_eq_true.mp hctl
  have harg' := List.all_eq_true.mp harg
  refine ⟨hk, hn, hK, hm, fun j _ a ha => (okB_fp hown' ha).1,
    fun j a ha => placedB_iff.mp (okB_fp hown' ha).2, fun a ha => ?_, fun a ha => ?_, hnd,
    fun it hit => by simpa using harg' it hit⟩
  · have := hctl' a ha
    simp only [Bool.and_eq_true] at this
    exact placedB_iff.mp this.1
  · have := hctl' a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

end Silmaril.Proofs.X86.Concurrency.Cir.Pool

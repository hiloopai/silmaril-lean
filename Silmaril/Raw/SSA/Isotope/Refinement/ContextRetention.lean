module

public import Silmaril.Raw.SSA.Isotope.Refinement.ContextSplitting

/-! # Separating the resources of a retained computation -/

@[expose] public section

namespace Silmaril.Isotope.Refinement.QCtx
universe u
variable {τ : Type u} [HasQuantity τ]

/-- A split is disjoint when no slot is retained by both outputs. -/
def Split.Disjoint {n : Nat} {Γ Γl Γr : QCtx τ n} (_ : Γ.Split Γl Γr) : Prop :=
  ∀ i, (Γl i).2 = .zero ∨ (Γr i).2 = .zero

/-- The component used alongside a fully retained context permits copying. -/
theorem SlotSplit.relevant_retained {A : τ} {q ql : Usage}
    (h : SlotSplit A q ql q) : Quantity.relevant ≤ Usage.linearity ql (quantity A) := by
  cases h with
  | left => exact le_top
  | right => exact le_top
  | both h => exact ((Usage.relevant_le_effective_iff _ _).mp h).1

theorem Split.relevant_retained {n : Nat} {Γ Δ : QCtx τ n} (h : Γ.Split Δ Γ) :
    Quantity.relevant ≤ Δ.linearity := by
  apply le_linearity_iff.mpr
  intro i
  have hi := (h i).2.2.relevant_retained
  simpa only [effective, (h i).1] using hi

/-- Keep precisely the source slots absent from the selected component. -/
def complement {n : Nat} (Γ Δ : QCtx τ n) : QCtx τ n :=
  fun i => ((Γ i).1, if (Δ i).2 = .zero then (Γ i).2 else .zero)

theorem SlotSplit.separate_retained {A : τ} {q ql : Usage} (h : SlotSplit A q ql q) :
    SlotSplit A q (if ql = .zero then q else .zero) ql := by
  cases h with
  | left => exact .left .zero
  | right => exact .left q
  | both h =>
    have hn := ((Usage.relevant_le_effective_iff _ _).mp h).2
    simpa only [ite_eq_right_iff.mpr (fun hh => (hn hh).elim)] using SlotSplit.right (A := A) q

/-- Separating a component from a retained input requires no copying. -/
theorem Split.separate_retained {n : Nat} {Γ Δ : QCtx τ n} (h : Γ.Split Δ Γ) :
    Γ.Split (complement Γ Δ) Δ := by
  intro i
  exact ⟨rfl, (h i).1, (h i).2.2.separate_retained⟩

theorem Split.separate_retained_disjoint {n : Nat} {Γ Δ : QCtx τ n} (h : Γ.Split Δ Γ) :
    h.separate_retained.Disjoint := by
  intro i
  by_cases hz : (Δ i).2 = .zero
  · exact .inr hz
  · exact .inl (by simp [complement, hz])

end Silmaril.Isotope.Refinement.QCtx

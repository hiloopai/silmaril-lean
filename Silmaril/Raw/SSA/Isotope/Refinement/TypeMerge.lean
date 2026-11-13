module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypeQuantity

/-! # A common covariant target for free types

Matching product and coproduct shapes are combined componentwise; unmatched
shapes embed into a coproduct. This construction is a comparison device for
unannotated internal type choices, not a lattice operation on types.
-/

@[expose] public section
namespace Silmaril.Isotope.Refinement
universe u
variable {α : Type u} [DecidableEq α]

/-- Preserve shared type structure, using a coproduct for unrelated shapes. -/
def mergeType : Ty α → Ty α → Ty α
  | .base a, .base b => if a = b then .base a else .coprod (.base a) (.base b)
  | .product A B, .product C D => .product (mergeType A C) (mergeType B D)
  | .coprod A B, .coprod C D => .coprod (mergeType A C) (mergeType B D)
  | .unit, .unit => .unit
  | .empty, .empty => .empty
  | A, B => .coprod A B

@[simp] theorem mergeType_self (A : Ty α) : mergeType A A = A := by
  induction A <;> simp_all [mergeType]

variable [HasQuantity α]
/-- Common type comparisons preserve precisely the quantity bounds shared by both types. -/
@[simp] theorem quantity_mergeType (A B : Ty α) : quantity (mergeType A B) = quantity A ⊓ quantity B := by
  induction A generalizing B with
  | base a =>
    cases B <;> simp only [mergeType, quantity_coprod, quantity_base]
    split_ifs with h
    · subst h
      exact (inf_idem _).symm
    · rfl
  | product A C iha ihc =>
    cases B <;> simp [mergeType, iha, ihc, inf_assoc, inf_left_comm, inf_comm]
  | unit => cases B <;> simp [mergeType]
  | coprod A C iha ihc =>
    cases B <;> simp [mergeType, iha, ihc, inf_assoc, inf_left_comm, inf_comm]
  | empty => cases B <;> simp [mergeType]

end Silmaril.Isotope.Refinement

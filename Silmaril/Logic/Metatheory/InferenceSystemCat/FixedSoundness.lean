module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.FixedOrder
public import Silmaril.Logic.Metatheory.InferenceSystemCat.Soundness

@[expose] public section

/-!
# Soundness and completeness at fixed conclusions

The specification and proof system use the same conclusions. Soundness is
inclusion of their derivability sets; completeness is the reverse inclusion.
These are exactly the two directions of the quotient lattice order.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed

open CategoryTheory

universe u v

variable {α : Type u}

/-- The system derives only conclusions allowed by its specification. -/
def Sound (S M : Fixed.{u, v} α) : Prop := support S ⊆ support M

/-- Every conclusion allowed by the specification is derivable. -/
def Complete (S M : Fixed.{u, v} α) : Prop := support M ⊆ support S

theorem sound_iff_ambient (S M : Fixed.{u, v} α) :
    Sound S M ↔ InferenceSystemCat.Sound (toAmbient S) (toAmbient M) id := Iff.rfl

theorem complete_iff_ambient (S M : Fixed.{u, v} α) :
    Complete S M ↔ InferenceSystemCat.Complete (toAmbient S) (toAmbient M) id := Iff.rfl

theorem sound_iff_hom (S M : Fixed.{u, v} α) : Sound S M ↔ Nonempty (S ⟶ M) :=
  nonempty_hom_iff.symm

theorem complete_iff_hom (S M : Fixed.{u, v} α) : Complete S M ↔ Nonempty (M ⟶ S) :=
  nonempty_hom_iff.symm

theorem sound_iff_le (S M : Fixed.{u, v} α) :
    Sound S M ↔ DerivabilityOrder.ofSystem S ≤ DerivabilityOrder.ofSystem M := Iff.rfl

theorem complete_iff_le (S M : Fixed.{u, v} α) :
    Complete S M ↔ DerivabilityOrder.ofSystem M ≤ DerivabilityOrder.ofSystem S := Iff.rfl

/-- Soundness and completeness identify exactly one derivability class. -/
theorem sound_complete_iff (S M : Fixed.{u, v} α) :
    Sound S M ∧ Complete S M ↔ DerivabilityOrder.ofSystem S = DerivabilityOrder.ofSystem M := by
  rw [DerivabilityOrder.ofSystem_eq_iff]
  exact Set.Subset.antisymm_iff.symm

/-- A fixed specification determines a lower set of sound systems. -/
theorem Sound.trans {S T M : Fixed.{u, v} α} (hST : Sound S T) (hTM : Sound T M) : Sound S M :=
  fun _ h => hTM (hST h)

theorem Complete.trans {S T M : Fixed.{u, v} α}
    (hST : Complete S T) (hTM : Complete T M) : Complete S M :=
  fun _ h => hST (hTM h)

end Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed

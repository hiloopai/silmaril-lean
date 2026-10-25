module

public import Silmaril.Logic.SetTheory.ZFSetModel

@[expose] public section

/-!
# The choice axiom used by the inductive ZFC extension

The extension uses the exact first-order `ax-ac` of set.mm. All variables
range over sets. The witness `y` encodes a selection relation through
membership; the formula does not require its members to be unordered pairs.
The concrete `ZFSet` model constructs such a witness using unordered pairs.
`Selected` names the membership-only body and adds no object-language symbol.

The results below are about the meaning of this axiom in a membership
structure. They are not completeness results or proof-system equivalences.
-/

namespace Silmaril.Logic.SetTheory.Inductive.Choice

universe u

variable {M : Type u} [Membership M M]

/-- The membership-only relation selected by the set-of-pairs witness. -/
def Selected (y w u : M) : Prop :=
  ∃ t : M, (u ∈ w ∧ w ∈ t) ∧ (u ∈ t ∧ t ∈ y)

/-- The exact first-order choice assertion, with the family `x` as parameter. -/
def AxAC (x : M) : Prop :=
  ∃ y : M, ∀ z w : M, z ∈ w ∧ w ∈ x →
    ∃ v : M, ∀ u : M, Selected y w u ↔ u = v

/-- The witness has precisely one selected element of each nonempty family member. -/
def ChoiceWitness (x y : M) : Prop :=
  ∀ w : M, w ∈ x → (∃ z : M, z ∈ w) → ∃! u : M, Selected y w u

/-- Equality-to-a-witness and unique existence describe the same selected relation. -/
theorem selection_iff_unique (y w : M) :
    (∃ v : M, ∀ u : M, Selected y w u ↔ u = v) ↔ ∃! u : M, Selected y w u := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (hv v).2 rfl, fun u hu => (hv u).1 hu⟩
  · rintro ⟨v, hv, huniq⟩
    exact ⟨v, fun u => ⟨fun hu => huniq u hu, fun h => h ▸ hv⟩⟩

/-- Removing the redundant nonemptiness witness quantifier preserves the exact axiom. -/
theorem axAC_iff_choiceWitness (x : M) : AxAC x ↔ ∃ y : M, ChoiceWitness x y := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, fun w hw ⟨z, hz⟩ => (selection_iff_unique y w).1 (hy z w ⟨hz, hw⟩)⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, fun z w h => (selection_iff_unique y w).2 (hy w h.2 ⟨z, h.1⟩)⟩

/-- The chosen element really belongs to the family member. -/
theorem selected_mem {y w u : M} (h : Selected y w u) : u ∈ w := h.choose_spec.1.1

/-- An ax-ac witness yields an actual unique member, not only an abstract equality. -/
theorem witness_selects_member {x y w : M} (h : ChoiceWitness x y)
    (hw : w ∈ x) (hne : ∃ z : M, z ∈ w) :
    ∃ v : M, v ∈ w ∧ Selected y w v ∧ ∀ u : M, Selected y w u → u = v := by
  obtain ⟨v, hv, huniq⟩ := h w hw hne
  exact ⟨v, selected_mem hv, hv, huniq⟩

/-- Mathlib's ambient ZFSet model satisfies precisely this membership-only axiom. -/
theorem zfSet_axAC (x : ZFSet.{u}) : AxAC x := ZFSetModel.exists_ac x

end Silmaril.Logic.SetTheory.Inductive.Choice

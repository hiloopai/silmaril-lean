module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Hom.CompleteLattice

@[expose] public section

/-!
# The derivability lattice for fixed conclusions

Proof families form a preorder under preservation of derivability. They do not
form a partial order: different families can derive exactly the same conclusions.
`DerivabilityOrder α` quotients by equality of the sets of derivable conclusions.
It is order isomorphic to `Set α` and hence a complete lattice.

The preorder is supplied as a named definition, not a typeclass instance: the
category on `Fixed α` retains proof maps and must not be replaced by the thin
category induced by a preorder. Passing to `DerivabilityOrder` explicitly forgets
proof multiplicity.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed

open CategoryTheory

universe u v

variable {α : Type u}

/-- The conclusions with at least one derivation. -/
def support (S : Fixed.{u, v} α) : Set α := {a | Nonempty (S.Derivation a)}

@[simp] theorem mem_support (S : Fixed.{u, v} α) (a : α) :
    a ∈ support S ↔ Nonempty (S.Derivation a) := Iff.rfl

/-- Preservation of derivability at the same conclusions. -/
def DerivableLE (S T : Fixed.{u, v} α) : Prop := support S ⊆ support T

/-- The derivability preorder, kept separate from the proof-relevant category. -/
abbrev derivabilityPreorder : Preorder (Fixed.{u, v} α) where
  le := DerivableLE
  le_refl _ := fun _ h => h
  le_trans _ _ _ h h' := fun _ ha => h' (h ha)

/-- An identity-on-conclusions proof map exists exactly when derivability is preserved.
The reverse implication chooses a target derivation in each nonempty fiber. -/
theorem nonempty_hom_iff {S T : Fixed.{u, v} α} :
    Nonempty (S ⟶ T) ↔ support S ⊆ support T := by
  constructor
  · rintro ⟨f⟩ a ⟨d⟩
    exact ⟨f a d⟩
  · intro h
    classical
    exact ⟨fun _ d => Classical.choice (h ⟨d⟩)⟩

/-- A predicate realized as a proof family with at most one derivation per conclusion. -/
def ofSet (P : Set α) : Fixed.{u, v} α where
  Derivation a := ULift.{v} (PLift (a ∈ P))

instance (P : Set α) (a : α) : Subsingleton ((ofSet.{u, v} P).Derivation a) :=
  inferInstanceAs (Subsingleton (ULift.{v} (PLift (a ∈ P))))

@[simp] theorem support_ofSet (P : Set α) : support (ofSet.{u, v} P) = P := by
  ext a
  constructor
  · exact fun ⟨d⟩ => d.down.down
  · exact fun h => ⟨⟨⟨h⟩⟩⟩

@[simp] theorem support_empty : support (empty : Fixed.{u, v} α) = ∅ := by
  ext a
  constructor
  · exact fun ⟨d⟩ => d.elim
  · exact False.elim

@[simp] theorem support_trivial : support (trivial : Fixed.{u, v} α) = Set.univ := by
  ext a
  constructor
  · exact fun _ => True.intro
  · exact fun _ => ⟨PUnit.unit⟩

/-- Proof families are equivalent here when they derive the same conclusions. -/
def sameSupport : Setoid (Fixed.{u, v} α) where
  r S T := support S = support T
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Fixed-conclusion inference systems modulo equality of derivability. -/
def DerivabilityOrder (α : Type u) := Quotient (sameSupport : Setoid (Fixed.{u, v} α))

namespace DerivabilityOrder

/-- Forget the number and representation of a system's derivations. -/
def ofSystem (S : Fixed.{u, v} α) : DerivabilityOrder.{u, v} α := Quotient.mk _ S

/-- The well-defined set of derivable conclusions of an equivalence class. -/
def toSet (q : DerivabilityOrder.{u, v} α) : Set α := Quotient.lift support (fun _ _ h => h) q

/-- Realize a set of conclusions by its canonical subsingleton proof family. -/
def ofSet (P : Set α) : DerivabilityOrder.{u, v} α := ofSystem (Fixed.ofSet P)

@[simp] theorem toSet_ofSystem (S : Fixed.{u, v} α) :
    toSet (ofSystem S) = support S := rfl

@[simp] theorem toSet_ofSet (P : Set α) : toSet (ofSet.{u, v} P) = P :=
  support_ofSet P

@[simp] theorem ofSet_toSet (q : DerivabilityOrder.{u, v} α) : ofSet (toSet q) = q := by
  refine Quotient.inductionOn q ?_
  intro S
  exact Quotient.sound (support_ofSet (support S))

/-- Every derivability class is represented by precisely one predicate on conclusions. -/
def equivSet : DerivabilityOrder.{u, v} α ≃ Set α where
  toFun := toSet
  invFun := ofSet
  left_inv := ofSet_toSet
  right_inv := toSet_ofSet

/-- The quotient has arbitrary joins and meets, inherited from sets of conclusions. -/
instance : CompleteLattice (DerivabilityOrder.{u, v} α) := equivSet.completeLattice

/-- The complete lattice of derivability classes is the powerset lattice. -/
def orderIsoSet : DerivabilityOrder.{u, v} α ≃o Set α where
  toEquiv := equivSet
  map_rel_iff' := Iff.rfl

@[simp] theorem le_iff {p q : DerivabilityOrder.{u, v} α} :
    p ≤ q ↔ toSet p ⊆ toSet q := Iff.rfl

@[simp] theorem ofSystem_le_iff {S T : Fixed.{u, v} α} :
    ofSystem S ≤ ofSystem T ↔ support S ⊆ support T := Iff.rfl

/-- Quotient order is exactly existence of a proof map preserving each conclusion. -/
theorem ofSystem_le_iff_nonempty_hom {S T : Fixed.{u, v} α} :
    ofSystem S ≤ ofSystem T ↔ Nonempty (S ⟶ T) := nonempty_hom_iff.symm

@[simp] theorem ofSystem_eq_iff {S T : Fixed.{u, v} α} :
    ofSystem S = ofSystem T ↔ support S = support T := Quotient.eq

/-- Equality forgets proof multiplicity: maps both ways suffice, not an isomorphism. -/
theorem ofSystem_eq_iff_nonempty_hom {S T : Fixed.{u, v} α} :
    ofSystem S = ofSystem T ↔ Nonempty (S ⟶ T) ∧ Nonempty (T ⟶ S) := by
  rw [ofSystem_eq_iff, nonempty_hom_iff, nonempty_hom_iff]
  exact Set.Subset.antisymm_iff

@[simp] theorem toSet_bot : toSet (⊥ : DerivabilityOrder.{u, v} α) = ∅ := by
  exact equivSet.apply_symm_apply _

@[simp] theorem toSet_top : toSet (⊤ : DerivabilityOrder.{u, v} α) = Set.univ := by
  exact equivSet.apply_symm_apply _

@[simp] theorem toSet_sup (p q : DerivabilityOrder.{u, v} α) :
    toSet (p ⊔ q) = toSet p ∪ toSet q := by
  exact equivSet.apply_symm_apply _

@[simp] theorem toSet_inf (p q : DerivabilityOrder.{u, v} α) :
    toSet (p ⊓ q) = toSet p ∩ toSet q := by
  exact equivSet.apply_symm_apply _

/-- Arbitrary joins derive a conclusion exactly when one component derives it. -/
@[simp] theorem toSet_iSup {ι : Sort*} (p : ι → DerivabilityOrder.{u, v} α) :
    toSet (⨆ i, p i) = ⋃ i, toSet (p i) := map_iSup orderIsoSet p

/-- Arbitrary meets derive the conclusions derivable in every component. -/
@[simp] theorem toSet_iInf {ι : Sort*} (p : ι → DerivabilityOrder.{u, v} α) :
    toSet (⨅ i, p i) = ⋂ i, toSet (p i) := map_iInf orderIsoSet p

@[simp] theorem ofSystem_empty : ofSystem (empty : Fixed.{u, v} α) = ⊥ := by
  apply equivSet.injective
  simp only [equivSet, Equiv.coe_fn_mk, toSet_ofSystem, support_empty, toSet_bot]

@[simp] theorem ofSystem_trivial : ofSystem (trivial : Fixed.{u, v} α) = ⊤ := by
  apply equivSet.injective
  simp only [equivSet, Equiv.coe_fn_mk, toSet_ofSystem, support_trivial, toSet_top]

end DerivabilityOrder

end Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed

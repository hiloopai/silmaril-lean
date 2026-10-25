module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Soundness
public import Silmaril.Logic.Metatheory.InferenceSystemCat.PropSystems
public import Silmaril.Logic.Metatheory.InferenceSystemCat.FixedOrder
public import Mathlib.Order.UpperLower.Basic

@[expose] public section

/-!
# Consistency

A system is consistent when it is not universal: some conclusion is not
derivable. This is `InferenceSystemCat.NonUniversal`; here it is stated for
CSLib inference systems (`Consistent`), proposition-valued systems
(`PropSystems.Consistent`) and fixed-conclusion systems.

A logic usually designates a falsum, and calls a system consistent when it
does not derive it (`ConsistentAt`). This implies non-universality; the
converse holds when the falsum is explosive, i.e. deriving it derives
everything (`consistentAt_iff_consistent`).

Consistency is witnessed by semantics. If derivability is sound for a
predicate (every derivable conclusion satisfies it), each conclusion violating
it is underivable (`Consistent.of_sound`), and consistency is reflected along
provability-preserving interpretations (`nonUniversal_of_hom`).

In a lattice of theories ordered by inclusion of derivable conclusions,
consistent theories are those strictly below the top, the theory of all
conclusions. They form a lower set (`isLowerSet_ne_top`): a subtheory of a
consistent theory is consistent. In the derivability lattice of a fixed
conclusion type, this is non-universality (`DerivabilityOrder.ne_top_iff`).
-/

namespace Silmaril.Logic.Metatheory

open Cslib.Logic InferenceSystemCat

universe s u v

section CSLib

variable (S : Type s)

/-- A CSLib inference system is consistent when some conclusion is underivable. -/
def Consistent (α : Type u) [InferenceSystem S α] : Prop :=
  ∃ a : α, ¬ InferenceSystem.DerivableIn S a

variable {α : Type u} [InferenceSystem S α]

/-- A CSLib inference system is consistent relative to the designated falsum
`falsum` when it does not derive it. -/
def ConsistentAt (falsum : α) : Prop := ¬ InferenceSystem.DerivableIn S falsum

/-- The falsum `falsum` is explosive: deriving it derives every conclusion. -/
def Explosive (falsum : α) : Prop :=
  InferenceSystem.DerivableIn S falsum → ∀ a : α, InferenceSystem.DerivableIn S a

variable {S}

theorem ConsistentAt.consistent {falsum : α} (h : ConsistentAt S falsum) : Consistent S α :=
  ⟨falsum, h⟩

theorem consistentAt_iff_consistent {falsum : α} (h : Explosive S falsum) :
    ConsistentAt S falsum ↔ Consistent S α :=
  ⟨ConsistentAt.consistent, fun ⟨a, ha⟩ hf => ha (h hf a)⟩

theorem consistent_iff_not_forall : Consistent S α ↔ ¬ ∀ a : α, InferenceSystem.DerivableIn S a :=
  not_forall.symm

/-- A predicate satisfied by every derivable conclusion and violated by `a`
shows that `a` is underivable. -/
theorem ConsistentAt.of_sound {Sat : α → Prop}
    (sound : ∀ a, InferenceSystem.DerivableIn S a → Sat a) {a : α} (ha : ¬ Sat a) :
    ConsistentAt S a :=
  fun h => ha (sound a h)

/-- A predicate satisfied by every derivable conclusion and violated somewhere
witnesses consistency. -/
theorem Consistent.of_sound {Sat : α → Prop}
    (sound : ∀ a, InferenceSystem.DerivableIn S a → Sat a) {a : α} (ha : ¬ Sat a) :
    Consistent S α :=
  (ConsistentAt.of_sound sound ha).consistent

/-- Packaging a CSLib system in `InferenceSystemCat` preserves consistency. -/
theorem nonUniversal_of_iff (S : Type s) (α : Type u) [InferenceSystem.{s, u, v} S α] :
    (of.{s, u, v, 0} S α).NonUniversal ↔ Consistent S α :=
  exists_congr fun a => not_congr (of_derivable_iff.{s, u, v, 0} S α a)

end CSLib

namespace InferenceSystemCat

variable {S T : InferenceSystemCat.{u, v}}

/-- A system is consistent at the designated falsum `a` when `a` is not provable. -/
def ConsistentAt (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) : Prop := ¬ S.Provable a

theorem ConsistentAt.nonUniversal {a : S.Conclusion} (h : S.ConsistentAt a) : S.NonUniversal :=
  ⟨a, h⟩

/-- Consistency is reflected along a morphism: if the image of `a` is not
provable, neither is `a`. -/
theorem ConsistentAt.of_hom (f : S ⟶ T) {a : S.Conclusion} (h : T.ConsistentAt (f.map a)) :
    S.ConsistentAt a :=
  fun ha => h (map_provable f ha)

theorem ConsistentAt.of_sound {interpret : S.Conclusion → T.Conclusion}
    (hs : Sound S T interpret) {a : S.Conclusion} (h : T.ConsistentAt (interpret a)) :
    S.ConsistentAt a :=
  fun ha => h (hs a ha)

/-- A system with a morphism into a system that does not prove the image of
some conclusion is consistent. -/
theorem nonUniversal_of_hom (f : S ⟶ T) {a : S.Conclusion} (h : T.ConsistentAt (f.map a)) :
    S.NonUniversal :=
  (ConsistentAt.of_hom f h).nonUniversal

/-- Along a morphism that is surjective on conclusions, consistency of the
target implies consistency of the source. -/
theorem NonUniversal.of_hom_surjective (f : S ⟶ T) (hf : Function.Surjective f.map)
    (h : T.NonUniversal) : S.NonUniversal := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨a, rfl⟩ := hf b
  exact nonUniversal_of_hom f hb

/-- Semantics sound for the system and violated somewhere witnesses consistency. -/
theorem nonUniversal_of_sound {Sat : S.Conclusion → Prop} (sound : ∀ a, S.Provable a → Sat a)
    {a : S.Conclusion} (ha : ¬ Sat a) : S.NonUniversal :=
  ⟨a, fun h => ha (sound a h)⟩

end InferenceSystemCat

namespace InferenceSystemCat.PropSystems

variable {S T : PropSystems.{u}}

/-- A proposition-valued system is consistent when some judgment fails. -/
def Consistent (S : PropSystems.{u}) : Prop := ∃ a, ¬ S.Derivation a

/-- A proposition-valued system does not derive the designated falsum `a`. -/
def ConsistentAt (S : PropSystems.{u}) (a : S.Conclusion) : Prop := ¬ S.Derivation a

theorem ConsistentAt.consistent {a : S.Conclusion} (h : S.ConsistentAt a) : S.Consistent :=
  ⟨a, h⟩

theorem ConsistentAt.of_hom (f : S ⟶ T) {a : S.Conclusion} (h : T.ConsistentAt (f.map a)) :
    S.ConsistentAt a :=
  fun ha => h (f.mapDerivation ha)

/-- Lifting to coherent proof-relevant systems preserves consistency. -/
theorem nonUniversal_toCoherent_iff (S : PropSystems.{u}) :
    (toCoherent.{u, v}.obj S).obj.NonUniversal ↔ S.Consistent :=
  exists_congr fun a => not_congr (toCoherent_provable S a)

end InferenceSystemCat.PropSystems

section Lattice

variable {β : Type u} [Preorder β] [OrderTop β]

/-- Consistent theories, those different from the top theory, form a lower
set: every subtheory of a consistent theory is consistent. -/
theorem isLowerSet_ne_top {β : Type u} [PartialOrder β] [OrderTop β] :
    IsLowerSet {a : β | a ≠ ⊤} :=
  fun _ _ hle h => ne_top_of_le_ne_top h hle

/-- A theory is consistent exactly when it lies strictly below the top. -/
theorem ne_top_iff_lt_top {β : Type u} [PartialOrder β] [OrderTop β] {a : β} :
    a ≠ ⊤ ↔ a < ⊤ :=
  lt_top_iff_ne_top.symm

end Lattice

namespace InferenceSystemCat.Fixed.DerivabilityOrder

variable {α : Type u}

/-- A derivability class is below the top exactly when some conclusion is not
derivable. -/
theorem ne_top_iff (q : DerivabilityOrder.{u, v} α) : q ≠ ⊤ ↔ ∃ a, a ∉ toSet q := by
  rw [Ne, ← equivSet.injective.eq_iff]
  change ¬ toSet q = toSet ⊤ ↔ _
  rw [toSet_top, Set.eq_univ_iff_forall, not_forall]

/-- The class of a fixed-conclusion system is below the top exactly when the
system is non-universal. -/
theorem ofSystem_ne_top_iff (S : Fixed.{u, v} α) :
    ofSystem S ≠ ⊤ ↔ (Fixed.toAmbient S).NonUniversal := by
  rw [ne_top_iff, toSet_ofSystem]
  rfl

end InferenceSystemCat.Fixed.DerivabilityOrder

end Silmaril.Logic.Metatheory

module

public import Silmaril.Logic.Metatheory.InferenceSystemCat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# Derivability and object restrictions

Non-universal systems have an underivable conclusion. Restricting to them, or
to systems whose conclusion type equals a fixed type, gives a full subcategory.
The latter still permits arbitrary maps on conclusions; identity-on-conclusion
maps are a separate restriction.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat

open CategoryTheory

universe u v

/-- A conclusion is provable when its derivation type is inhabited. -/
def Provable (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) : Prop :=
  Nonempty (S.Derivation a)

/-- Every conclusion has a derivation. -/
def Universal (S : InferenceSystemCat.{u, v}) : Prop := ∀ a, S.Provable a

/-- There is at least one underivable conclusion. -/
def NonUniversal (S : InferenceSystemCat.{u, v}) : Prop := ∃ a, ¬ S.Provable a

theorem nonUniversal_iff_not_universal (S : InferenceSystemCat.{u, v}) :
    S.NonUniversal ↔ ¬ S.Universal := by
  classical
  simp [NonUniversal, Universal]

theorem map_provable {S T : InferenceSystemCat.{u, v}} (f : S ⟶ T)
    {a : S.Conclusion} (h : S.Provable a) : T.Provable (f.map a) := by
  obtain ⟨d⟩ := h
  exact ⟨f.mapDerivation d⟩

-- The bundled category retains independent conclusion and proof universes.
set_option linter.checkUnivs false in
/-- The full subcategory of systems with an underivable conclusion. -/
abbrev NonUniversalSystems :=
  ObjectProperty.FullSubcategory (NonUniversal : ObjectProperty InferenceSystemCat.{u, v})

abbrev nonUniversalInclusion : NonUniversalSystems.{u, v} ⥤ InferenceSystemCat.{u, v} :=
  ObjectProperty.ι (NonUniversal : ObjectProperty InferenceSystemCat.{u, v})

/-- The full subcategory with a fixed conclusion type. Its morphisms may still
rename conclusions. Use `Fixed` for the category with identity conclusion maps. -/
abbrev ConclusionSystems (α : Type u) :=
  ObjectProperty.FullSubcategory (fun S : InferenceSystemCat.{u, v} => S.Conclusion = α)

abbrev conclusionInclusion (α : Type u) : ConclusionSystems.{u, v} α ⥤ InferenceSystemCat.{u, v} :=
  ObjectProperty.ι (fun S : InferenceSystemCat.{u, v} => S.Conclusion = α)

/-- The empty ambient system is universal vacuously, so it is excluded from
the non-universal full subcategory. -/
theorem empty_universal : (empty : InferenceSystemCat.{u, v}).Universal := by
  intro a
  exact a.elim

theorem trivial_universal : (trivial : InferenceSystemCat.{u, v}).Universal :=
  fun _ => ⟨PUnit.unit⟩

theorem not_nonUniversal_empty : ¬ (empty : InferenceSystemCat.{u, v}).NonUniversal :=
  fun ⟨a, h⟩ => h (empty_universal a)

theorem not_nonUniversal_trivial : ¬ (trivial : InferenceSystemCat.{u, v}).NonUniversal :=
  fun ⟨a, h⟩ => h (trivial_universal a)

end Silmaril.Logic.Metatheory.InferenceSystemCat

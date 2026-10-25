module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Properties
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

/-!
# Coherent inference systems

A coherent system has at most one derivation of each conclusion. These objects
form a full subcategory: conclusion maps remain arbitrary. Coherification
forgets the identity of derivations while preserving exactly which conclusions
are provable. It is left adjoint to the full inclusion.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat

open CategoryTheory

universe u v

/-- Each conclusion has at most one derivation. -/
def Coherent (S : InferenceSystemCat.{u, v}) : Prop :=
  ∀ a, Subsingleton (S.Derivation a)

set_option linter.checkUnivs false in
/-- Coherence restricts objects, leaving all ambient morphisms available. -/
abbrev CoherentSystems :=
  ObjectProperty.FullSubcategory (Coherent : ObjectProperty InferenceSystemCat.{u, v})

abbrev coherentInclusion : CoherentSystems.{u, v} ⥤ InferenceSystemCat.{u, v} :=
  ObjectProperty.ι (Coherent : ObjectProperty InferenceSystemCat.{u, v})

/-- For a coherent target the conclusion map determines the derivation map. -/
theorem Coherent.hom_ext {S T : InferenceSystemCat.{u, v}} (hT : T.Coherent)
    {f g : S ⟶ T} (h : f.map = g.map) : f = g := by
  cases f with
  | mk f df =>
    cases g with
    | mk g dg =>
      dsimp at h
      cases h
      have hd : @df = @dg := by
        funext a d
        exact (hT (f a)).elim _ _
      cases hd
      rfl

/-- Collapse all derivations of a conclusion to its inhabitedness proposition. -/
def coherification (S : InferenceSystemCat.{u, v}) : InferenceSystemCat.{u, v} where
  Conclusion := S.Conclusion
  Derivation a := ULift.{v} (PLift (S.Provable a))

theorem coherification_coherent (S : InferenceSystemCat.{u, v}) :
    (coherification S).Coherent := by
  intro a
  change Subsingleton (ULift (PLift (S.Provable a)))
  infer_instance

/-- The relation identifying every pair of derivations of the same conclusion. -/
def allDerivationsSetoid (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) :
    Setoid (S.Derivation a) where
  r _ _ := True
  iseqv := ⟨fun _ => True.intro, fun _ => True.intro, fun _ _ => True.intro⟩

instance (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) :
    Subsingleton (Quotient (allDerivationsSetoid S a)) where
  allEq q r := Quotient.inductionOn₂ q r (fun _ _ => Quotient.sound True.intro)

/-- The inhabitedness fiber is exactly the quotient identifying all original derivations. -/
noncomputable def allDerivationsQuotientEquiv (S : InferenceSystemCat.{u, v})
    (a : S.Conclusion) : Quotient (allDerivationsSetoid S a) ≃ (coherification S).Derivation a where
  toFun q := ⟨⟨Quotient.inductionOn q (fun d => ⟨d⟩)⟩⟩
  invFun d := Quotient.mk _ (Classical.choice d.down.down)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := (coherification_coherent S a).elim _ _

@[simp] theorem coherification_provable (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) :
    (coherification S).Provable a ↔ S.Provable a :=
  ⟨fun ⟨d⟩ => d.down.down, fun h => ⟨⟨⟨h⟩⟩⟩⟩

@[simp] theorem coherification_nonUniversal (S : InferenceSystemCat.{u, v}) :
    (coherification S).NonUniversal ↔ S.NonUniversal := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, fun ha => h ((coherification_provable S a).mpr ha)⟩
  · rintro ⟨a, h⟩
    exact ⟨a, fun ha => h ((coherification_provable S a).mp ha)⟩

/-- The quotient map is the identity on conclusions. -/
def coherentUnit (S : InferenceSystemCat.{u, v}) : S ⟶ coherification S where
  map a := a
  mapDerivation d := ⟨⟨⟨d⟩⟩⟩

@[simp] theorem coherentUnit_map (S : InferenceSystemCat.{u, v}) (a : S.Conclusion) :
    (coherentUnit S).map a = a := rfl

/-- The reflector's unit sends a derivation to its literal quotient class. -/
@[simp] theorem allDerivationsQuotientEquiv_mk (S : InferenceSystemCat.{u, v})
    {a : S.Conclusion} (d : S.Derivation a) :
    allDerivationsQuotientEquiv S a (Quotient.mk _ d) = (coherentUnit S).mapDerivation d :=
  (coherification_coherent S a).elim _ _

/-- Coherification transports a conclusion map and its preservation of provability. -/
def coherificationMap {S T : InferenceSystemCat.{u, v}} (f : S ⟶ T) :
    coherification S ⟶ coherification T where
  map := f.map
  mapDerivation d := ⟨⟨map_provable f d.down.down⟩⟩

/-- The reflection into the full subcategory of coherent systems. -/
def coherify : InferenceSystemCat.{u, v} ⥤ CoherentSystems.{u, v} where
  obj S := ⟨coherification S, coherification_coherent S⟩
  map f := ObjectProperty.homMk (coherificationMap f)
  map_id S := by
    apply ObjectProperty.hom_ext
    exact (coherification_coherent S).hom_ext rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (coherification_coherent _).hom_ext rfl

/-- Every map to a coherent system factors through coherification. -/
noncomputable def coherentLift {S T : InferenceSystemCat.{u, v}} (_hT : T.Coherent)
    (f : S ⟶ T) : coherification S ⟶ T where
  map := f.map
  mapDerivation d := Classical.choice (map_provable f d.down.down)

@[simp] theorem coherentLift_map {S T : InferenceSystemCat.{u, v}} (hT : T.Coherent)
    (f : S ⟶ T) (a : S.Conclusion) : (coherentLift hT f).map a = f.map a := rfl

@[simp] theorem coherentUnit_lift {S T : InferenceSystemCat.{u, v}} (hT : T.Coherent)
    (f : S ⟶ T) : coherentUnit S ≫ coherentLift hT f = f :=
  hT.hom_ext rfl

/-- The factorization is unique, including its action on derivations. -/
theorem coherentLift_unique {S T : InferenceSystemCat.{u, v}} (hT : T.Coherent)
    (f : S ⟶ T) (g : coherification S ⟶ T) (h : coherentUnit S ≫ g = f) :
    g = coherentLift hT f :=
  hT.hom_ext (congrArg (fun k => k.map) h)

/-- The reflection's universal hom-set equivalence. -/
noncomputable def coherentHomEquiv (S : InferenceSystemCat.{u, v})
    (T : CoherentSystems.{u, v}) :
    (coherify.obj S ⟶ T) ≃ (S ⟶ coherentInclusion.obj T) where
  toFun f := coherentUnit S ≫ f.hom
  invFun f := ObjectProperty.homMk (coherentLift T.property f)
  left_inv f := by
    apply ObjectProperty.hom_ext
    exact T.property.hom_ext rfl
  right_inv f := coherentUnit_lift T.property f

/-- Coherification is left adjoint to the full inclusion of coherent systems. -/
noncomputable def coherifyAdjunction :
    coherify.{u, v} ⊣ coherentInclusion.{u, v} :=
  Adjunction.mkOfHomEquiv {
    homEquiv := coherentHomEquiv
    homEquiv_naturality_left_symm := by
      intro S' S T f g
      apply ObjectProperty.hom_ext
      exact T.property.hom_ext rfl
    homEquiv_naturality_right := by
      intro S T T' f g
      exact T'.property.hom_ext rfl }

/-- The adjunction has the explicit proof-collapsing quotient map as its unit. -/
@[simp] theorem coherifyAdjunction_unit (S : InferenceSystemCat.{u, v}) :
    coherifyAdjunction.unit.app S = coherentUnit S :=
  (coherification_coherent S).hom_ext rfl

end Silmaril.Logic.Metatheory.InferenceSystemCat

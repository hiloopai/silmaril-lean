module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Coherent
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

/-!
# Proposition-valued inference systems

Here the derivation family takes values in `Prop` directly. Morphisms may
translate conclusions and must preserve the derivation proposition. Lifting
these propositions into any chosen proof universe gives an equivalence with
the full category of coherent proof-relevant systems.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat

open Cslib.Logic CategoryTheory

universe u v

/-- An inference system whose judgments are propositions. -/
structure PropSystems where
  Conclusion : Type u
  Derivation : Conclusion → Prop

namespace PropSystems

structure Tag (S : PropSystems.{u}) where

instance (S : PropSystems.{u}) : InferenceSystem (Tag S) S.Conclusion where
  derivation := S.Derivation

instance : Category (PropSystems.{u}) where
  Hom S T := InferenceMorphism (Tag S) (Tag T) S.Conclusion T.Conclusion
  id _ := InferenceMorphism.id
  comp f g := g.comp f
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- A conclusion function uniquely determines a proposition-valued morphism. -/
theorem hom_ext {S T : PropSystems.{u}} {f g : S ⟶ T} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Lift a proposition-valued system to a coherent proof-relevant system. -/
def lift (S : PropSystems.{u}) : CoherentSystems.{u, v} :=
  ⟨{
    Conclusion := S.Conclusion
    Derivation a := ULift.{v} (PLift (S.Derivation a)) }, by
      intro a
      change Subsingleton (ULift (PLift (S.Derivation a)))
      infer_instance⟩
def liftMap {S T : PropSystems.{u}} (f : S ⟶ T) : lift.{u, v} S ⟶ lift T :=
  ObjectProperty.homMk {
    map := f.map
    mapDerivation d := ⟨⟨f.mapDerivation d.down.down⟩⟩ }

/-- Regard the proposition-valued derivation family as subsingleton proof types. -/
def toCoherent : PropSystems.{u} ⥤ CoherentSystems.{u, v} where
  obj := lift
  map := liftMap
  map_id S := by
    apply ObjectProperty.hom_ext
    apply Coherent.hom_ext
    · intro a
      change Subsingleton (ULift (PLift (S.Derivation a)))
      infer_instance
    · rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Coherent.hom_ext
    · intro a
      change Subsingleton (ULift (PLift _))
      infer_instance
    · rfl

/-- The proposition that a coherent derivation fiber is inhabited. -/
def lower (S : CoherentSystems.{u, v}) : PropSystems.{u} where
    Conclusion := S.obj.Conclusion
    Derivation a := S.obj.Provable a

def lowerMap {S T : CoherentSystems.{u, v}} (f : S ⟶ T) : lower S ⟶ lower T where
    map := f.hom.map
    mapDerivation := map_provable f.hom

/-- Extract the proposition that the coherent proof fiber is inhabited. -/
def ofCoherent : CoherentSystems.{u, v} ⥤ PropSystems.{u} where
  obj := lower
  map := lowerMap
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

@[simp] theorem toCoherent_provable (S : PropSystems.{u}) (a : S.Conclusion) :
    (toCoherent.{u, v}.obj S).obj.Provable a ↔ S.Derivation a :=
  ⟨fun ⟨d⟩ => d.down.down, fun h => ⟨⟨⟨h⟩⟩⟩⟩

@[simp] theorem ofCoherent_derivation (S : CoherentSystems.{u, v})
    (a : S.obj.Conclusion) : (ofCoherent.obj S).Derivation a ↔ S.obj.Provable a := Iff.rfl

/-- Propositional judgments agree with the inhabitedness of their lifted fibers. -/
def unitIso : 𝟭 PropSystems.{u} ≅ toCoherent.{u, v} ⋙ ofCoherent :=
  NatIso.ofComponents (fun _S => {
    hom := {
      map := id
      mapDerivation d := ⟨⟨⟨d⟩⟩⟩ }
    inv := {
      map := id
      mapDerivation d := d.elim fun d => d.down.down }
    hom_inv_id := hom_ext rfl
    inv_hom_id := hom_ext rfl }) (fun _ => hom_ext rfl)

/-- A coherent proof fiber is isomorphic to its lifted inhabitedness proposition. -/
noncomputable def counitIso : ofCoherent.{u, v} ⋙ toCoherent ≅ 𝟭 CoherentSystems.{u, v} :=
  NatIso.ofComponents (fun S => {
    hom := ObjectProperty.homMk {
      map := id
      mapDerivation d := Classical.choice d.down.down }
    inv := ObjectProperty.homMk {
      map := id
      mapDerivation d := ⟨⟨⟨d⟩⟩⟩ }
    hom_inv_id := by
      apply ObjectProperty.hom_ext
      exact (toCoherent.obj (ofCoherent.obj S)).property.hom_ext rfl
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      exact S.property.hom_ext rfl }) (by
        intro S T f
        apply ObjectProperty.hom_ext
        exact T.property.hom_ext rfl)

/-- Native proposition-valued systems are equivalent to the coherent full subcategory. -/
noncomputable def equivalenceCoherent : PropSystems.{u} ≌ CoherentSystems.{u, v} where
  functor := toCoherent
  inverse := ofCoherent
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp S := by
    apply ObjectProperty.hom_ext
    exact (toCoherent.obj S).property.hom_ext rfl

end PropSystems

end Silmaril.Logic.Metatheory.InferenceSystemCat

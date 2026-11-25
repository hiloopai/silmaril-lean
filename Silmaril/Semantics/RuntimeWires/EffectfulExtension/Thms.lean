module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Maps
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulExtension.Preservation

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Assignment

open CategoryTheory Diagram Presentation

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

/-- The two extending functors form the strict effectful square of Lemma 3.13. -/
def extension : (strictRuntime G).Hom T where
  value := F.valueExtension
  computation := F.computationExtension
  valueStrict := (F.valuesInterpretation.functor_extends _ False.elim).strict
  computationStrict := by exact Proofs.EffectfulExtension.computation_strict F
  square := by exact Proofs.EffectfulExtension.pure_square F

/-- The pure square determines the computation functor on objects from its
value functor. -/
theorem computationObjects (H : (strictRuntime G).Hom T)
    (valueObjects : ∀ X : Pure G, H.value.obj X = wordObject F.obj X.word)
    (X : Computations G) :
    H.computation.obj X = F.computationObject X :=
  (Functor.congr_obj H.square (⟨X.word⟩ : Pure G)).trans
    (congrArg T.pure.obj (valueObjects ⟨X.word⟩))

/-- An extension interprets the value presentation and agrees on the effectful
generators after transporting along the forced computation object equalities. -/
structure Extends (H : (strictRuntime G).Hom T) : Prop where
  values : F.valuesInterpretation.Extends (fun _ _ => False) H.value
  effects (e : G.effect.Edge) :
    H.computation.map (effectGenerator G e) ≫
        eqToHom (F.computationObjects H values.objects ⟨G.effect.target e⟩) =
      eqToHom (F.computationObjects H values.objects ⟨G.effect.source e⟩) ≫ F.effect e

/-- Existence in Lemma 3.13. The extension agrees with the entire assignment. -/
theorem extension_extends : F.Extends F.extension where
  values := F.valuesInterpretation.functor_extends _ False.elim
  effects e := by
    change F.computationExtension.map (effectGenerator G e) ≫ eqToHom (rfl) =
      eqToHom (rfl) ≫ F.effect e
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact Proofs.EffectfulExtension.effect_generator F e

end Silmaril.RuntimeWires.StrictEffectful.Assignment

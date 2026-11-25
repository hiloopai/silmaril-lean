module

public import Silmaril.Semantics.RuntimeWires.ChosenCenter.Defs
public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Thms
public import Silmaril.Semantics.RuntimeWires.Polygraph.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ChosenCenter.Comparison

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful

open CategoryTheory PremonoidalCategory

universe u v u' v' u₁ v₁ u₂ v₂

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable (S : StrictEffectful V C)

theorem toCenter_obj_bijective : Function.Bijective S.toCenter.obj :=
  Proofs.ChosenCenter.obj_bijective S

theorem toCenter_full_iff : S.toCenter.Full ↔ S.ExhaustsCenter :=
  Proofs.ChosenCenter.full_iff_exhausts S

theorem toCenter_faithful_iff : S.toCenter.Faithful ↔ S.pure.Faithful :=
  Proofs.ChosenCenter.faithful_iff S

variable {W : Type u₁} {D : Type u₂} [Category.{v₁} W] [Category.{v₂} D]
variable [MonoidalCategory W] [PremonoidalCategory D] [IsStrictTensor W] [IsStrictTensor D]
variable {T : StrictEffectful W D}

/-- A strict effectful functor from a source whose chosen pure image exhausts
the center preserves every central arrow. The target may have additional central arrows. -/
theorem Hom.preservesCentral_of_exhaustsCenter (H : S.Hom T) (h : S.ExhaustsCenter)
    {A B : C} (f : A ⟶ B) (hf : IsCentral f) : IsCentral (H.computation.map f) :=
  Proofs.ChosenCenter.preserves_central S H h f hf

namespace Bundled

/-- The composite free construction for polygraphs whose generators are all effectful. -/
def freeAllEffectful : Polygraph.{u,max u v} ⥤ Bundled.{u,v} :=
  Polygraph.allEffectfulFunctor ⋙ free

/-- The all-effectful adjunction with chosen pure structure. Morphisms on the
semantic side are strict effectful functors. -/
def freeAllEffectfulAdjunction :
    freeAllEffectful.{u,v} ⊣ forget.{u,v} ⋙ EffectfulPolygraph.forgetPure :=
  Polygraph.allEffectfulAdjunction.comp freeAdjunction

end Bundled
end Silmaril.RuntimeWires.StrictEffectful

module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulAdjunction

open CategoryTheory StrictEffectful Bundled
open scoped MonoidalCategory SameArrow

universe u v

theorem id_strict {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C] :
    IsStrictTensorFunctor (𝟭 C) where
  unit := rfl
  tensor _ _ := rfl
  left _ {_ _} _ := (Category.comp_id _).trans (Category.id_comp _).symm
  right {_ _} _ _ := (Category.comp_id _).trans (Category.id_comp _).symm

theorem comp_strict {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [MonoidalCategoryStruct A] [MonoidalCategoryStruct B] [MonoidalCategoryStruct C]
    {F : A ⥤ B} {G : B ⥤ C} (f : IsStrictTensorFunctor F) (g : IsStrictTensorFunctor G) :
    IsStrictTensorFunctor (F ⋙ G) where
  unit := (congrArg G.obj f.unit).trans g.unit
  tensor X Y := (congrArg G.obj (f.tensor X Y)).trans (g.tensor _ _)
  left X {_ _} p :=
    ((DiagramInterpretation.map_congr G (DiagramInterpretation.of_square _ _ (f.left X p))).trans
      (DiagramInterpretation.of_square _ _ (g.left (F.obj X) (F.map p)))).square _ _
  right {_ _} p Z :=
    ((DiagramInterpretation.map_congr G (DiagramInterpretation.of_square _ _ (f.right p Z))).trans
      (DiagramInterpretation.of_square _ _ (g.right (F.map p) (F.obj Z)))).square _ _

theorem comp_square {A B C : Bundled.{u,v}} (a : A.model.Hom B.model) (b : B.model.Hom C.model) :
    A.model.pure ⋙ (a.computation ⋙ b.computation) = (a.value ⋙ b.value) ⋙ C.model.pure := by
  calc
    _ = (A.model.pure ⋙ a.computation) ⋙ b.computation := rfl
    _ = (a.value ⋙ B.model.pure) ⋙ b.computation := congrArg (· ⋙ b.computation) a.square
    _ = a.value ⋙ (B.model.pure ⋙ b.computation) := rfl
    _ = a.value ⋙ (b.value ⋙ C.model.pure) := congrArg (a.value ⋙ ·) b.square
    _ = _ := rfl

end Silmaril.RuntimeWires.Proofs.EffectfulAdjunction

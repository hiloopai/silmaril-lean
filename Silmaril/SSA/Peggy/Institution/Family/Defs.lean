module

public import Silmaril.SSA.Peggy.Institution.Thms

/-! # Peggy institutions over diagrams of fixed-sort dialects -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Institution

open CategoryTheory
open Dialect (FixedSortSignature)

universe u v w c h

variable {Data : Type u} {C : Type c} [Category.{h} C]

/-- Restrict Peggy to a diagram of dialects, such as a subcategory of its signatures. -/
def onFamily (F : C ⥤ FixedSortSignature.{u,v} Data) :
    Silmaril.Inst.Institution.{c,h,max u v,0,max u v (w + 1)} :=
  Silmaril.Inst.Institution.ofFunctor (F ⋙ (inst.{u,v,w} Data).I)

/-- Compare the family with all Peggy signatures by its defining signature functor. -/
def familyComorphism (F : C ⥤ FixedSortSignature.{u,v} Data) :
    Silmaril.Inst.Comorphism (onFamily.{u,v,w,c,h} F) (inst.{u,v,w} Data) :=
  ⟨F, 𝟙 _⟩

/-- A natural change of dialect induces a translation of family institutions. Each component
relabels sentences along that signature map and pulls models back along its reduct. -/
def familyChange {F G : C ⥤ FixedSortSignature.{u,v} Data} (α : F ⟶ G) :
    Silmaril.Inst.Comorphism (onFamily.{u,v,w,c,h} F) (onFamily.{u,v,w,c,h} G) :=
  ⟨𝟭 C, Functor.whiskerRight α (inst.{u,v,w} Data).I ≫ (Functor.leftUnitor _).inv⟩

end Silmaril.SSA.Peggy.Institution

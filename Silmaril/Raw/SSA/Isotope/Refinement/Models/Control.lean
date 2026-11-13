module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Category

/-! # Case and iteration capabilities of categorical models

These extend sequential models. In particular, a sequential model is not
required to have coproducts or an iteration operator.
-/

@[expose] public section
noncomputable section

universe u v w r

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable (τ : Type u) [TypeFormers τ] [TypeQuantity τ]
variable (Φ : Type w) [HasTy Φ τ] (ε : Type r) [EffectSystem ε] [HasEff Φ ε]

/-- A sequential model with chosen distributive, enriched coproducts. -/
structure CaseData extends SeqModel.{u,v,w,r} τ Φ ε where
  coproducts : @ChosenCoproducts τ toSeqData.category
  sum_obj : ∀ A B : τ, coproducts.sum A B = Silmaril.coprod A B
  initial_obj : coproducts.zero = Silmaril.empty
  caseLaws : letI := toSeqData.category; letI := toSeqData.homOrder;
    letI := toSeqData.premonoidal; letI := toSeqData.symmetric;
    CaseCategory τ ε toSeqData.effects coproducts

namespace CaseData

variable {τ Φ ε} (M : CaseData.{u,v,w,r} τ Φ ε)

def inl (A B : τ) : M.toSeqData.Hom A (Silmaril.coprod A B) := by
  letI := M.toSeqData.category
  exact M.coproducts.inl A B ≫ eqToHom (M.sum_obj A B)

def inr (A B : τ) : M.toSeqData.Hom B (Silmaril.coprod A B) := by
  letI := M.toSeqData.category
  exact M.coproducts.inr A B ≫ eqToHom (M.sum_obj A B)

def desc {A B D : τ} (f : M.toSeqData.Hom A D) (g : M.toSeqData.Hom B D) :
    M.toSeqData.Hom (Silmaril.coprod A B) D := by
  letI := M.toSeqData.category
  exact eqToHom (M.sum_obj A B).symm ≫ M.coproducts.desc f g

def abort (A : τ) : M.toSeqData.Hom Silmaril.empty A := by
  letI := M.toSeqData.category
  exact eqToHom M.initial_obj.symm ≫ M.coproducts.abort A

end CaseData

/-- The copy/discard interpretation agrees with the coproduct type formers. -/
structure CaseModel extends CaseData.{u,v,w,r} τ Φ ε where
  discard_empty (h : Quantity.affine ≤ quantity (Silmaril.empty : τ)) :
    toSeqData.discard Silmaril.empty h = toCaseData.abort Silmaril.unit
  copy_empty (h : Quantity.relevant ≤ quantity (Silmaril.empty : τ)) :
    toSeqData.copy Silmaril.empty h = toCaseData.abort (product Silmaril.empty Silmaril.empty)
  discard_coprod (A B : τ) (hA : Quantity.affine ≤ quantity A)
      (hB : Quantity.affine ≤ quantity B) (hAB : Quantity.affine ≤ quantity (Silmaril.coprod A B)) :
    toSeqData.discard (Silmaril.coprod A B) hAB =
      toCaseData.desc (toSeqData.discard A hA) (toSeqData.discard B hB)
  copy_coprod (A B : τ) (hA : Quantity.relevant ≤ quantity A)
      (hB : Quantity.relevant ≤ quantity B) (hAB : Quantity.relevant ≤ quantity (Silmaril.coprod A B)) :
    toSeqData.copy (Silmaril.coprod A B) hAB = toCaseData.desc
      (toSeqData.compose (toSeqData.copy A hA)
        (toSeqData.tensor (toCaseData.inl A B) (toCaseData.inl A B)))
      (toSeqData.compose (toSeqData.copy B hB)
        (toSeqData.tensor (toCaseData.inr A B) (toCaseData.inr A B)))

namespace CaseData

variable {τ Φ ε}

/-- Enriched functors additionally preserving the chosen coproduct operations. -/
structure HomMap (M N : CaseData.{u,v,w,r} τ Φ ε)
    extends SeqData.HomMap M.toSeqData N.toSeqData where
  inl (A B : τ) : map (M.inl A B) = N.inl A B
  inr (A B : τ) : map (M.inr A B) = N.inr A B
  desc {A B D} (f : M.toSeqData.Hom A D) (g : M.toSeqData.Hom B D) :
    map (M.desc f g) = N.desc (map f) (map g)
  abort (A : τ) : map (M.abort A) = N.abort A

namespace HomMap

variable {M N P : CaseData.{u,v,w,r} τ Φ ε}

@[ext] theorem ext {f g : HomMap M N} (h : f.toHomMap = g.toHomMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (M : CaseData.{u,v,w,r} τ Φ ε) : HomMap M M where
  toHomMap := SeqData.HomMap.id M.toSeqData
  inl _ _ := rfl
  inr _ _ := rfl
  desc _ _ := rfl
  abort _ := rfl

def comp (g : HomMap N P) (f : HomMap M N) : HomMap M P where
  toHomMap := g.toHomMap.comp f.toHomMap
  inl A B := (congrArg g.map (f.inl A B)).trans (g.inl _ _)
  inr A B := (congrArg g.map (f.inr A B)).trans (g.inr _ _)
  desc a b := (congrArg g.map (f.desc a b)).trans (g.desc _ _)
  abort A := (congrArg g.map (f.abort A)).trans (g.abort _)

end HomMap
end CaseData

instance : Category (CaseModel.{u,v,w,r} τ Φ ε) where
  Hom M N := CaseData.HomMap M.toCaseData N.toCaseData
  id M := CaseData.HomMap.id M.toCaseData
  comp f g := g.comp f
  id_comp _ := CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl))
  comp_id _ := CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl))
  assoc _ _ _ := CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl))

/-- An iterative model adds strong ordered effect-sensitive Elgot iteration. -/
structure IterModel extends CaseModel.{u,v,w,r} τ Φ ε where
  iteration : letI := toSeqData.category; ConwayIteration τ coproducts
  iterLaws : letI := toSeqData.category; letI := toSeqData.homOrder;
    letI := toSeqData.premonoidal; letI := toSeqData.symmetric;
    IterCategory τ ε toSeqData.effects coproducts caseLaws iteration

namespace IterModel

variable {τ Φ ε} (M : IterModel.{u,v,w,r} τ Φ ε)

def iterate {A B : τ} (f : M.toSeqData.Hom A (Silmaril.coprod B A)) : M.toSeqData.Hom A B := by
  letI := M.toSeqData.category
  exact M.iteration.iterate (f ≫ eqToHom (M.sum_obj B A).symm)

variable {M} in
/-- Model maps preserve iteration of every arrow, not just denotations of syntax. -/
structure HomMap (M N : IterModel.{u,v,w,r} τ Φ ε)
    extends toCaseHom : CaseData.HomMap M.toCaseData N.toCaseData where
  iterate {A B} (f : M.toSeqData.Hom A (Silmaril.coprod B A)) :
    map (M.iterate f) = N.iterate (map f)

namespace HomMap

variable {M N P : IterModel.{u,v,w,r} τ Φ ε}

@[ext] theorem ext {f g : HomMap M N} (h : f.toCaseHom = g.toCaseHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (M : IterModel.{u,v,w,r} τ Φ ε) : HomMap M M where
  toCaseHom := CaseData.HomMap.id M.toCaseData
  iterate _ := rfl

def comp (g : HomMap N P) (f : HomMap M N) : HomMap M P where
  toCaseHom := g.toCaseHom.comp f.toCaseHom
  iterate a := (congrArg g.map (f.iterate a)).trans (g.iterate _)

end HomMap

instance : Category (IterModel.{u,v,w,r} τ Φ ε) where
  Hom := HomMap
  id := HomMap.id
  comp f g := g.comp f
  id_comp _ := HomMap.ext (CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl)))
  comp_id _ := HomMap.ext (CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl)))
  assoc _ _ _ := HomMap.ext (CaseData.HomMap.ext (SeqData.HomMap.ext (fun _ => rfl)))

end IterModel

/-- Forget iteration while retaining the full case model. -/
def forgetIteration : IterModel.{u,v,w,r} τ Φ ε ⥤ CaseModel.{u,v,w,r} τ Φ ε where
  obj M := M.toCaseModel
  map f := f.toCaseHom

/-- Forget coproducts while retaining the full sequential model. -/
def forgetCase : CaseModel.{u,v,w,r} τ Φ ε ⥤ SeqModel.{u,v,w,r} τ Φ ε where
  obj M := M.toSeqModel
  map f := f.toHomMap

end Silmaril.Isotope.Refinement.Models

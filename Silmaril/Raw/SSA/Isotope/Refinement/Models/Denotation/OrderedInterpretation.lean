module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Naturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ResourceNaturality
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel

/-! # Ordered constructor interpretations of categorical models

Every constructor is monotone in its semantic arguments. This uses the actual
ordered category, coproduct, and iteration laws, independently of soundness of
the additional equations and directed refinement rules.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem le_refl {A B : τ} (f : M.Hom A B) : M.le f f := by
  let := M.homOrder
  exact le_rfl

theorem left_mono (A : τ) {B D : τ} {f g : M.Hom B D} (h : M.le f g) :
    M.le (M.left A f) (M.left A g) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  let := M.ordered
  exact OrderedCategory.comp_mono le_rfl
    (OrderedCategory.comp_mono (OrderedPremonoidal.whiskerLeft_mono A h) le_rfl)

theorem right_mono {A B : τ} {f g : M.Hom A B} (h : M.le f g) (D : τ) :
    M.le (M.right f D) (M.right g D) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  let := M.ordered
  exact OrderedCategory.comp_mono le_rfl
    (OrderedCategory.comp_mono (OrderedPremonoidal.whiskerRight_mono D h) le_rfl)

theorem tensor_mono {A B D E : τ} {f f' : M.Hom A B} {g g' : M.Hom D E}
    (hf : M.le f f') (hg : M.le g g') : M.le (M.tensor f g) (M.tensor f' g') :=
  M.compose_mono (M.right_mono hf D) (M.left_mono B hg)

end SeqData

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

theorem desc_mono {A B D : τ} {f f' : M.Hom A D} {g g' : M.Hom B D}
    (hf : M.le f f') (hg : M.le g g') : M.le (M.desc f g) (M.desc f' g') := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  let := M.toSeqData.ordered
  exact OrderedCategory.comp_mono le_rfl (M.caseLaws.desc_mono hf hg)

end CaseData

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

theorem iterate_mono {A B : τ} {f g : M.Hom A (coprod B A)} (h : M.le f g) :
    M.le (M.iterate f) (M.iterate g) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  let := M.toSeqData.ordered
  exact M.iterLaws.monotone (OrderedCategory.comp_mono h le_rfl)

end IterModel

namespace Denotation
variable {M : SeqData.{u,v,w,r} τ Φ ε} {F : Fragment}

/-- The optional control operations inherit monotonicity from their models. -/
structure ControlMonotone (K : ControlData M F) : Prop where
  desc (h : F.HasCase) {A B D : τ} {f f' : M.Hom A D} {g g' : M.Hom B D} :
    M.le f f' → M.le g g' → M.le (K.desc h f g) (K.desc h f' g')
  iterate (h : F.HasIter) {A B : τ} {f g : M.Hom A (coprod B A)} :
    M.le f g → M.le (K.iterate h f) (K.iterate h g)

namespace ControlMonotone

theorem seq (M : SeqModel.{u,v,w,r} τ Φ ε) : ControlMonotone (ControlData.seq M) where
  desc h := False.elim h
  iterate h := False.elim h

theorem case (M : CaseModel.{u,v,w,r} τ Φ ε) : ControlMonotone (ControlData.case M) where
  desc _ := M.toCaseData.desc_mono
  iterate h := False.elim h

theorem iter (M : IterModel.{u,v,w,r} τ Φ ε) : ControlMonotone (ControlData.iter M) where
  desc _ := M.toCaseData.desc_mono
  iterate _ := M.iterate_mono

variable {K : ControlData M F} (N : ControlMonotone K)

theorem contextStep (h : F.HasCase) (D : τ)
    (hc : Quantity.relevant ≤ quantity D) (hd : Quantity.affine ≤ quantity D)
    {A B : τ} {f g : M.Hom (product D A) (coprod B A)} (hf : M.le f g) :
    M.le (K.contextStep h D hc hd f) (K.contextStep h D hc hd g) := by
  exact M.compose_mono (M.le_refl _) (M.compose_mono (M.le_refl _)
    (M.compose_mono (M.left_mono D hf) (M.le_refl _)))

include N in
theorem iterateWithContext (h : F.HasIter) (D : τ)
    (hc : Quantity.relevant ≤ quantity D) (hd : Quantity.affine ≤ quantity D)
    {A B : τ} {f g : M.Hom (product D A) (coprod B A)} (hf : M.le f g) :
    M.le (K.iterateWithContext h D hc hd f) (K.iterateWithContext h D hc hd g) :=
  N.iterate h (contextStep _ D hc hd hf)

end ControlMonotone

/-- The interpreted constructor algebra with its actual categorical hom orders. -/
def orderedAlgebra (K : ControlData M F) (N : ControlMonotone K) :
    OrderedAlgebra (signature (τ := τ) Φ F) where
  toAlgebra := algebra M K
  order i := M.homOrder (packed i.context) i.result
  monotone_op o a b h := by
    cases o with
    | var i hv => exact M.le_refl _
    | op f => exact M.compose_mono (h 0) (M.le_refl _)
    | let₁ A B s =>
      exact M.compose_mono (M.le_refl _) (M.compose_mono (M.left_mono _ (h 0)) (h 1))
    | unit hd => exact M.le_refl _
    | pair A B s => exact M.compose_mono (M.le_refl _) (M.tensor_mono (h 0) (h 1))
    | let₂ A B C s =>
      exact M.compose_mono (M.le_refl _)
        (M.compose_mono (M.left_mono _ (h 0)) (M.compose_mono (M.le_refl _) (h 1)))
    | inl A B hc => exact M.compose_mono (h 0) (M.le_refl _)
    | inr A B hc => exact M.compose_mono (h 0) (M.le_refl _)
    | case A B C hc s =>
      exact M.compose_mono (M.le_refl _)
        (M.compose_mono (M.left_mono _ (h 0))
          (M.compose_mono (M.le_refl _) (N.desc hc (h 1) (h 2))))
    | abort A hc => exact M.compose_mono (h 0) (M.le_refl _)
    | iter A B hc s hu =>
      exact M.compose_mono (M.le_refl _)
        (M.compose_mono (M.left_mono _ (h 0)) (N.iterateWithContext hc _ _ _ (h 1)))

/-- A categorical model map preserves both the constructor operations and
their actual semantic orders. -/
def orderedAlgebraMap {P : SeqData.{u,v,w,r} τ Φ ε} {K : ControlData M F}
    {L : ControlData P F} {φ : M.HomMap P} (C : ControlMap φ K L)
    (N : ControlMonotone K) (O : ControlMonotone L) :
    OrderedAlgebra.Hom (orderedAlgebra K N) (orderedAlgebra L O) where
  toHom := C.algebraMap
  monotone _ := fun _ _ h => φ.monotone h

/-- Categorical sequential models give ordered constructor algebras functorially. -/
def seqOrderedAlgebraFunctor : SeqModel.{u,v,w,r} τ Φ ε ⥤
    OrderedAlgebra.{u, max u w, v} (signature (τ := τ) Φ .seq) where
  obj M := orderedAlgebra (ControlData.seq M) (ControlMonotone.seq M)
  map φ := orderedAlgebraMap (ControlMap.seq φ) _ _
  map_id _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))
  map_comp _ _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))

def caseOrderedAlgebraFunctor : CaseModel.{u,v,w,r} τ Φ ε ⥤
    OrderedAlgebra.{u, max u w, v} (signature (τ := τ) Φ .case) where
  obj M := orderedAlgebra (ControlData.case M) (ControlMonotone.case M)
  map φ := orderedAlgebraMap (ControlMap.case φ) _ _
  map_id _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))
  map_comp _ _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))

def iterOrderedAlgebraFunctor : IterModel.{u,v,w,r} τ Φ ε ⥤
    OrderedAlgebra.{u, max u w, v} (signature (τ := τ) Φ .iter) where
  obj M := orderedAlgebra (ControlData.iter M) (ControlMonotone.iter M)
  map φ := orderedAlgebraMap (ControlMap.iter φ) _ _
  map_id _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))
  map_comp _ _ := OrderedAlgebra.Hom.ext (Algebra.Hom.ext (fun _ => rfl))

end Denotation
end Silmaril.Isotope.Refinement.Models

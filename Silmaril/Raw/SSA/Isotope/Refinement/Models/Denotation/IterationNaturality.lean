module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.StructuralNaturality

/-! # Pure maps of persistent loop environments -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory Denotation
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Duplicating a persistent environment commutes with every pure map that
preserves the chosen diagonals. -/
theorem copy_context_naturality {D E : τ} (f : M.Hom D E) (hf : M.hasEffect ⊥ f)
    (hD : Quantity.relevant ≤ quantity D) (hE : Quantity.relevant ≤ quantity E) (A : τ) :
    M.compose (M.right f A)
      (M.compose (M.right (M.copy E hE) A) (M.associator E E A)) =
    M.compose (M.compose (M.right (M.copy D hD) A) (M.associator D D A))
      (M.tensor f (M.right f A)) := by
  let D' : M.PureObject := ⟨D⟩
  let E' : M.PureObject := ⟨E⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : D' ⟶ E' := ⟨f, hf⟩
  let d : D' ⟶ D' ⊗ D' := ⟨M.copy D hD, M.copy_pure D hD⟩
  let e : E' ⟶ E' ⊗ E' := ⟨M.copy E hE, M.copy_pure E hE⟩
  have hc : ff ≫ e = d ≫ (ff ⊗ₘ ff) :=
    Subtype.ext (M.pure_copy_natural f hf hD hE)
  have he : ff ▷ A' ≫ (e ▷ A' ≫ (α_ E' E' A').hom) =
      (d ▷ A' ≫ (α_ D' D' A').hom) ≫ (ff ⊗ₘ (ff ▷ A')) := by
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hc,
      MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    exact congrArg (fun k => d ▷ A' ≫ k)
      (by simpa only [MonoidalCategory.tensorHom_id] using
        MonoidalCategory.associator_naturality ff ff (𝟙 A'))
  exact congrArg Subtype.val he

end SeqData

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- A pure map of environments intertwines their explicit one-step machines. -/
theorem contextStep_natural {D E A B : τ} (f : M.Hom D E) (hf : M.hasEffect ⊥ f)
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (body : M.Hom (product E A) (coprod B A)) :
    M.compose (M.right f A) ((ControlData.iter M).contextStep trivial E cE dE body) =
      M.compose ((ControlData.iter M).contextStep trivial D cD dD
        (M.compose (M.right f A) body))
        (M.desc (M.inl B (product E A))
          (M.compose (M.right f A) (M.inr B (product E A)))) := by
  let exitD := M.compose (M.right (M.discard D dD) B) (M.leftUnitor B)
  let exitE := M.compose (M.right (M.discard E dE) B) (M.leftUnitor B)
  let transfer := M.desc (M.inl B (product E A))
    (M.compose (M.right f A) (M.inr B (product E A)))
  have hd : M.compose (M.right f B) exitE = exitD := by
    dsimp [exitD, exitE]
    rw [← M.compose_assoc, ← M.toSeqData.right_compose,
      M.toSeqData.pure_discard_natural f hf dD dE]
  have he : M.compose
      (M.desc (M.compose (M.right f B) (M.inl (product E B) (product E A)))
        (M.compose (M.right f A) (M.inr (product E B) (product E A))))
      (M.desc (M.compose exitE (M.inl B (product E A))) (M.inr B (product E A))) =
      M.compose (M.desc (M.compose exitD (M.inl B (product D A)))
        (M.inr B (product D A))) transfer := by
    rw [M.toCaseData.desc_compose, M.toCaseData.desc_compose]
    simp only [M.compose_assoc, transfer, M.toCaseData.inl_desc, M.toCaseData.inr_desc]
    rw [← M.compose_assoc, hd]
  simp only [ControlData.contextStep, ControlData.iter, ControlData.ofCase]
  rw [← M.compose_assoc (M.right (M.discard E dE) B) (M.leftUnitor B),
    ← M.compose_assoc (M.right (M.discard D dD) B) (M.leftUnitor B)]
  change M.compose (M.right f A)
    (M.compose (M.right (M.copy E cE) A)
      (M.compose (M.associator E E A)
        (M.compose (M.left E body)
          (M.compose (M.distribute E B A)
            (M.desc (M.compose exitE (M.inl B (product E A))) (M.inr B (product E A))))))) =
    M.compose
      (M.compose (M.right (M.copy D cD) A)
        (M.compose (M.associator D D A)
          (M.compose (M.left D (M.compose (M.right f A) body))
            (M.compose (M.distribute D B A)
              (M.desc (M.compose exitD (M.inl B (product D A))) (M.inr B (product D A))))))) transfer
  rw [← M.compose_assoc (M.right (M.copy E cE) A) (M.associator E E A),
    ← M.compose_assoc (M.right f A), M.toSeqData.copy_context_naturality f hf cD cE A]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor f (M.right f A)) (M.left E body),
    M.toSeqData.tensor_left_pure f (M.right f A) body hf]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.right f (coprod B A)) (M.distribute E B A),
    M.toCaseData.distribute_natural]
  simp only [M.compose_assoc]
  rw [he]

/-- Changing a persistent loop environment by a pure map commutes with
iteration. All copying and discarding compatibility is derived from model laws. -/
theorem iterateWithContext_natural {D E A B : τ} (f : M.Hom D E) (hf : M.hasEffect ⊥ f)
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (body : M.Hom (product E A) (coprod B A)) :
    M.compose (M.right f A) ((ControlData.iter M).iterateWithContext trivial E cE dE body) =
      (ControlData.iter M).iterateWithContext trivial D cD dD (M.compose (M.right f A) body) :=
  M.pure_uniformity (M.toSeqData.right_effect A hf) (M.contextStep_natural f hf cD dD cE dE body)

end IterModel
end Silmaril.Isotope.Refinement.Models

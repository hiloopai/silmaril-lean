module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Effects
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextCoherence

/-! # Structural naturality of control operations -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r

namespace ChosenCoproducts
variable {C : Type u} [Category.{v} C] (S : ChosenCoproducts C)

/-- Copairing commutes with postcomposition by its universal property. -/
theorem desc_compose {A B D E : C} (f : A ⟶ D) (g : B ⟶ D) (h : D ⟶ E) :
    S.desc f g ≫ h = S.desc (f ≫ h) (g ≫ h) := by
  apply CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext (S.isColimit A B)
  · simp [← Category.assoc]
  · simp [← Category.assoc]

end ChosenCoproducts

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A pure right-hand computation commutes with any left-hand computation. -/
theorem exchange_right_pure {A B D E : τ} (f : M.Hom A B) (g : M.Hom D E)
    (hg : M.hasEffect ⊥ g) :
    M.compose (M.right f D) (M.left B g) =
      M.compose (M.left A g) (M.right f E) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := (M.effects.pure_central hg).2 f
  simpa [compose, left, right, PremonoidalCategory.leftTensor,
    PremonoidalCategory.rightTensor, Category.assoc] using
      congrArg (fun k => eqToHom (M.tensor_obj A D).symm ≫ k ≫ eqToHom (M.tensor_obj B E)) h

end SeqData

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- Postcomposition distributes over the chosen copairing. -/
theorem desc_compose {A B D E : τ} (f : M.Hom A D) (g : M.Hom B D) (h : M.Hom D E) :
    M.compose (M.desc f g) h = M.desc (M.compose f h) (M.compose g h) := by
  apply M.sum_hom_ext
  · rw [← M.compose_assoc, M.inl_desc, M.inl_desc]
  · rw [← M.compose_assoc, M.inr_desc, M.inr_desc]

/-- Equality out of a distributed context can be checked on its two branches. -/
theorem distributed_hom_ext {D A B E : τ} {f g : M.Hom (product D (coprod A B)) E}
    (hl : M.compose (M.left D (M.inl A B)) f = M.compose (M.left D (M.inl A B)) g)
    (hr : M.compose (M.left D (M.inr A B)) f = M.compose (M.left D (M.inr A B)) g) : f = g := by
  have he : M.compose (M.distributeInv D A B) f = M.compose (M.distributeInv D A B) g := by
    unfold distributeInv
    rw [M.desc_compose, M.desc_compose, hl, hr]
  have hh := congrArg (M.compose (M.distribute D A B)) he
  simpa only [← M.compose_assoc, M.distribute_distributeInv, M.identity_compose] using hh

/-- Distribution is natural in the retained environment. The environment map
may be effectful because the sum injections are pure. -/
theorem distribute_natural {D E : τ} (f : M.Hom D E) (A B : τ) :
    M.compose (M.right f (coprod A B)) (M.distribute E A B) =
      M.compose (M.distribute D A B)
        (M.desc (M.compose (M.right f A) (M.inl (product E A) (product E B)))
          (M.compose (M.right f B) (M.inr (product E A) (product E B)))) := by
  apply M.distributed_hom_ext
  · rw [← M.compose_assoc, ← M.toSeqData.exchange_right_pure f (M.inl A B) (M.inl_pure A B),
      M.compose_assoc, M.left_inl_distribute, ← M.compose_assoc,
      M.left_inl_distribute, M.inl_desc]
  · rw [← M.compose_assoc, ← M.toSeqData.exchange_right_pure f (M.inr A B) (M.inr_pure A B),
      M.compose_assoc, M.left_inr_distribute, ← M.compose_assoc,
      M.left_inr_distribute, M.inr_desc]

end CaseData
end Silmaril.Isotope.Refinement.Models

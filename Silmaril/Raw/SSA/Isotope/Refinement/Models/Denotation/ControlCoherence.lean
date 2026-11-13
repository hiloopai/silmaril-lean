module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Operations
public import Silmaril.Raw.SSA.Isotope.CategoryTheory.Premonoidal.Monoidal

/-! # Normalized coproduct and distribution laws

These expose the chosen categorical universal properties using the signature's
sum and product types, and let model-map proofs avoid transport details.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
namespace ChosenCoproducts
variable {C : Type u} [Category.{v} C] (S : ChosenCoproducts C)

theorem eqToHom_inl {A A' B B' : C} (hA : A = A') (hB : B = B') :
    eqToHom hA ≫ S.inl A' B' = S.inl A B ≫ eqToHom (congrArg₂ S.sum hA hB) := by
  subst A'
  subst B'
  simp

theorem eqToHom_inr {A A' B B' : C} (hA : A = A') (hB : B = B') :
    eqToHom hB ≫ S.inr A' B' = S.inr A B ≫ eqToHom (congrArg₂ S.sum hA hB) := by
  subst A'
  subst B'
  simp
end ChosenCoproducts

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

theorem inl_desc {A B D : τ} (f : M.toSeqData.Hom A D) (g : M.toSeqData.Hom B D) :
    M.compose (M.inl A B) (M.desc f g) = f := by
  let := M.toSeqData.category
  simp [SeqData.compose, inl, desc]

theorem inr_desc {A B D : τ} (f : M.toSeqData.Hom A D) (g : M.toSeqData.Hom B D) :
    M.compose (M.inr A B) (M.desc f g) = g := by
  let := M.toSeqData.category
  simp [SeqData.compose, inr, desc]

theorem sum_hom_ext {A B D : τ} {f g : M.toSeqData.Hom (coprod A B) D}
    (hl : M.compose (M.inl A B) f = M.compose (M.inl A B) g)
    (hr : M.compose (M.inr A B) f = M.compose (M.inr A B) g) : f = g := by
  let := M.toSeqData.category
  have h : eqToHom (M.sum_obj A B) ≫ f = eqToHom (M.sum_obj A B) ≫ g := by
    apply BinaryCofan.IsColimit.hom_ext (M.coproducts.isColimit A B)
    · simpa [SeqData.compose, inl, Category.assoc] using hl
    · simpa [SeqData.compose, inr, Category.assoc] using hr
  exact (cancel_epi _).mp h

theorem left_inl_distribute (D A B : τ) :
    M.compose (M.left D (M.inl A B)) (M.distribute D A B) =
      M.inl (product D A) (product D B) := by
  let := M.toSeqData.category
  let := M.toSeqData.premonoidal
  let := M.toSeqData.homOrder
  let := M.toSeqData.symmetric
  let := M.caseLaws.distributor_isIso D A B
  have h := M.coproducts.inl_desc (D ◁ M.coproducts.inl A B) (D ◁ M.coproducts.inr A B)
  change M.coproducts.inl (D ⊗ A) (D ⊗ B) ≫ M.coproducts.distributor D A B =
    D ◁ M.coproducts.inl A B at h
  have hh : D ◁ M.coproducts.inl A B ≫ inv (M.coproducts.distributor D A B) =
      M.coproducts.inl (D ⊗ A) (D ⊗ B) := by
    rw [← h]
    simp
  simp only [SeqData.compose, SeqData.left, inl, distribute,
    whiskerLeft_comp, Category.assoc]
  simp only [whiskerLeft_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (D ◁ M.coproducts.inl A B), hh]
  rw [← Category.assoc, M.coproducts.eqToHom_inl (M.tensor_obj D A).symm (M.tensor_obj D B).symm]
  simp

theorem left_inr_distribute (D A B : τ) :
    M.compose (M.left D (M.inr A B)) (M.distribute D A B) =
      M.inr (product D A) (product D B) := by
  let := M.toSeqData.category
  let := M.toSeqData.premonoidal
  let := M.toSeqData.homOrder
  let := M.toSeqData.symmetric
  let := M.caseLaws.distributor_isIso D A B
  have h := M.coproducts.inr_desc (D ◁ M.coproducts.inl A B) (D ◁ M.coproducts.inr A B)
  change M.coproducts.inr (D ⊗ A) (D ⊗ B) ≫ M.coproducts.distributor D A B =
    D ◁ M.coproducts.inr A B at h
  have hh : D ◁ M.coproducts.inr A B ≫ inv (M.coproducts.distributor D A B) =
      M.coproducts.inr (D ⊗ A) (D ⊗ B) := by
    rw [← h]
    simp
  simp only [SeqData.compose, SeqData.left, inr, distribute,
    whiskerLeft_comp, Category.assoc]
  simp only [whiskerLeft_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (D ◁ M.coproducts.inr A B), hh]
  rw [← Category.assoc, M.coproducts.eqToHom_inr (M.tensor_obj D A).symm (M.tensor_obj D B).symm]
  simp

/-- The forward distributor, expressed in normalized constructor operations. -/
def distributeInv (D A B : τ) :
    M.Hom (coprod (product D A) (product D B)) (product D (coprod A B)) :=
  M.desc (M.left D (M.inl A B)) (M.left D (M.inr A B))

theorem distributeInv_distribute (D A B : τ) :
    M.compose (M.distributeInv D A B) (M.distribute D A B) =
      M.identity (coprod (product D A) (product D B)) := by
  unfold distributeInv
  apply M.sum_hom_ext
  · rw [← M.toSeqData.compose_assoc, M.inl_desc, M.left_inl_distribute, M.compose_identity]
  · rw [← M.toSeqData.compose_assoc, M.inr_desc, M.left_inr_distribute, M.compose_identity]

theorem distribute_distributeInv (D A B : τ) :
    M.compose (M.distribute D A B) (M.distributeInv D A B) =
      M.identity (product D (coprod A B)) := by
  let := M.toSeqData.category
  let := M.toSeqData.premonoidal
  let := M.toSeqData.homOrder
  let := M.toSeqData.symmetric
  let := M.caseLaws.distributor_isIso D A B
  have : IsIso (M.distribute D A B) := by
    unfold distribute
    infer_instance
  apply (cancel_mono (M.distribute D A B)).mp
  change M.compose (M.compose (M.distribute D A B) (M.distributeInv D A B))
      (M.distribute D A B) = M.compose (M.identity _) (M.distribute D A B)
  rw [M.compose_assoc, M.distributeInv_distribute, M.compose_identity, M.identity_compose]

namespace HomMap
variable {M N : CaseData.{u,v,w,r} τ Φ ε}

theorem distributeInv (φ : M.HomMap N) (D A B : τ) :
    φ.map (M.distributeInv D A B) = N.distributeInv D A B := by
  unfold CaseData.distributeInv
  rw [φ.desc, φ.left, φ.left, φ.inl, φ.inr]

/-- Preserving the chosen coproducts and tensor preserves the inverse distributor. -/
theorem distribute (φ : M.HomMap N) (D A B : τ) :
    φ.map (M.distribute D A B) = N.distribute D A B := by
  have hi : N.compose (N.distributeInv D A B) (φ.map (M.distribute D A B)) = N.identity _ := by
    rw [← φ.distributeInv, ← φ.compose, M.distributeInv_distribute, φ.identity]
  calc
    φ.map (M.distribute D A B) =
        N.compose (N.identity _) (φ.map (M.distribute D A B)) := (N.identity_compose _).symm
    _ = N.compose (N.compose (N.distribute D A B) (N.distributeInv D A B))
        (φ.map (M.distribute D A B)) := by rw [N.distribute_distributeInv]
    _ = N.distribute D A B := by rw [N.compose_assoc, hi, N.compose_identity]

end HomMap

end CaseData
end Silmaril.Isotope.Refinement.Models

module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Binding

/-! # Categorical equations for contextual case analysis

All equations are derived from the chosen coproduct universal properties and
premonoidal distributivity. No equation for syntactic denotation is postulated.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Naturality of the normalized left unitor for arbitrary computations. -/
theorem leftUnitor_natural {A B : τ} (f : M.Hom A B) :
    M.compose (M.left Silmaril.unit f) (M.leftUnitor B) =
      M.compose (M.leftUnitor A) f := by
  have h := congrArg (M.compose (M.leftUnitor A)) (M.unit_bind f)
  simpa only [← M.compose_assoc, M.leftUnitor_hom_inv, M.identity_compose] using h

end SeqData
namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- Any two arrows from the designated empty type agree. -/
theorem empty_hom_ext {A : τ} (f g : M.Hom Silmaril.empty A) : f = g := by
  let := M.toSeqData.category
  have h := M.coproducts.isInitial.hom_ext
    (eqToHom M.initial_obj ≫ f) (eqToHom M.initial_obj ≫ g)
  exact (cancel_epi _).mp h

/-- Tensoring with the empty type gives at most one arrow to any object.
This follows already from binary distributivity and initiality. -/
theorem empty_tensor_hom_ext {D A : τ} (f g : M.Hom (product D Silmaril.empty) A) : f = g := by
  have h := congrArg (fun k => M.compose (M.left D k) (M.distribute D Silmaril.empty Silmaril.empty))
    (M.empty_hom_ext (M.inl Silmaril.empty Silmaril.empty) (M.inr Silmaril.empty Silmaril.empty))
  rw [M.left_inl_distribute, M.left_inr_distribute] at h
  have hh := congrArg (fun k => M.compose k (M.desc f g)) h
  simpa only [M.inl_desc, M.inr_desc] using hh

/-- Case eta retains evaluation of the scrutinee and discards only its
unused ambient environment. -/
theorem case_eta {D A B : τ} (d : M.Hom D Silmaril.unit) :
    M.compose (M.distribute D A B)
      (M.desc (M.compose (M.compose (M.right d A) (M.leftUnitor A)) (M.inl A B))
        (M.compose (M.compose (M.right d B) (M.leftUnitor B)) (M.inr A B))) =
      M.compose (M.right d (coprod A B)) (M.leftUnitor (coprod A B)) := by
  apply M.distributed_hom_ext
  · rw [← M.compose_assoc, M.left_inl_distribute, M.inl_desc,
      ← M.compose_assoc, ← M.toSeqData.exchange_right_pure d (M.inl A B) (M.inl_pure A B),
      M.compose_assoc]
    simp only [M.compose_assoc, M.toSeqData.leftUnitor_natural]
  · rw [← M.compose_assoc, M.left_inr_distribute, M.inr_desc,
      ← M.compose_assoc, ← M.toSeqData.exchange_right_pure d (M.inr A B) (M.inr_pure A B),
      M.compose_assoc]
    simp only [M.compose_assoc, M.toSeqData.leftUnitor_natural]

/-- A retained environment and a following computation move inside each
case branch, preserving the order of all effectful computations. -/
theorem case_bind {E D A B C G : τ}
    (l : M.Hom (product D A) C) (r : M.Hom (product D B) C)
    (k : M.Hom (product E C) G) :
    M.compose (M.associator E D (coprod A B))
      (M.compose (M.left E (M.compose (M.distribute D A B) (M.desc l r))) k) =
      M.compose (M.distribute (product E D) A B)
        (M.desc (M.compose (M.associator E D A) (M.compose (M.left E l) k))
          (M.compose (M.associator E D B) (M.compose (M.left E r) k))) := by
  apply M.distributed_hom_ext
  · rw [← M.compose_assoc, ← M.toSeqData.associator_natural_right]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left E (M.left D (M.inl A B))),
      ← M.toSeqData.left_compose,
      ← M.compose_assoc (M.left D (M.inl A B)), M.left_inl_distribute, M.inl_desc]
    rw [← M.compose_assoc (M.left (product E D) (M.inl A B)), M.left_inl_distribute, M.inl_desc]
  · rw [← M.compose_assoc, ← M.toSeqData.associator_natural_right]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left E (M.left D (M.inr A B))),
      ← M.toSeqData.left_compose,
      ← M.compose_assoc (M.left D (M.inr A B)), M.left_inr_distribute, M.inr_desc]
    rw [← M.compose_assoc (M.left (product E D) (M.inr A B)), M.left_inr_distribute, M.inr_desc]

end CaseData
end Silmaril.Isotope.Refinement.Models

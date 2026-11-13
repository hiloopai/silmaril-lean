module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationNaturality

/-! # Structural environment maps for optional control

These are derived properties of the concrete categorical models. Keeping the
proofs separate from control operations lets the typing fold share one resource
restriction proof without imposing further model axioms.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Optional control commutes with structural maps of its retained environment. -/
structure ControlEnvironment {M : SeqData.{u,v,w,r} τ Φ ε} {F : Fragment}
    (K : ControlData M F) : Prop where
  case_natural : ∀ (hg : F.HasCase) {D E A B C : τ} (f : M.Hom D E)
    (l : M.Hom (product E A) C) (r : M.Hom (product E B) C),
    M.compose (M.right f (coprod A B))
      (M.compose (K.distribute hg E A B) (K.desc hg l r)) =
      M.compose (K.distribute hg D A B)
        (K.desc hg (M.compose (M.right f A) l) (M.compose (M.right f B) r))
  iter_natural : ∀ (hg : F.HasIter) {D E A B : τ} (f : M.Hom D E) (_hf : M.hasEffect ⊥ f)
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (body : M.Hom (product E A) (coprod B A)),
    M.compose (M.right f A) (K.iterateWithContext hg E cE dE body) =
      K.iterateWithContext hg D cD dD (M.compose (M.right f A) body)

namespace ControlEnvironment

theorem seq (M : SeqModel.{u,v,w,r} τ Φ ε) : ControlEnvironment (ControlData.seq M) where
  case_natural h := False.elim h
  iter_natural h := False.elim h

theorem caseData_natural (M : CaseData.{u,v,w,r} τ Φ ε)
    {D E A B C : τ} (f : M.Hom D E) (l : M.Hom (product E A) C) (r : M.Hom (product E B) C) :
    M.compose (M.right f (coprod A B)) (M.compose (M.distribute E A B) (M.desc l r)) =
      M.compose (M.distribute D A B)
        (M.desc (M.compose (M.right f A) l) (M.compose (M.right f B) r)) := by
  rw [← M.compose_assoc, M.distribute_natural]
  simp only [M.compose_assoc, M.desc_compose, M.inl_desc, M.inr_desc]

theorem case (M : CaseModel.{u,v,w,r} τ Φ ε) : ControlEnvironment (ControlData.case M) where
  case_natural _ := caseData_natural M.toCaseData
  iter_natural h := False.elim h

theorem iter (M : IterModel.{u,v,w,r} τ Φ ε) : ControlEnvironment (ControlData.iter M) where
  case_natural _ := caseData_natural M.toCaseData
  iter_natural _ := M.iterateWithContext_natural

end ControlEnvironment
end Silmaril.Isotope.Refinement.Models.Denotation

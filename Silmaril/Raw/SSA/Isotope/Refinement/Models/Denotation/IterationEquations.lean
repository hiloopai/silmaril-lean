module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation

/-! # Conway equations at normalized types and persistent environments -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.IterModel
open CategoryTheory Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- The normalized loop equation exposes its first step. -/
theorem fixpoint {A B : τ} (f : M.Hom A (coprod B A)) :
    M.iterate f = M.compose f (M.desc (M.identity B) (M.iterate f)) := by
  let := M.toSeqData.category
  have h := M.iteration.fixpoint (f ≫ eqToHom (M.sum_obj B A).symm)
  simpa [iterate, SeqData.compose, SeqData.identity, CaseData.desc, Category.assoc] using h

/-- Flattening two nested iterations is the Conway codiagonal equation. -/
theorem codiagonal {A B : τ} (f : M.Hom A (coprod (coprod B A) A)) :
    M.iterate (M.iterate f) =
      M.iterate (M.compose f (M.desc (M.identity (coprod B A)) (M.inr B A))) := by
  let := M.toSeqData.category
  let g := f ≫ eqToHom (M.sum_obj (coprod B A) A).symm
  let k := eqToHom (M.sum_obj B A).symm
  have hn := M.iteration.naturality g k
  have hc := M.iteration.codiagonal (g ≫ M.coproducts.map k (𝟙 A))
  rw [← hn] at hc
  simpa [g, k, iterate, SeqData.compose, SeqData.identity, CaseData.desc, CaseData.inr,
    ChosenCoproducts.map, ChosenCoproducts.desc_compose, Category.assoc] using hc

/-- Unfolding a contextual loop retains one environment copy for its next
iteration and discards it only on the exit branch. -/
theorem iterateWithContext_fixpoint {D A B : τ}
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (f : M.Hom (product D A) (coprod B A)) :
    (ControlData.iter M).iterateWithContext trivial D cD dD f =
    M.compose (M.right (M.copy D cD) A)
      (M.compose (M.associator D D A)
        (M.compose (M.left D f)
          (M.compose (M.distribute D B A)
            (M.desc (M.compose (M.right (M.discard D dD) B) (M.leftUnitor B))
              ((ControlData.iter M).iterateWithContext trivial D cD dD f))))) := by
  change M.iterate ((ControlData.iter M).contextStep trivial D cD dD f) = _
  rw [M.fixpoint]
  simp only [ControlData.contextStep, ControlData.iter, ControlData.ofCase,
    M.compose_assoc, M.toCaseData.desc_compose, M.toCaseData.inl_desc, M.toCaseData.inr_desc,
    M.compose_identity]
  rfl

end Silmaril.Isotope.Refinement.Models.IterModel

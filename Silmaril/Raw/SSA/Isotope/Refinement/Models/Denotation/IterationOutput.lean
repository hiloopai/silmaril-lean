module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoherence

/-! # Output naturality and mixed simulations of categorical iteration -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.IterModel
open CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- A continuation on the result may be incorporated into the loop's exit branch. -/
theorem output_naturality {A B D : τ} (f : M.Hom A (coprod B A)) (g : M.Hom B D) :
    M.compose (M.iterate f) g =
      M.iterate (M.compose f (M.desc (M.compose g (M.inl D A)) (M.inr D A))) := by
  let := M.toSeqData.category
  have h := M.iteration.naturality (f ≫ eqToHom (M.sum_obj B A).symm) g
  simpa [iterate, SeqData.compose, CaseData.desc, CaseData.inl, CaseData.inr,
    ChosenCoproducts.map, ChosenCoproducts.desc_compose, Category.assoc] using h

/-- Pure state simulation and arbitrary output postcomposition combine into
one iteration comparison. No purity or special effect bound is imposed on the loop bodies. -/
theorem pure_output_simulation {A B C D : τ}
    (h : M.Hom A B) (k : M.Hom C D)
    (f : M.Hom B (coprod C B)) (g : M.Hom A (coprod D A))
    (hh : M.hasEffect ⊥ h)
    (hs : M.compose h (M.compose f (M.desc (M.compose k (M.inl D B)) (M.inr D B))) =
      M.compose g (M.desc (M.inl D B) (M.compose h (M.inr D B)))) :
    M.compose h (M.compose (M.iterate f) k) = M.iterate g := by
  rw [M.output_naturality]
  exact M.pure_uniformity hh hs

end Silmaril.Isotope.Refinement.Models.IterModel

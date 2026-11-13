module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationEquations

/-! # Strength at the signature's product and sum types -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r

namespace ConwayIteration
variable {C : Type u} [Category.{v} C] {S : ChosenCoproducts C} (It : ConwayIteration C S)

/-- Changing chosen state and output objects only transports the iteration. -/
theorem transport {A A' B B' : C} (hA : A = A') (hB : B = B') (f : A ⟶ S.sum B A) :
    It.iterate (eqToHom hA.symm ≫ f ≫ eqToHom (congrArg₂ S.sum hB hA)) =
      eqToHom hA.symm ≫ It.iterate f ≫ eqToHom hB := by
  subst A'
  subst B'
  simp

end ConwayIteration

namespace IterModel
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- Iteration commutes with retaining an arbitrary, possibly linear, object. -/
theorem strength (D : τ) {A B : τ} (f : M.Hom A (coprod B A)) :
    M.iterate (M.compose (M.left D f) (M.distribute D B A)) = M.left D (M.iterate f) := by
  let := M.toSeqData.category
  let := M.toSeqData.premonoidal
  let := M.toSeqData.homOrder
  let := M.toSeqData.symmetric
  let := M.caseLaws.distributor_isIso D B A
  have h := M.iterLaws.strength D (f ≫ eqToHom (M.sum_obj B A).symm)
  have ht := M.iteration.transport (M.tensor_obj D A) (M.tensor_obj D B)
    (D ◁ (f ≫ eqToHom (M.sum_obj B A).symm) ≫ inv (M.coproducts.distributor D B A))
  rw [h] at ht
  simpa [iterate, SeqData.compose, SeqData.left, CaseData.distribute,
    PremonoidalCategory.whiskerLeft_comp, PremonoidalCategory.whiskerLeft_eqToHom,
    Category.assoc] using ht

end IterModel
end Silmaril.Isotope.Refinement.Models

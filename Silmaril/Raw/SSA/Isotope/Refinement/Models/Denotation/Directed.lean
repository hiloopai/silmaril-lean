module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Binding
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Separation

/-! # Directed categorical operations at the signature's types -/

@[expose] public section

-- Toolchain fix (port): Mathlib's `β_` and the premonoidal `β_` of
-- `Premonoidal.Symmetric` are both in scope; select Mathlib's braiding, as in the source.
local notation (priority := high) "β_" => CategoryTheory.BraidedCategory.braiding
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.SeqData
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Precomposition preserves either refinement orientation. -/
theorem orient_compose_left (p : Polarity) {A B C : τ} {f g : M.Hom B C}
    (h : p.orient M.le f g) (k : M.Hom A B) :
    p.orient M.le (M.compose k f) (M.compose k g) := by
  cases p <;> exact M.compose_mono (M.le_refl _) h

theorem orient_left (p : Polarity) (D : τ) {A B : τ} {f g : M.Hom A B}
    (h : p.orient M.le f g) : p.orient M.le (M.left D f) (M.left D g) := by
  cases p <;> exact M.left_mono D h

theorem orient_right (p : Polarity) {A B : τ} {f g : M.Hom A B}
    (h : p.orient M.le f g) (D : τ) : p.orient M.le (M.right f D) (M.right g D) := by
  cases p <;> exact M.right_mono h D

/-- A right-invertible observation reflects directed inequalities. -/
theorem orient_of_compose_right (p : Polarity) {A B C : τ} {f g : M.Hom A B}
    (k : M.Hom B C) (l : M.Hom C B) (hkl : M.compose k l = M.identity B)
    (h : p.orient M.le (M.compose f k) (M.compose g k)) : p.orient M.le f g := by
  have hr := M.orient_compose_right p h l
  simpa only [M.compose_assoc, hkl, M.compose_identity] using hr

/-- The effect system's mover relation compares the two evaluation orders. -/
theorem exchange (p : Polarity) {e η : ε} {A B D E : τ}
    (f : M.Hom A B) (g : M.Hom D E) (hm : EffectSystem.moves p e η)
    (hf : M.hasEffect e f) (hg : M.hasEffect η g) :
    p.orient M.le (M.compose (M.right f D) (M.left B g))
      (M.compose (M.left A g) (M.right f E)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := M.effects.exchange p hm hf hg
  have h' := M.orient_compose_left p
    (M.orient_compose_right p h (eqToHom (M.tensor_obj B E)))
    (eqToHom (M.tensor_obj A D).symm)
  simpa [compose, left, right, PremonoidalCategory.leftTensor,
    PremonoidalCategory.rightTensor, Category.assoc] using h'

theorem braiding_natural_left {A B : τ} (f : M.Hom A B) (D : τ) :
    M.compose (M.right f D) (M.braiding B D) =
      M.compose (M.braiding A D) (M.left D f) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, right, left, braiding, Category.assoc,
    BraidedPremonoidalCategory.naturality_left_assoc]

theorem unit_swap_cancel (A : τ) :
    M.compose (M.leftUnitorInv A)
      (M.compose (M.braiding Silmaril.unit A) (M.rightUnitor A)) = M.identity A := by
  let A' : M.PureObject := ⟨A⟩
  have h : (λ_ A').inv ≫ (β_ (𝟙_ M.PureObject) A').hom ≫ (ρ_ A').hom = 𝟙 A' := by
    simp
  exact congrArg Subtype.val h

end Silmaril.Isotope.Refinement.Models.SeqData

namespace Silmaril.Isotope.Refinement.Models.SeqModel
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Delete a computation on the second copy while retaining the first. -/
theorem retained_unit_right (p : Polarity) {e : ε} {A : τ} (f : M.Hom A Silmaril.unit)
    (hA : Quantity.relevant ≤ quantity A) (he : EffectSystem.canDelete p e)
    (hf : M.hasEffect e f) :
    p.orient M.le (M.compose (M.copy A hA)
      (M.compose (M.left A f) (M.rightUnitor A))) (M.identity A) := by
  have hI : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]
    exact le_top
  have h := M.toSeqData.retained_elimination p f hA hI he hf
  rw [M.discard_unit, M.toSeqData.compose_identity] at h
  have h' := M.toSeqData.orient_compose_right p h
    (M.compose (M.braiding Silmaril.unit A) (M.rightUnitor A))
  rw [M.toSeqData.unit_swap_cancel] at h'
  simp only [M.toSeqData.compose_assoc] at h'
  rw [← M.toSeqData.compose_assoc (M.right f A), M.toSeqData.braiding_natural_left] at h'
  simp only [M.toSeqData.compose_assoc] at h'
  rw [← M.toSeqData.compose_assoc (M.copy A hA), M.toSeqData.copy_braiding] at h'
  exact h'

end Silmaril.Isotope.Refinement.Models.SeqModel

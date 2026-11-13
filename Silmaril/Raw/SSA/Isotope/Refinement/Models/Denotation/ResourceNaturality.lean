module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Slots

@[expose] public section

namespace Silmaril.Isotope.Refinement.Models.SeqData

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Composition is monotone at the model's fixed type indices. -/
theorem compose_mono {A B D : τ} {f f' : M.Hom A B} {g g' : M.Hom B D}
    (hf : M.le f f') (hg : M.le g g') : M.le (M.compose f g) (M.compose f' g') := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.ordered
  exact OrderedCategory.comp_mono hf hg

/-- Postcomposition preserves either orientation of refinement. -/
theorem orient_compose_right (p : Polarity) {A B D : τ} {f g : M.Hom A B}
    (h : p.orient M.le f g) (k : M.Hom B D) :
    p.orient M.le (M.compose f k) (M.compose g k) := by
  cases p <;> exact M.compose_mono h (by let := M.category; let := M.homOrder; exact le_rfl)

/-- Normalized directional deletion is the written discard naturality law. -/
theorem discard_naturality (p : Polarity) {e : ε} {A B : τ} (f : M.Hom A B)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) (hf : M.hasEffect e f) :
    p.orient M.le (M.compose f (M.discard B hB)) (M.discard A hA) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := M.orient_compose_right p (M.copyDiscard.discard_natural p f hA hB he hf)
    (eqToHom M.tensor_unit)
  simpa only [compose, discard, Category.assoc] using h

/-- The effect-sensitive copy inequality at the signature's product types. -/
theorem copy_naturality (p : Polarity) {e : ε} {A B : τ} (f : M.Hom A B)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (he : EffectSystem.canCopy p e) (hf : M.hasEffect e f) :
    p.orient M.le (M.compose f (M.copy B hB))
      (M.compose (M.copy A hA) (M.tensor f f)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := M.orient_compose_right p (M.copyDiscard.copy_natural p f hA hB he hf)
    (eqToHom (M.tensor_obj B B))
  simpa [compose, copy, tensor, right, left, PremonoidalCategory.leftTensor, Category.assoc] using h

/-- Keeping the original input while deleting a pure/deletable computation. -/
theorem retained_elimination (p : Polarity) {e : ε} {A B : τ} (f : M.Hom A B)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) (hf : M.hasEffect e f) :
    p.orient M.le
      (M.compose (M.copy A hA) (M.right (M.compose f (M.discard B hB)) A))
      (M.leftUnitorInv A) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := M.orient_compose_right p (M.copyDiscard.retained_elimination p f hA hB he hf)
    (eqToHom (by rw [M.tensor_obj, M.tensor_unit] : (𝟙_ τ) ⊗ A = product Silmaril.unit A))
  simpa [compose, copy, discard, right, leftUnitorInv, PremonoidalCategory.comp_whiskerRight,
    PremonoidalCategory.eqToHom_whiskerRight, Category.assoc] using h

/-- Pure arrows preserve the chosen diagonal maps whenever both types permit copying. -/
theorem pure_copy_natural {A B : τ} (f : M.Hom A B) (hf : M.hasEffect ⊥ f)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B) :
    M.compose f (M.copy B hB) = M.compose (M.copy A hA) (M.tensor f f) := by
  let := M.category
  let := M.homOrder
  exact le_antisymm
    (M.copy_naturality .positive f hA hB (EffectSystem.canCopy_pure _) hf)
    (M.copy_naturality .negative f hA hB (EffectSystem.canCopy_pure _) hf)

end Silmaril.Isotope.Refinement.Models.SeqData

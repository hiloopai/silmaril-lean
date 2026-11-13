module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Splitting
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Weakening

@[expose] public section

-- Toolchain fix (port): Mathlib's `β_` and the premonoidal `β_` of
-- `Premonoidal.Symmetric` are both in scope; select Mathlib's braiding, as in the source.
local notation (priority := high) "β_" => CategoryTheory.BraidedCategory.braiding

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r

namespace Structural
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
open MonoidalCategory BraidedCategory

theorem tensorμ_unit_unit (B D : C) :
    (B ⊗ D) ◁ (λ_ (𝟙_ C)).inv ≫ tensorμ B D (𝟙_ C) (𝟙_ C) ≫
      ((ρ_ B).hom ⊗ₘ (ρ_ D).hom) = (ρ_ (B ⊗ D)).hom :=
  (tensor_right_unitality B D).symm

theorem tensorμ_unit_left (B D A : C) :
    (B ⊗ D) ◁ (λ_ A).inv ≫ tensorμ B D (𝟙_ C) A ≫
      ((ρ_ B).hom ⊗ₘ 𝟙 (D ⊗ A)) = (α_ B D A).hom := by
  simp only [tensorμ, tensorHom_def, whiskerLeft_id, Category.comp_id,
    braiding_tensorUnit_right]
  monoidal

theorem tensorμ_unit_right (B D A : C) :
    (B ⊗ D) ◁ (ρ_ A).inv ≫ tensorμ B D A (𝟙_ C) ≫
      (𝟙 (B ⊗ A) ⊗ₘ (ρ_ D).hom) =
    (α_ B D A).hom ≫ B ◁ (β_ D A).hom ≫ (α_ B A D).inv := by
  simp only [tensorμ, tensorHom_def, id_whiskerRight, Category.id_comp]
  monoidal

end Structural

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- The chosen normalized copy is coassociative. -/
theorem copy_associator (A : τ) (h : Quantity.relevant ≤ quantity A) :
    M.compose (M.copy A h) (M.compose (M.right (M.copy A h) A) (M.associator A A A)) =
      M.compose (M.copy A h) (M.left A (M.copy A h)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, copy, right, left, associator]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp,
    PremonoidalCategory.eqToHom_whiskerRight, PremonoidalCategory.whiskerLeft_eqToHom]
  have hh : (M.copyDiscard.copy A h ≫ M.copyDiscard.copy A h ▷ A) ≫ (α_ A A A).hom =
      M.copyDiscard.copy A h ≫ A ◁ M.copyDiscard.copy A h := by
    simpa only [Category.assoc] using M.copyDiscard.copy_assoc A h
  simp only [← Category.assoc]
  rw [hh]
  simp only [Category.assoc, eqToHom_trans]

/-- Retained elimination for a pure identity supplies the counit law. -/
theorem copy_discard_left (A : τ) (hc : Quantity.relevant ≤ quantity A)
    (hd : Quantity.affine ≤ quantity A) :
    M.compose (M.copy A hc) (M.right (M.discard A hd) A) = M.leftUnitorInv A := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h : M.copyDiscard.copy A hc ≫ M.copyDiscard.discard A hd ▷ A = (λ_ A).inv := by
    have hp := M.copyDiscard.retained_elimination .positive (𝟙 A) hc hd
      (EffectSystem.canDelete_pure _) (M.effects.id ⊥ A)
    have hn := M.copyDiscard.retained_elimination .negative (𝟙 A) hc hd
      (EffectSystem.canDelete_pure _) (M.effects.id ⊥ A)
    simpa using le_antisymm hp hn
  simp only [compose, copy, discard, right, leftUnitorInv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.eqToHom_whiskerRight]
  simp only [← Category.assoc, h, eqToHom_trans]

end SeqData
namespace Denotation
open MonoidalCategory BraidedCategory
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- An unused variable contributes the tensor unit, while a retained variable
contributes its value type, independently of the nonzero quantity annotation. -/
def slotObject (A : τ) : Usage → M.PureObject
  | .zero => 𝟙_ M.PureObject
  | .used _ => ⟨A⟩

/-- The packing convention suppresses unit factors for unused variables. -/
def retainIso (L A : τ) (q : Usage) :
    (⟨retain L A q⟩ : M.PureObject) ≅ (⟨L⟩ : M.PureObject) ⊗ slotObject M A q :=
  match q with
  | .zero => (ρ_ (⟨L⟩ : M.PureObject)).symm
  | .used _ => Iso.refl _

/-- The scalar structural map specified by one quantitative split. -/
def slotSplit {A : τ} {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) :
    slotObject M A q ⟶ slotObject M A ql ⊗ slotObject M A qr := by
  cases q <;> cases ql <;> cases qr
  · exact (λ_ (𝟙_ M.PureObject)).inv
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact (λ_ (⟨A⟩ : M.PureObject)).inv
  · exact (ρ_ (⟨A⟩ : M.PureObject)).inv
  · have hc : Quantity.relevant ≤ quantity A := by
      cases h with
      | both h => exact ((Usage.relevant_le_effective_iff _ _).mp h).1.trans inf_le_left
    exact ⟨M.copy A hc, M.copy_pure A hc⟩

/-- Context splitting appends the scalar split using the symmetric tensor comparison. -/
theorem splitSlot_tensor {L B D A : τ} (f : PureHom M L (product B D))
    {q ql qr : Usage} (h : QCtx.SlotSplit A q ql qr) :
    splitSlot M f h =
      (retainIso M L A q).hom ≫
      ((show (⟨L⟩ : M.PureObject) ⟶ (⟨B⟩ : M.PureObject) ⊗ (⟨D⟩ : M.PureObject) from f)
        ⊗ₘ slotSplit M h) ≫
      tensorμ (⟨B⟩ : M.PureObject) (⟨D⟩ : M.PureObject) (slotObject M A ql) (slotObject M A qr) ≫
      ((retainIso M B A ql).inv ⊗ₘ (retainIso M D A qr).inv) := by
  let L' : M.PureObject := ⟨L⟩
  let B' : M.PureObject := ⟨B⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : L' ⟶ B' ⊗ D' := f
  cases q <;> cases ql <;> cases qr
  · change ff = (ρ_ L').inv ≫ (ff ⊗ₘ (λ_ (𝟙_ M.PureObject)).inv) ≫
      tensorμ B' D' (𝟙_ M.PureObject) (𝟙_ M.PureObject) ≫ ((ρ_ B').hom ⊗ₘ (ρ_ D').hom)
    simp only [tensorHom_def, Category.assoc]
    rw [← tensorHom_def, Structural.tensorμ_unit_unit]
    simp
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · exact False.elim (by cases h)
  · change ff ▷ A' ≫ (α_ B' D' A').hom =
      𝟙 _ ≫ (ff ⊗ₘ (λ_ A').inv) ≫ tensorμ B' D' (𝟙_ M.PureObject) A' ≫
        ((ρ_ B').hom ⊗ₘ 𝟙 _)
    simp only [Category.id_comp, tensorHom_def, Category.assoc]
    rw [← tensorHom_def, Structural.tensorμ_unit_left]
  · change ff ▷ A' ≫ (α_ B' D' A').hom ≫ B' ◁ (β_ D' A').hom ≫ (α_ B' A' D').inv =
      𝟙 _ ≫ (ff ⊗ₘ (ρ_ A').inv) ≫ tensorμ B' D' A' (𝟙_ M.PureObject) ≫
        (𝟙 _ ⊗ₘ (ρ_ D').hom)
    simp only [Category.id_comp, tensorHom_def, Category.assoc]
    rw [← tensorHom_def, Structural.tensorμ_unit_right]
  · have hc : Quantity.relevant ≤ quantity A := by
      cases h with
      | both h => exact ((Usage.relevant_le_effective_iff _ _).mp h).1.trans inf_le_left
    let c : A' ⟶ A' ⊗ A' := ⟨M.copy A hc, M.copy_pure _ _⟩
    change (ff ⊗ₘ c) ≫ tensorμ B' D' A' A' =
      𝟙 (L' ⊗ A') ≫ (ff ⊗ₘ c) ≫ tensorμ B' D' A' A' ≫
        (𝟙 (B' ⊗ A') ⊗ₘ 𝟙 (D' ⊗ A'))
    simp


/-- Scalar interpretation of quantity weakening. -/
def slotWeaken {A : τ} {q q' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    slotObject M A q ⟶ slotObject M A q' := by
  cases q <;> cases q'
  · exact 𝟙 _
  · exact False.elim h
  · have ha : Quantity.affine ≤ quantity A :=
      ((Usage.zero_le_effective_iff _ _).mp h).trans inf_le_left
    exact ⟨M.discard A ha, M.discard_pure A ha⟩
  · exact 𝟙 _

/-- Quantity weakening is tensoring the scalar weakening with the retained map. -/
theorem weakenSlot_tensor {L B A : τ} (f : PureHom M L B) {q q' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    weakenSlot M f h = (retainIso M L A q).hom ≫
      ((show (⟨L⟩ : M.PureObject) ⟶ (⟨B⟩ : M.PureObject) from f) ⊗ₘ slotWeaken M h) ≫
      (retainIso M B A q').inv := by
  let L' : M.PureObject := ⟨L⟩
  let B' : M.PureObject := ⟨B⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : L' ⟶ B' := f
  cases q <;> cases q'
  · change ff = (ρ_ L').inv ≫ (ff ⊗ₘ 𝟙 (𝟙_ M.PureObject)) ≫ (ρ_ B').hom
    simp
  · exact False.elim h
  · have ha : Quantity.affine ≤ quantity A :=
      ((Usage.zero_le_effective_iff _ _).mp h).trans inf_le_left
    let d : A' ⟶ 𝟙_ M.PureObject := ⟨M.discard A ha, M.discard_pure _ _⟩
    change ff ▷ A' ≫ B' ◁ d ≫ (ρ_ B').hom =
      𝟙 (L' ⊗ A') ≫ (ff ⊗ₘ d) ≫ (ρ_ B').hom
    simp only [Category.id_comp, tensorHom_def, Category.assoc]
  · change ff ▷ A' = 𝟙 (L' ⊗ A') ≫ (ff ⊗ₘ 𝟙 A') ≫ 𝟙 (B' ⊗ A')
    simp

/-- A scalar copy followed by discarding its first output is a unitor inverse. -/
theorem pure_copy_discard_left (A : τ) (hc : Quantity.relevant ≤ quantity A)
    (hd : Quantity.affine ≤ quantity A) :
    (show (⟨A⟩ : M.PureObject) ⟶ (⟨A⟩ : M.PureObject) ⊗ (⟨A⟩ : M.PureObject)
      from ⟨M.copy A hc, M.copy_pure _ _⟩) ≫
      (show (⟨A⟩ : M.PureObject) ⟶ 𝟙_ M.PureObject from ⟨M.discard A hd, M.discard_pure _ _⟩) ▷
        (⟨A⟩ : M.PureObject) = (λ_ (⟨A⟩ : M.PureObject)).inv :=
  Subtype.ext (M.copy_discard_left A hc hd)

/-- The right counit follows by symmetry of copying. -/
theorem pure_copy_discard_right (A : τ) (hc : Quantity.relevant ≤ quantity A)
    (hd : Quantity.affine ≤ quantity A) :
    (show (⟨A⟩ : M.PureObject) ⟶ (⟨A⟩ : M.PureObject) ⊗ (⟨A⟩ : M.PureObject)
      from ⟨M.copy A hc, M.copy_pure _ _⟩) ≫
      (⟨A⟩ : M.PureObject) ◁
        (show (⟨A⟩ : M.PureObject) ⟶ 𝟙_ M.PureObject from ⟨M.discard A hd, M.discard_pure _ _⟩) =
      (ρ_ (⟨A⟩ : M.PureObject)).inv := by
  let A' : M.PureObject := ⟨A⟩
  let c : A' ⟶ A' ⊗ A' := ⟨M.copy A hc, M.copy_pure _ _⟩
  let d : A' ⟶ 𝟙_ M.PureObject := ⟨M.discard A hd, M.discard_pure _ _⟩
  have hc' : c ≫ (β_ A' A').hom = c := Subtype.ext (M.copy_braiding A hc)
  change c ≫ A' ◁ d = (ρ_ A').inv
  rw [← leftUnitor_inv_braiding]
  rw [← pure_copy_discard_left M A hc hd]
  change c ≫ A' ◁ d = (c ≫ d ▷ A') ≫ (β_ (𝟙_ M.PureObject) A').hom
  rw [Category.assoc, braiding_naturality_left, ← Category.assoc, hc']

/-- Discarding both copied outputs is the scalar zero split after discard. -/
theorem pure_copy_discard_both (A : τ) (hc : Quantity.relevant ≤ quantity A)
    (hd : Quantity.affine ≤ quantity A) :
    (show (⟨A⟩ : M.PureObject) ⟶ (⟨A⟩ : M.PureObject) ⊗ (⟨A⟩ : M.PureObject)
      from ⟨M.copy A hc, M.copy_pure _ _⟩) ≫
      ((show (⟨A⟩ : M.PureObject) ⟶ 𝟙_ M.PureObject from ⟨M.discard A hd, M.discard_pure _ _⟩) ⊗ₘ
       (show (⟨A⟩ : M.PureObject) ⟶ 𝟙_ M.PureObject from ⟨M.discard A hd, M.discard_pure _ _⟩)) =
      (show (⟨A⟩ : M.PureObject) ⟶ 𝟙_ M.PureObject from ⟨M.discard A hd, M.discard_pure _ _⟩) ≫
        (λ_ (𝟙_ M.PureObject)).inv := by
  rw [tensorHom_def, ← Category.assoc, pure_copy_discard_left]
  exact (leftUnitor_inv_naturality _).symm

set_option linter.unusedTactic false in
/-- Every compatible scalar weakening square commutes, including an admissible
choice to copy a value and discard one or both copies. -/
theorem slotWeaken_split {A : τ} {q q' ql qr ql' qr' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A))
    (s : QCtx.SlotSplit A q ql qr) (t : QCtx.SlotSplit A q' ql' qr')
    (hl : Usage.effective ql' (quantity A) ≤ Usage.effective ql (quantity A))
    (hr : Usage.effective qr' (quantity A) ≤ Usage.effective qr (quantity A)) :
    slotWeaken M h ≫ slotSplit M t = slotSplit M s ≫ (slotWeaken M hl ⊗ₘ slotWeaken M hr) := by
  cases q <;> cases q' <;> cases ql <;> cases qr <;> cases ql' <;> cases qr'
  all_goals try (solve | cases s)
  all_goals try (solve | cases t)
  all_goals try (solve | exact False.elim h)
  all_goals try (solve | exact False.elim hl)
  all_goals try (solve | exact False.elim hr)
  all_goals simp only [slotWeaken, slotSplit, slotObject]
  all_goals try simp only [tensorHom_id, id_tensorHom, id_whiskerRight, Category.id_comp, Category.comp_id]
  all_goals try exact (pure_copy_discard_both M _ _ _).symm
  all_goals try exact (pure_copy_discard_left M _ _ _).symm
  all_goals try exact (pure_copy_discard_right M _ _ _).symm
  all_goals try exact leftUnitor_inv_naturality (C := M.PureObject) _
  all_goals rw [unitors_inv_equal]
  all_goals exact rightUnitor_inv_naturality (C := M.PureObject) _


set_option backward.isDefEq.respectTransparency false in
/-- Appending a variable preserves a compatible context weakening/splitting square. -/
theorem weakenSlot_splitSlot {L B D L' B' D' A : τ}
    (f : PureHom M L (product B D)) (g : PureHom M L' (product B' D'))
    (u : PureHom M L L') (ul : PureHom M B B') (ur : PureHom M D D')
    (hf : pureCompose M u g = pureCompose M f (pureTensor M ul ur))
    {q q' ql qr ql' qr' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A))
    (s : QCtx.SlotSplit A q ql qr) (t : QCtx.SlotSplit A q' ql' qr')
    (hl : Usage.effective ql' (quantity A) ≤ Usage.effective ql (quantity A))
    (hr : Usage.effective qr' (quantity A) ≤ Usage.effective qr (quantity A)) :
    pureCompose M (weakenSlot M u h) (splitSlot M g t) =
      pureCompose M (splitSlot M f s) (pureTensor M (weakenSlot M ul hl) (weakenSlot M ur hr)) := by
  change (weakenSlot M u h : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫ splitSlot M g t =
    (splitSlot M f s : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫
      ((show (⟨retain B A ql⟩ : M.PureObject) ⟶ (⟨retain B' A ql'⟩ : M.PureObject) from weakenSlot M ul hl) ⊗ₘ
       (show (⟨retain D A qr⟩ : M.PureObject) ⟶ (⟨retain D' A qr'⟩ : M.PureObject) from weakenSlot M ur hr))
  rw [weakenSlot_tensor, splitSlot_tensor, splitSlot_tensor, weakenSlot_tensor, weakenSlot_tensor]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  have hh : (show (⟨L⟩ : M.PureObject) ⟶ (⟨L'⟩ : M.PureObject) from u) ≫ g =
      f ≫ ((show (⟨B⟩ : M.PureObject) ⟶ (⟨B'⟩ : M.PureObject) from ul) ⊗ₘ
        (show (⟨D⟩ : M.PureObject) ⟶ (⟨D'⟩ : M.PureObject) from ur)) := hf
  rw [hh, slotWeaken_split M h s t hl hr]
  simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [tensorμ_natural_assoc]
  simp only [tensorHom_comp_tensorHom]

end Denotation
end Silmaril.Isotope.Refinement.Models

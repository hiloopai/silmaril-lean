module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Slots
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ResourceNaturality

/-! # Splitting commutes with pure comparisons of retained value types -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A pure type map acts on a slot when both contexts retain that position. -/
def slotTypeMap {A B : τ} (f : PureHom M A B) {q r : Usage} (h : q = .zero ↔ r = .zero) :
    slotObject M A q ⟶ slotObject M B r := by
  cases q with
  | zero =>
    cases r with
    | zero => exact 𝟙 _
    | used => exact False.elim (Usage.noConfusion (h.mp rfl))
  | used =>
    cases r with
    | zero => exact False.elim (Usage.noConfusion (h.mpr rfl))
    | used => exact f

/-- A simultaneous quantity-valid split is natural for every pure type comparison. -/
theorem slotTypeMap_split {A B : τ} (f : PureHom M A B) {q ql qr r rl rr : Usage}
    (s : QCtx.SlotSplit A q ql qr) (t : QCtx.SlotSplit B r rl rr)
    (h : q = .zero ↔ r = .zero) (hl : ql = .zero ↔ rl = .zero) (hr : qr = .zero ↔ rr = .zero) :
    slotTypeMap M f h ≫ slotSplit M t =
      slotSplit M s ≫ (slotTypeMap M f hl ⊗ₘ slotTypeMap M f hr) := by
  cases s with
  | left =>
    cases t with
    | left =>
      cases q <;> cases r
      · simp [slotTypeMap, slotSplit, slotObject]
      · exact False.elim (Usage.noConfusion (h.mp rfl))
      · exact False.elim (Usage.noConfusion (h.mpr rfl))
      · change f ≫ (ρ_ (⟨B⟩ : M.PureObject)).inv = (ρ_ (⟨A⟩ : M.PureObject)).inv ≫ (f ⊗ₘ 𝟙 _)
        simp
    | right =>
      have hq := hl.mpr rfl
      have hr' := hr.mp rfl
      subst q
      subst r
      simp [slotTypeMap, slotSplit, slotObject]
    | both hc =>
      have he := hr.mp rfl
      subst r
      exact False.elim hc
  | right =>
    cases t with
    | left =>
      have hq := hr.mpr rfl
      have hr' := hl.mp rfl
      subst q
      subst r
      simp [slotTypeMap, slotSplit, slotObject]
    | right =>
      cases q <;> cases r
      · simp [slotTypeMap, slotSplit, slotObject]
      · exact False.elim (Usage.noConfusion (h.mp rfl))
      · exact False.elim (Usage.noConfusion (h.mpr rfl))
      · change f ≫ (λ_ (⟨B⟩ : M.PureObject)).inv = (λ_ (⟨A⟩ : M.PureObject)).inv ≫ (𝟙 _ ⊗ₘ f)
        simp
    | both hc =>
      have he := hl.mp rfl
      subst r
      exact False.elim hc
  | both hc =>
    cases t with
    | left =>
      have he := hr.mpr rfl
      subst q
      exact False.elim hc
    | right =>
      have he := hl.mpr rfl
      subst q
      exact False.elim hc
    | both hd =>
      cases q with
      | zero => exact False.elim hc
      | used q =>
        cases r with
        | zero => exact False.elim hd
        | used r =>
          apply Subtype.ext
          exact M.pure_copy_natural f.1 f.2 _ _

/-- Extend a pure context map by a comparison of aligned newest slots. -/
def retainTypeMap {L K A B : τ} (f : PureHom M L K) (a : PureHom M A B)
    {q r : Usage} (h : q = .zero ↔ r = .zero) : PureHom M (retain L A q) (retain K B r) :=
  (retainIso M L A q).hom ≫
    ((show (⟨L⟩ : M.PureObject) ⟶ (⟨K⟩ : M.PureObject) from f) ⊗ₘ slotTypeMap M a h) ≫
    (retainIso M K B r).inv

@[simp] theorem retainTypeMap_zero {L K A B : τ} (f : PureHom M L K) (a : PureHom M A B)
    (h : Usage.zero = .zero ↔ Usage.zero = .zero) : retainTypeMap M f a h = f := by
  change (ρ_ (⟨L⟩ : M.PureObject)).inv ≫ (f ⊗ₘ 𝟙 (𝟙_ M.PureObject)) ≫ (ρ_ (⟨K⟩ : M.PureObject)).hom = f
  simp

@[simp] theorem retainTypeMap_used {L K A B : τ} (f : PureHom M L K) (a : PureHom M A B)
    (q r : Quantity) (h : Usage.used q = .zero ↔ Usage.used r = .zero) :
    retainTypeMap M f a h = pureTensor M f a := by
  change 𝟙 (⟨product L A⟩ : M.PureObject) ≫
    (show (⟨product L A⟩ : M.PureObject) ⟶ (⟨product K B⟩ : M.PureObject) from pureTensor M f a) ≫
    𝟙 (⟨product K B⟩ : M.PureObject) = pureTensor M f a
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Appending a pure type comparison preserves any compatible context splitting square. -/
theorem retainTypeMap_splitSlot {L B D L' B' D' A A' : τ}
    (f : PureHom M L (product B D)) (g : PureHom M L' (product B' D'))
    (u : PureHom M L L') (ul : PureHom M B B') (ur : PureHom M D D')
    (a : PureHom M A A')
    (hf : pureCompose M u g = pureCompose M f (pureTensor M ul ur))
    {q q' ql qr ql' qr' : Usage}
    (h : q = .zero ↔ q' = .zero)
    (s : QCtx.SlotSplit A q ql qr) (t : QCtx.SlotSplit A' q' ql' qr')
    (hl : ql = .zero ↔ ql' = .zero) (hr : qr = .zero ↔ qr' = .zero) :
    pureCompose M (retainTypeMap M u a h) (splitSlot M g t) =
      pureCompose M (splitSlot M f s)
        (pureTensor M (retainTypeMap M ul a hl) (retainTypeMap M ur a hr)) := by
  change (retainTypeMap M u a h : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫ splitSlot M g t =
    (splitSlot M f s : (⟨retain L A q⟩ : M.PureObject) ⟶ _) ≫
      ((show (⟨retain B A ql⟩ : M.PureObject) ⟶ (⟨retain B' A' ql'⟩ : M.PureObject) from retainTypeMap M ul a hl) ⊗ₘ
       (show (⟨retain D A qr⟩ : M.PureObject) ⟶ (⟨retain D' A' qr'⟩ : M.PureObject) from retainTypeMap M ur a hr))
  rw [retainTypeMap.eq_def, splitSlot_tensor, splitSlot_tensor, retainTypeMap.eq_def, retainTypeMap.eq_def]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  have hh : (show (⟨L⟩ : M.PureObject) ⟶ (⟨L'⟩ : M.PureObject) from u) ≫ g =
      f ≫ ((show (⟨B⟩ : M.PureObject) ⟶ (⟨B'⟩ : M.PureObject) from ul) ⊗ₘ
        (show (⟨D⟩ : M.PureObject) ⟶ (⟨D'⟩ : M.PureObject) from ur)) := hf
  rw [hh, slotTypeMap_split M a s t h hl hr]
  simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [tensorμ_natural_assoc]
  simp only [tensorHom_comp_tensorHom]

end Silmaril.Isotope.Refinement.Models.Denotation

namespace Silmaril.Isotope.Refinement.Models.Structural
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Naturality of tensoring two splitting diagrams. -/
theorem tensorSplit_natural {L K D E D' E' A B Al Ar Bl Br : C}
    (f : L ⟶ D ⊗ E) (g : K ⟶ D' ⊗ E') (w : L ⟶ K) (wl : D ⟶ D') (wr : E ⟶ E')
    (s : A ⟶ Al ⊗ Ar) (t : B ⟶ Bl ⊗ Br) (a : A ⟶ B) (al : Al ⟶ Bl) (ar : Ar ⟶ Br)
    (hw : w ≫ g = f ≫ (wl ⊗ₘ wr)) (ha : a ≫ t = s ≫ (al ⊗ₘ ar)) :
    (w ⊗ₘ a) ≫ (g ⊗ₘ t) ≫ tensorμ D' E' Bl Br =
      (f ⊗ₘ s) ≫ tensorμ D E Al Ar ≫ ((wl ⊗ₘ al) ⊗ₘ (wr ⊗ₘ ar)) := by
  rw [tensorHom_comp_tensorHom_assoc, hw, ha, ← tensorHom_comp_tensorHom_assoc,
    tensorμ_natural]

end Silmaril.Isotope.Refinement.Models.Structural

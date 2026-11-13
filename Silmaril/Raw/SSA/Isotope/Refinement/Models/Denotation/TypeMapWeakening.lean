module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextTypeMap

/-! # Pure type comparisons commute with quantitative weakening -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Scalar pure comparison is natural for admissible quantity restriction. -/
theorem slotTypeMap_weaken {A B : τ} (f : PureHom M A B) {q q' r r' : Usage}
    (h : q = .zero ↔ r = .zero) (h' : q' = .zero ↔ r' = .zero)
    (ha : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A))
    (hb : Usage.effective r' (quantity B) ≤ Usage.effective r (quantity B)) :
    slotTypeMap M f h ≫ slotWeaken M hb = slotWeaken M ha ≫ slotTypeMap M f h' := by
  cases q <;> cases r <;> cases q' <;> cases r'
  all_goals try (solve | exact False.elim ha | exact False.elim hb)
  all_goals try (solve
    | exact False.elim (Usage.noConfusion (h.mp rfl))
    | exact False.elim (Usage.noConfusion (h.mpr rfl))
    | exact False.elim (Usage.noConfusion (h'.mp rfl))
    | exact False.elim (Usage.noConfusion (h'.mpr rfl)))
  all_goals simp only [slotTypeMap, slotWeaken, slotObject, Category.id_comp, Category.comp_id]
  apply Subtype.ext
  exact M.pure_discard_natural f.1 f.2 _ _

set_option backward.isDefEq.respectTransparency false in
/-- Appending a slot preserves a compatible type-comparison/weakening square. -/
theorem retainTypeMap_weakenSlot {L K L' K' A B : τ}
    (f : PureHom M L K) (g : PureHom M L' K') (wl : PureHom M L L') (wr : PureHom M K K')
    (a : PureHom M A B) (hf : pureCompose M f wr = pureCompose M wl g)
    {q q' r r' : Usage} (h : q = .zero ↔ r = .zero) (h' : q' = .zero ↔ r' = .zero)
    (ha : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A))
    (hb : Usage.effective r' (quantity B) ≤ Usage.effective r (quantity B)) :
    pureCompose M (retainTypeMap M f a h) (weakenSlot M wr hb) =
      pureCompose M (weakenSlot M wl ha) (retainTypeMap M g a h') := by
  change (retainTypeMap M f a h : (⟨retain L A q⟩ : M.PureObject) ⟶ (⟨retain K B r⟩ : M.PureObject)) ≫
      (show (⟨retain K B r⟩ : M.PureObject) ⟶ (⟨retain K' B r'⟩ : M.PureObject) from weakenSlot M wr hb) =
    (weakenSlot M wl ha : (⟨retain L A q⟩ : M.PureObject) ⟶ (⟨retain L' A q'⟩ : M.PureObject)) ≫
      (show (⟨retain L' A q'⟩ : M.PureObject) ⟶ (⟨retain K' B r'⟩ : M.PureObject) from retainTypeMap M g a h')
  rw [retainTypeMap.eq_def, weakenSlot_tensor, weakenSlot_tensor, retainTypeMap.eq_def]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  have hh : (show (⟨L⟩ : M.PureObject) ⟶ (⟨K⟩ : M.PureObject) from f) ≫ wr = wl ≫ g := hf
  rw [hh, slotTypeMap_weaken M a h h' ha hb]

/-- Native weakening for pointwise equal value types and admissible quantities. -/
theorem pointwiseWeakening {n : Nat} (A : Fin n → τ) (q q' : Fin n → Usage)
    (h : ∀ i, Usage.effective (q' i) (quantity (A i)) ≤ Usage.effective (q i) (quantity (A i))) :
    QCtx.Weakening (fun i => (A i, q i)) (fun i => (A i, q' i)) id := by
  induction n with
  | zero =>
    convert QCtx.Weakening.nil (τ := τ) using 1
  | succ n ih =>
    have hw := QCtx.Weakening.cons (A := A 0)
      (ih (fun i => A i.succ) (fun i => q i.succ) (fun i => q' i.succ) (fun i => h i.succ)) (h 0)
    convert hw using 1
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · funext i; exact Fin.cases rfl (fun _ => rfl) i

set_option backward.isDefEq.respectTransparency false in
/-- Packing pointwise pure maps commutes with native quantity weakening. -/
theorem contextTypeMap_weaken {n : Nat} (A B : Fin n → τ) (q q' r r' : Fin n → Usage)
    (f : ∀ i, PureHom M (A i) (B i))
    (h : ∀ i, q i = .zero ↔ r i = .zero) (h' : ∀ i, q' i = .zero ↔ r' i = .zero)
    (ha : ∀ i, Usage.effective (q' i) (quantity (A i)) ≤ Usage.effective (q i) (quantity (A i)))
    (hb : ∀ i, Usage.effective (r' i) (quantity (B i)) ≤ Usage.effective (r i) (quantity (B i))) :
    pureCompose M (contextTypeMap M A B q r f h) (weakenPure M (pointwiseWeakening B r r' hb)) =
      pureCompose M (weakenPure M (pointwiseWeakening A q q' ha)) (contextTypeMap M A B q' r' f h') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact retainTypeMap_weakenSlot M _ _ _ _ (f 0)
      (ih (fun i => A i.succ) (fun i => B i.succ)
        (fun i => q i.succ) (fun i => q' i.succ) (fun i => r i.succ) (fun i => r' i.succ)
        (fun i => f i.succ) (fun i => h i.succ) (fun i => h' i.succ)
        (fun i => ha i.succ) (fun i => hb i.succ))
      (h 0) (h' 0) (ha 0) (hb 0)

end Silmaril.Isotope.Refinement.Models.Denotation

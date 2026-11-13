module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Contexts
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextSplitting

@[expose] public section

namespace Silmaril.Isotope.Refinement.Models

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {M N : SeqData.{u,v,w,r} τ Φ ε}

namespace SeqData
open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

@[simp] theorem right_identity (M : SeqData.{u,v,w,r} τ Φ ε) (A B : τ) :
    M.right (M.identity A) B = M.identity (product A B) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [right, identity]

@[simp] theorem left_identity (M : SeqData.{u,v,w,r} τ Φ ε) (A B : τ) :
    M.left A (M.identity B) = M.identity (product A B) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [left, identity]

theorem right_compose (M : SeqData.{u,v,w,r} τ Φ ε) {A B D : τ}
    (f : M.Hom A B) (g : M.Hom B D) (E : τ) :
    M.right (M.compose f g) E = M.compose (M.right f E) (M.right g E) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [right, compose, PremonoidalCategory.comp_whiskerRight, Category.assoc]

theorem left_compose (M : SeqData.{u,v,w,r} τ Φ ε) (A : τ) {B D E : τ}
    (f : M.Hom B D) (g : M.Hom D E) :
    M.left A (M.compose f g) = M.compose (M.left A f) (M.left A g) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [left, compose, PremonoidalCategory.whiskerLeft_comp, Category.assoc]

@[simp] theorem associator_hom_inv (M : SeqData.{u,v,w,r} τ Φ ε) (A B D : τ) :
    M.compose (M.associator A B D) (M.associatorInv A B D) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, associator, associatorInv, identity, Category.assoc]

@[simp] theorem associator_inv_hom (M : SeqData.{u,v,w,r} τ Φ ε) (A B D : τ) :
    M.compose (M.associatorInv A B D) (M.associator A B D) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, associator, associatorInv, identity, Category.assoc]

@[simp] theorem leftUnitor_hom_inv (M : SeqData.{u,v,w,r} τ Φ ε) (A : τ) :
    M.compose (M.leftUnitor A) (M.leftUnitorInv A) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, leftUnitor, leftUnitorInv, identity, Category.assoc]

@[simp] theorem leftUnitor_inv_hom (M : SeqData.{u,v,w,r} τ Φ ε) (A : τ) :
    M.compose (M.leftUnitorInv A) (M.leftUnitor A) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, leftUnitor, leftUnitorInv, identity, Category.assoc]

@[simp] theorem rightUnitor_hom_inv (M : SeqData.{u,v,w,r} τ Φ ε) (A : τ) :
    M.compose (M.rightUnitor A) (M.rightUnitorInv A) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, rightUnitor, rightUnitorInv, identity, Category.assoc]

@[simp] theorem rightUnitor_inv_hom (M : SeqData.{u,v,w,r} τ Φ ε) (A : τ) :
    M.compose (M.rightUnitorInv A) (M.rightUnitor A) = M.identity _ := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp [compose, rightUnitor, rightUnitorInv, identity, Category.assoc]

end SeqData
namespace Denotation

theorem map_weakenSlot (φ : M.HomMap N) {L B A : τ} (f : PureHom M L B) {q q' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    φ.map (weakenSlot M f h).1 = (weakenSlot N (mapPure φ f) h).1 := by
  cases q <;> cases q'
  · rfl
  · exact False.elim h
  · exact map_dropRight φ f A _
  · exact φ.right f.1 A

/-- Interpreting native context weakening commutes with every model map. -/
theorem map_weaken (φ : M.HomMap N) {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ) :
    φ.map (weaken M h) = weaken N h := by
  induction h with
  | nil => exact φ.identity _
  | cons h hq ih =>
    change φ.map (weakenSlot M (weakenPure M h) hq).1 =
      (weakenSlot N (weakenPure N h) hq).1
    rw [map_weakenSlot]
    have he : mapPure φ (weakenPure M h) = weakenPure N h := Subtype.ext ih
    rw [he]
  | @skip n m Γ Δ ρ A q h hq ih =>
    cases m with
    | zero => exact φ.discard _ _
    | succ m =>
      cases q with
      | zero => exact ih
      | used q =>
        have ha : Quantity.affine ≤ quantity A :=
          ((Usage.zero_le_effective_iff _ _).mp hq).trans inf_le_left
        change φ.map (dropRight M (weakenPure M h) A ha).1 =
          (dropRight N (weakenPure N h) A ha).1
        rw [map_dropRight]
        have he : mapPure φ (weakenPure M h) = weakenPure N h := Subtype.ext ih
        rw [he]

/-- Reflexive native weakening denotes the categorical identity. -/
@[simp] theorem weaken_refl (M : SeqData.{u,v,w,r} τ Φ ε) {n : Nat} (Γ : QCtx τ n) :
    weaken M (QCtx.Weakening.refl Γ) = M.identity (packed Γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs (Γt : QCtx τ n) (A : τ) (q : Usage) :
        weaken M (QCtx.Weakening.refl (Γt.snoc A q)) = M.identity (packed (Γt.snoc A q)) := by
      cases q with
      | zero => exact ih Γt
      | used q =>
        change M.right (weaken M (QCtx.Weakening.refl Γt)) A = M.identity (product (packed Γt) A)
        rw [ih, M.right_identity]
    let P (G : QCtx τ (n + 1)) := weaken M (QCtx.Weakening.refl G) = M.identity (packed G)
    exact (congrArg P (QCtx.snoc_tail Γ)).mp (hs _ _ _)

/-- Splitting the empty context is the canonical unit diagonal. -/
@[simp] theorem split_nil (M : SeqData.{u,v,w,r} τ Φ ε) :
    split M (QCtx.Split.nil (τ := τ)) = M.leftUnitorInv Silmaril.unit := rfl

/-- Discarding the empty context is the identity of the tensor unit. -/
@[simp] theorem discard_nil (M : SeqModel.{u,v,w,r} τ Φ ε)
    (h : (QCtx.nil : QCtx τ 0).Discardable) :
    discard M.toSeqData h = M.toSeqData.identity Silmaril.unit := M.discard_unit _

/-- Native diagonal splitting is exactly the model's chosen copy map.
This uses the specified copy equations at unit and product types. -/
theorem split_diagonal (M : SeqModel.{u,v,w,r} τ Φ ε) {n : Nat} (Γ : QCtx τ n)
    (h : Quantity.relevant ≤ Γ.linearity) :
    split M.toSeqData (QCtx.Split.diagonal Γ h) =
      M.toSeqData.copy (packed Γ) (h.trans (packed_quantity Γ)) := by
  induction n with
  | zero => exact (M.copy_unit _).symm
  | succ n ih =>
    have hs (Γt : QCtx τ n) (A : τ) (q : Usage) (hq : Quantity.relevant ≤ (Γt.snoc A q).linearity) :
        split M.toSeqData (QCtx.Split.diagonal (Γt.snoc A q) hq) =
          M.toSeqData.copy (packed (Γt.snoc A q)) (hq.trans (packed_quantity _)) := by
      have ht : Quantity.relevant ≤ Γt.linearity :=
        (show Quantity.relevant ≤ Usage.linearity q (quantity A) ⊓ Γt.linearity by
          simpa only [QCtx.linearity_snoc] using hq).trans inf_le_right
      cases q with
      | zero => exact ih Γt ht
      | used q =>
        have hA : Quantity.relevant ≤ quantity A :=
          (show Quantity.relevant ≤ (quantity A ⊓ q) ⊓ Γt.linearity by
            simpa only [QCtx.linearity_snoc, Usage.linearity_used] using hq).trans
              (inf_le_left.trans inf_le_left)
        change M.toSeqData.compose
          (M.toSeqData.tensor (split M.toSeqData (QCtx.Split.diagonal Γt ht)) (M.toSeqData.copy A hA))
          (M.toSeqData.middleSwap (packed Γt) (packed Γt) A A) = _
        rw [ih Γt ht]
        exact (M.copy_product _ _ _ _ _).symm
    let P (G : QCtx τ (n + 1)) := ∀ k : Quantity.relevant ≤ G.linearity,
      split M.toSeqData (QCtx.Split.diagonal G k) = M.toSeqData.copy (packed G) (k.trans (packed_quantity G))
    exact ((congrArg P (QCtx.snoc_tail Γ)).mp (hs _ _ _)) h

end Denotation
end Silmaril.Isotope.Refinement.Models

module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMapSplit

/-! # Naturality of whole context splits under pure type comparisons -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Pack a pointwise family of pure maps, retaining the same variable positions. -/
def contextTypeMap : {n : Nat} → (A B : Fin n → τ) → (q r : Fin n → Usage) →
    (∀ i, PureHom M (A i) (B i)) → (∀ i, q i = .zero ↔ r i = .zero) →
    PureHom M (packed (fun i => (A i, q i))) (packed (fun i => (B i, r i))) := by
  intro n
  induction n with
  | zero => intro A B q r f h; exact ⟨M.identity _, M.identity_effect ⊥ _⟩
  | succ n ih =>
    intro A B q r f h
    exact retainTypeMap M
      (ih (fun i => A i.succ) (fun i => B i.succ) (fun i => q i.succ) (fun i => r i.succ)
        (fun i => f i.succ) (fun i => h i.succ)) (f 0) (h 0)

/-- A pointwise split has literal, shared value types in its three contexts. -/
theorem pointwiseSplit {n : Nat} (A : Fin n → τ) (q ql qr : Fin n → Usage)
    (s : ∀ i, QCtx.SlotSplit (A i) (q i) (ql i) (qr i)) :
    QCtx.Split (fun i => (A i, q i)) (fun i => (A i, ql i)) (fun i => (A i, qr i)) :=
  fun i => ⟨rfl, rfl, s i⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise pure maps commute with any pair of aligned quantitative context splits. -/
theorem contextTypeMap_split {n : Nat} (A B : Fin n → τ) (q ql qr r rl rr : Fin n → Usage)
    (f : ∀ i, PureHom M (A i) (B i))
    (s : ∀ i, QCtx.SlotSplit (A i) (q i) (ql i) (qr i))
    (t : ∀ i, QCtx.SlotSplit (B i) (r i) (rl i) (rr i))
    (h : ∀ i, q i = .zero ↔ r i = .zero)
    (hl : ∀ i, ql i = .zero ↔ rl i = .zero) (hr : ∀ i, qr i = .zero ↔ rr i = .zero) :
    pureCompose M (contextTypeMap M A B q r f h) (splitPure M (pointwiseSplit B r rl rr t)) =
      pureCompose M (splitPure M (pointwiseSplit A q ql qr s))
        (pureTensor M (contextTypeMap M A B ql rl f hl) (contextTypeMap M A B qr rr f hr)) := by
  induction n with
  | zero =>
    change 𝟙 (𝟙_ M.PureObject) ≫ (λ_ (𝟙_ M.PureObject)).inv =
      (λ_ (𝟙_ M.PureObject)).inv ≫ (𝟙 (𝟙_ M.PureObject) ⊗ₘ 𝟙 (𝟙_ M.PureObject))
    simp
  | succ n ih =>
    exact retainTypeMap_splitSlot M _ _ _ _ _ (f 0)
      (ih (fun i => A i.succ) (fun i => B i.succ)
        (fun i => q i.succ) (fun i => ql i.succ) (fun i => qr i.succ)
        (fun i => r i.succ) (fun i => rl i.succ) (fun i => rr i.succ)
        (fun i => f i.succ) (fun i => s i.succ) (fun i => t i.succ)
        (fun i => h i.succ) (fun i => hl i.succ) (fun i => hr i.succ))
      (h 0) (s 0) (t 0) (hl 0) (hr 0)

end Silmaril.Isotope.Refinement.Models.Denotation

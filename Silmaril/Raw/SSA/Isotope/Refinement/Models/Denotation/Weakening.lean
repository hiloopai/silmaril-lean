module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Pure
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextComposition
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

@[expose] public section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Discard is natural for pure computations between discardable types. -/
theorem pure_discard_natural {A B : τ} (f : M.Hom A B) (hf : M.hasEffect ⊥ f)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B) :
    M.compose f (M.discard B hB) = M.discard A hA := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have he : f ≫ M.copyDiscard.discard B hB = M.copyDiscard.discard A hA :=
    le_antisymm
      (M.copyDiscard.discard_natural .positive f hA hB (EffectSystem.canDelete_pure _) hf)
      (M.copyDiscard.discard_natural .negative f hA hB (EffectSystem.canDelete_pure _) hf)
  simpa only [compose, discard, Category.assoc] using
    congrArg (fun g => g ≫ eqToHom M.tensor_unit) he

end SeqData
namespace Denotation
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Dropping a final slot commutes with every pure map on the retained context. -/
theorem dropRight_compose {L B D A : τ} (f : PureHom M L B) (g : PureHom M B D)
    (h : Quantity.affine ≤ quantity A) :
    pureCompose M (dropRight M f A h) g = dropRight M (pureCompose M f g) A h := by
  let L' : M.PureObject := ⟨L⟩
  let B' : M.PureObject := ⟨B⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let ff : L' ⟶ B' := f
  let gg : B' ⟶ D' := g
  let d : A' ⟶ 𝟙_ M.PureObject := ⟨M.discard A h, M.discard_pure _ _⟩
  change (ff ▷ A' ≫ B' ◁ d ≫ (ρ_ B').hom) ≫ gg =
    (ff ≫ gg) ▷ A' ≫ D' ◁ d ≫ (ρ_ D').hom
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.rightUnitor_naturality gg, ← MonoidalCategory.whisker_exchange_assoc gg d]

/-- Append a slot and subsequently discard it after a pure context map. -/
theorem right_dropRight {L B D A : τ} (f : PureHom M L B) (g : PureHom M B D)
    (h : Quantity.affine ≤ quantity A) :
    pureCompose M (pureRight M f A) (dropRight M g A h) = dropRight M (pureCompose M f g) A h := by
  apply Subtype.ext
  change M.compose (M.right f.1 A) (M.compose (M.right g.1 A) _) =
    M.compose (M.right (M.compose f.1 g.1) A) _
  rw [M.right_compose, M.compose_assoc]

/-- Quantity restriction is compatible with composition of pure context maps. -/
theorem weakenSlot_compose {L B D A : τ} (f : PureHom M L B) (g : PureHom M B D)
    {q q' q'' : Usage}
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A))
    (k : Usage.effective q'' (quantity A) ≤ Usage.effective q' (quantity A)) :
    pureCompose M (weakenSlot M f h) (weakenSlot M g k) =
      weakenSlot M (pureCompose M f g) (k.trans h) := by
  cases q <;> cases q' <;> cases q''
  · rfl
  · exact False.elim k
  · exact False.elim h
  · exact False.elim h
  · exact dropRight_compose M f g _
  · exact False.elim k
  · exact right_dropRight M f g _
  · exact Subtype.ext (M.right_compose f.1 g.1 A).symm

/-- Weakening to an empty target agrees with the model's chosen discard. -/
theorem weaken_nil (M : SeqModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {Δ : QCtx τ 0}
    {ρ : Fin 0 → Fin n} (h : QCtx.Weakening Γ Δ ρ) :
    weaken M.toSeqData h = discard M.toSeqData (fun i => h.omitted i (fun j => Fin.elim0 j)) := by
  cases n with
  | zero => exact (M.discard_unit _).symm
  | succ n => rfl

theorem weaken_comp_nil (M : SeqModel.{u,v,w,r} τ Φ ε) {n m : Nat}
    {Γ : QCtx τ n} {Δ : QCtx τ m} {Θ : QCtx τ 0}
    {ρ : Fin m → Fin n} {σ : Fin 0 → Fin m}
    (h : QCtx.Weakening Γ Δ ρ) (g : QCtx.Weakening Δ Θ σ) :
    weakenPure M.toSeqData (h.comp g) = pureCompose M.toSeqData (weakenPure M.toSeqData h) (weakenPure M.toSeqData g) := by
  apply Subtype.ext
  change weaken M.toSeqData (h.comp g) = M.toSeqData.compose (weaken M.toSeqData h) (weaken M.toSeqData g)
  rw [weaken_nil, weaken_nil M g]
  exact (M.toSeqData.pure_discard_natural _ (weaken_pure _ h) _ _).symm

/-- Native weakening composition is interpreted by categorical composition. -/
theorem weakenPure_comp (M : SeqModel.{u,v,w,r} τ Φ ε) {n m k : Nat}
    {Γ : QCtx τ n} {Δ : QCtx τ m} {Θ : QCtx τ k}
    {ρ : Fin m → Fin n} {σ : Fin k → Fin m}
    (h : QCtx.Weakening Γ Δ ρ) (g : QCtx.Weakening Δ Θ σ) :
    weakenPure M.toSeqData (h.comp g) = pureCompose M.toSeqData (weakenPure M.toSeqData h) (weakenPure M.toSeqData g) := by
  induction h generalizing k with
  | nil =>
    cases g
    exact Subtype.ext (M.toSeqData.identity_compose _).symm
  | @cons n m Γ Δ ρ A q q' h hq ih =>
    cases k with
    | zero => exact weaken_comp_nil M _ g
    | succ k =>
      rcases g.cases_snoc with ⟨Θt, q'', σt, rfl, rfl, gt, hg⟩ | ⟨σt, rfl, gt, hg⟩
      ·
        change weakenSlot M.toSeqData (weakenPure M.toSeqData (h.comp gt)) (hg.trans hq) =
          pureCompose M.toSeqData (weakenSlot M.toSeqData (weakenPure M.toSeqData h) hq)
            (weakenSlot M.toSeqData (weakenPure M.toSeqData gt) hg)
        rw [ih gt, weakenSlot_compose]
      ·
        cases q <;> cases q'
        · exact ih gt
        · exact False.elim hq
        · have ha : Quantity.affine ≤ quantity A :=
            ((Usage.zero_le_effective_iff _ _).mp hq).trans inf_le_left
          change dropRight M.toSeqData (weakenPure M.toSeqData (h.comp gt)) A ha =
            pureCompose M.toSeqData (dropRight M.toSeqData (weakenPure M.toSeqData h) A ha)
              (weakenPure M.toSeqData gt)
          rw [ih gt, dropRight_compose]
        · have ha : Quantity.affine ≤ quantity A :=
            ((Usage.zero_le_effective_iff _ _).mp hg).trans inf_le_left
          change dropRight M.toSeqData (weakenPure M.toSeqData (h.comp gt)) A ha =
            pureCompose M.toSeqData (pureRight M.toSeqData (weakenPure M.toSeqData h) A)
              (dropRight M.toSeqData (weakenPure M.toSeqData gt) A ha)
          rw [ih gt, right_dropRight]
  | @skip n m Γ Δ ρ A q h hq ih =>
    cases k with
    | zero => exact weaken_comp_nil M _ g
    | succ k =>
      cases m with
      | zero => exact Fin.elim0 (σ 0)
      | succ m =>
        cases q with
        | zero => exact ih g
        | used q =>
          have ha : Quantity.affine ≤ quantity A :=
            ((Usage.zero_le_effective_iff _ _).mp hq).trans inf_le_left
          change dropRight M.toSeqData (weakenPure M.toSeqData (h.comp g)) A ha =
            pureCompose M.toSeqData (dropRight M.toSeqData (weakenPure M.toSeqData h) A ha)
              (weakenPure M.toSeqData g)
          rw [ih g, dropRight_compose]

theorem weaken_comp (M : SeqModel.{u,v,w,r} τ Φ ε) {n m k : Nat}
    {Γ : QCtx τ n} {Δ : QCtx τ m} {Θ : QCtx τ k}
    {ρ : Fin m → Fin n} {σ : Fin k → Fin m}
    (h : QCtx.Weakening Γ Δ ρ) (g : QCtx.Weakening Δ Θ σ) :
    weaken M.toSeqData (h.comp g) = M.toSeqData.compose (weaken M.toSeqData h) (weaken M.toSeqData g) :=
  congrArg Subtype.val (weakenPure_comp M h g)

end Denotation
end Silmaril.Isotope.Refinement.Models

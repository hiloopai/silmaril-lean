module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMapWeakening

/-! # Variable and discard naturality under pure changes of value types -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Pure maps between discardable contexts commute with the chosen context discard. -/
theorem contextTypeMap_discard {n : Nat} (A B : Fin n → τ) (q r : Fin n → Usage)
    (f : ∀ i, PureHom M (A i) (B i)) (h : ∀ i, q i = .zero ↔ r i = .zero)
    (ha : QCtx.Discardable (fun i => (A i, q i))) (hb : QCtx.Discardable (fun i => (B i, r i))) :
    pureCompose M (contextTypeMap M A B q r f h) ⟨discard M hb, discard_pure M hb⟩ =
      ⟨discard M ha, discard_pure M ha⟩ :=
  Subtype.ext (M.pure_discard_natural _ (contextTypeMap M A B q r f h).2 _ _)

/-- Tensoring a pure value map commutes with dropping that final value. -/
theorem pureTensor_dropRight {L K D A B : τ} (f : PureHom M L K) (a : PureHom M A B)
    (g : PureHom M K D) (ha : Quantity.affine ≤ quantity A) (hb : Quantity.affine ≤ quantity B) :
    pureCompose M (pureTensor M f a) (dropRight M g B hb) =
      dropRight M (pureCompose M f g) A ha := by
  let L' : M.PureObject := ⟨L⟩
  let K' : M.PureObject := ⟨K⟩
  let D' : M.PureObject := ⟨D⟩
  let A' : M.PureObject := ⟨A⟩
  let B' : M.PureObject := ⟨B⟩
  let da : A' ⟶ 𝟙_ M.PureObject := ⟨M.discard A ha, M.discard_pure _ _⟩
  let db : B' ⟶ 𝟙_ M.PureObject := ⟨M.discard B hb, M.discard_pure _ _⟩
  have hd : (show A' ⟶ B' from a) ≫ db = da := Subtype.ext (M.pure_discard_natural a.1 a.2 ha hb)
  change ((show L' ⟶ K' from f) ⊗ₘ (show A' ⟶ B' from a)) ≫
      ((show K' ⟶ D' from g) ▷ B' ≫ D' ◁ db ≫ (ρ_ D').hom) =
    ((show L' ⟶ K' from f) ≫ g) ▷ A' ≫ D' ◁ da ≫ (ρ_ D').hom
  rw [← Category.assoc (g ▷ B') (D' ◁ db), ← tensorHom_def, ← Category.assoc, tensorHom_comp_tensorHom, hd, tensorHom_def, Category.assoc]

/-- Tensoring a pure context map commutes with selecting the newest variable. -/
theorem pureTensor_newest {L K A B : τ} (f : PureHom M L K) (a : PureHom M A B)
    (ha : Quantity.affine ≤ quantity L) (hb : Quantity.affine ≤ quantity K) :
    pureCompose M (pureTensor M f a)
      (pureCompose M (pureRight M ⟨M.discard K hb, M.discard_pure _ _⟩ B)
        ⟨M.leftUnitor B, M.leftUnitor_pure B⟩) =
    pureCompose M
      (pureCompose M (pureRight M ⟨M.discard L ha, M.discard_pure _ _⟩ A)
        ⟨M.leftUnitor A, M.leftUnitor_pure A⟩) a := by
  let L' : M.PureObject := ⟨L⟩
  let K' : M.PureObject := ⟨K⟩
  let A' : M.PureObject := ⟨A⟩
  let B' : M.PureObject := ⟨B⟩
  let dl : L' ⟶ 𝟙_ M.PureObject := ⟨M.discard L ha, M.discard_pure _ _⟩
  let dk : K' ⟶ 𝟙_ M.PureObject := ⟨M.discard K hb, M.discard_pure _ _⟩
  have hd : (show L' ⟶ K' from f) ≫ dk = dl := Subtype.ext (M.pure_discard_natural f.1 f.2 ha hb)
  change ((show L' ⟶ K' from f) ⊗ₘ (show A' ⟶ B' from a)) ≫ (dk ▷ B' ≫ (λ_ B').hom) =
    (dl ▷ A' ≫ (λ_ A').hom) ≫ (show A' ⟶ B' from a)
  rw [← Category.assoc, ← tensorHom_id dk, tensorHom_comp_tensorHom]
  simp only [Category.comp_id, hd, tensorHom_def, Category.assoc]
  rw [leftUnitor_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- Selecting a variable is natural for any pointwise pure comparison of retained types. -/
theorem contextTypeMap_variable {n : Nat} (Γ Δ : QCtx τ n)
    (f : ∀ i, PureHom M (Γ i).1 (Δ i).1)
    (h : ∀ i, (Γ i).2 = .zero ↔ (Δ i).2 = .zero) (i : Fin n)
    (ha : Γ.VarAllowed i) (hb : Δ.VarAllowed i) :
    pureCompose M (contextTypeMap M (fun i => (Γ i).1) (fun i => (Δ i).1)
      (fun i => (Γ i).2) (fun i => (Δ i).2) f h) (variablePure M i hb) =
      pureCompose M (variablePure M i ha) (f i) := by
  induction Γ using QCtx.inductionOn with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A q ih =>
    generalize hB : (Δ 0).1 = B
    obtain ⟨Δ, r, rfl⟩ := QCtx.exists_snoc_of_type Δ B hB
    let ft := fun j : Fin n => f j.succ
    let ht := fun j : Fin n => h j.succ
    let ct := contextTypeMap M (fun j => (Γ j).1) (fun j => (Δ j).1)
      (fun j => (Γ j).2) (fun j => (Δ j).2) ft ht
    cases i using Fin.cases with
    | zero =>
      have hΓ : Γ.Discardable := fun j => ha.2 j.succ (Fin.succ_ne_zero _)
      have hΔ : Δ.Discardable := fun j => hb.2 j.succ (Fin.succ_ne_zero _)
      cases q with
      | zero => exact False.elim ha.1
      | used q =>
        cases r with
        | zero => exact False.elim hb.1
        | used r =>
          change pureCompose M (retainTypeMap M ct (f 0) (h 0))
            (pureCompose M (pureRight M ⟨discard M hΔ, discard_pure M hΔ⟩ B)
              ⟨M.leftUnitor B, M.leftUnitor_pure B⟩) =
            pureCompose M (pureCompose M (pureRight M ⟨discard M hΓ, discard_pure M hΓ⟩ A)
              ⟨M.leftUnitor A, M.leftUnitor_pure A⟩) (f 0)
          rw [retainTypeMap_used]
          exact pureTensor_newest M ct (f 0) _ _
    | succ i =>
      have hΓ : Γ.VarAllowed i :=
        ⟨ha.1, fun j hj => ha.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      have hΔ : Δ.VarAllowed i :=
        ⟨hb.1, fun j hj => hb.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      have hi := ih Δ ft ht i hΓ hΔ
      cases q with
      | zero =>
        have hr : r = .zero := (h 0).mp rfl
        subst r
        change pureCompose M (retainTypeMap M ct (f 0) (h 0)) (variablePure M i hΔ) =
          pureCompose M (variablePure M i hΓ) (f i.succ)
        rw [retainTypeMap_zero]
        exact hi
      | used q =>
        cases r with
        | zero => exact False.elim (Usage.noConfusion ((h 0).mpr rfl))
        | used r =>
          have hA : Quantity.affine ≤ quantity A :=
            ((Usage.zero_le_effective_iff _ _).mp (ha.2 0 (Ne.symm (Fin.succ_ne_zero i)))).trans inf_le_left
          have hB : Quantity.affine ≤ quantity B :=
            ((Usage.zero_le_effective_iff _ _).mp (hb.2 0 (Ne.symm (Fin.succ_ne_zero i)))).trans inf_le_left
          change pureCompose M (retainTypeMap M ct (f 0) (h 0)) (dropRight M (variablePure M i hΔ) B hB) =
            pureCompose M (dropRight M (variablePure M i hΓ) A hA) (f i.succ)
          rw [retainTypeMap_used]
          exact (pureTensor_dropRight M ct (f 0) (variablePure M i hΔ) hA hB).trans
            ((congrArg (fun g => dropRight M g A hA) hi).trans
              (dropRight_compose M (variablePure M i hΓ) (f i.succ) hA).symm)

end Silmaril.Isotope.Refinement.Models.Denotation

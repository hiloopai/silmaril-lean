module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Packing
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Syntactic roundtrip for a packed exit interface -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} {Φ : Type v}

private theorem unpackExits_substVars (L : LCtx τ) (σ : Nat → Tm Φ)
    (h₀ : σ 0 = .var 0) :
    (unpackExits L).substVars σ = unpackExits L := by
  induction L generalizing σ with
  | nil => simp only [unpackExits, substVars, Tm.subst, Tm.liftSubst, h₀]
  | cons _ L ih =>
      simp only [unpackExits, substVars, Tm.subst, h₀, substVars_renameLabels,
        ih (Tm.liftSubst σ) (show Tm.liftSubst σ 0 = .var 0 from rfl), Tm.liftSubst]

private theorem unpackExits_cons_subst (B : τ) (L : LCtx τ) (a : Tm Φ) :
    (unpackExits (B :: L)).substVars (Tm.singleSubst a) =
      .case a (.br 0 (.var 0)) ((unpackExits L).renameLabels Nat.succ) := by
  change Region.case a (.br 0 (.var 0))
    (((unpackExits L).renameLabels Nat.succ).substVars (Tm.liftSubst (Tm.singleSubst a))) = _
  rw [substVars_renameLabels, unpackExits_substVars L (Tm.liftSubst (Tm.singleSubst a)) rfl]

variable [TypeFormers τ] [HasTy Φ τ]

private theorem equiv_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ} {ρ : Nat → Nat}
    (h : SubstitutionEquiv Γ r s L) (hρ : Ren L K ρ) :
    SubstitutionEquiv Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  exact h.lsubst (fun _ _ hi => .br (hρ hi) (.var rfl))

theorem unpackExits_packedArg {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {A : τ} {a : Tm Φ}
    (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
    SubstitutionEquiv Γ ((unpackExits L).substVars (Tm.singleSubst (packedExitArg ℓ a))) (.br ℓ a) L := by
  induction L generalizing Γ ℓ with
  | nil => simp [At] at hℓ
  | cons B L ih =>
      have hl : Region.HasType (B :: Γ) (.br 0 (.var 0) : Region Φ) (B :: L) := .br rfl (.var rfl)
      have hw := Silmaril.Isotope.SSA.Ren.wk L B
      have hr := (unpackExits_hasType (Φ := Φ) Γ L).renameLabels hw
      rw [unpackExits_cons_subst]
      cases ℓ with
      | zero =>
          cases Option.some.inj hℓ
          exact .trans (.base (.caseInl ha.hasType hl hr)) (.letValue ha hl)
      | succ ℓ =>
          have hv : Tm.BranchValue Γ (packedExitArg ℓ a) (packedExitType L) := packedExitArg_value hℓ ha
          refine .trans (.base (.caseInr hv.hasType hl hr)) (.trans (.letValue hv hr) ?_)
          rw [substVars_renameLabels]
          exact equiv_renameLabels (ih hℓ ha) hw

theorem packExits_valueFamily (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily Γ L [packedExitType L] (fun ℓ => .br 0 (packedExitArg ℓ (.var 0 : Tm Φ))) := by
  intro ℓ A hℓ
  exact .br rfl (packedExitArg_value hℓ (.var rfl))

private theorem unpackExits_valueBranches (Γ : VCtx τ) (L : LCtx τ) :
    ValueBranches (packedExitType L :: Γ) (unpackExits L : Region Φ) L := by
  induction L generalizing Γ with
  | nil =>
      exact .cfg (fun _ => Silmaril.empty) (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl))
  | cons A L ih =>
      exact .case (.var rfl) (.br rfl (.var rfl))
        (valueBranches_renameLabels (ih (packedExitType (A :: L) :: Γ)) (Silmaril.Isotope.SSA.Ren.wk L A))

theorem unpackExits_valueFamily (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily Γ [packedExitType L] L (fun _ => unpackExits L : Nat → Region Φ) := by
  intro ℓ A hℓ
  cases ℓ with
  | zero =>
      cases Option.some.inj hℓ
      exact unpackExits_valueBranches Γ L
  | succ ℓ => simp [At] at hℓ

theorem unpack_packExits_pointwise (Γ : VCtx τ) (L : LCtx τ) :
    ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ)
      (compLSubst (fun i => .br 0 (packedExitArg i (.var 0))) (fun _ => unpackExits L) ℓ)
      (labelId ℓ : Region Φ) L := by
  intro ℓ A hℓ
  let decode : Nat → Region Φ := fun _ => unpackExits L
  have hdecode : liftLSubstVars decode 0 = (unpackExits L : Region Φ) := by
    change (unpackExits L : Region Φ).renameVars (Silmaril.DeBruijn.lift Nat.succ) = unpackExits L
    rw [renameVars_eq_substVars]
    exact unpackExits_substVars L _ rfl
  change SubstitutionEquiv (A :: Γ)
    ((liftLSubstVars decode 0).substVars (Tm.singleSubst (packedExitArg ℓ (.var 0)))) (.br ℓ (.var 0)) L
  rw [hdecode]
  exact unpackExits_packedArg hℓ (.var rfl)

theorem unpack_packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) :
    SubstitutionEquiv Γ (r.packExits.lsubst (fun _ => unpackExits L)) r L := by
  change SubstitutionEquiv Γ
    ((r.lsubst (fun i => .br 0 (packedExitArg i (.var 0)))).lsubst (fun _ => unpackExits L)) r L
  rw [lsubst_comp]
  simpa only [lsubst_labelId] using hr.lsubst_substitutionEquiv (unpack_packExits_pointwise Γ L)

@[simp] private theorem packedExitArg_rename_lift (i : Nat) :
    (packedExitArg i (.var 0 : Tm Φ)).rename (Silmaril.DeBruijn.lift Nat.succ) =
      packedExitArg i (.var 0) := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg Tm.inr ih

theorem packFamily_liftVars :
    liftLSubstVars (Φ := Φ) (fun i => .br 0 (packedExitArg i (.var 0))) =
      fun i => .br 0 (packedExitArg i (.var 0)) := by
  funext i
  exact congrArg (Region.br 0) (packedExitArg_rename_lift i)

theorem pack_unpackExits_payload (Γ : VCtx τ) (L : LCtx τ) :
    SubstitutionEquiv (packedExitType L :: Γ) (unpackExits L : Region Φ).packExits
      (.br 0 (.var 0)) [packedExitType L] := by
  induction L generalizing Γ with
  | nil =>
      exact .initial_var (i := 0) rfl (unpackExits_hasType Γ []).packExits (.br rfl (.var rfl))
  | cons A L ih =>
      let P := packedExitType (A :: L)
      let Q := packedExitType L
      let tag : Nat → Region Φ := fun i => .br 0 (packedExitArg i (.var 0))
      let rightTag : Nat → Region Φ := fun _ => .br 0 (.inr (.var 0))
      have htags : LSubst.HasType (Q :: P :: Γ) [Q] [P] rightTag := by
        intro i B hi
        cases i with
        | zero =>
            cases Option.some.inj hi
            exact .br rfl (.inr (.var (i := 0) rfl))
        | succ i => simp [At] at hi
      have right := (ih (P :: Γ)).lsubst htags
      have rightBody : ((unpackExits L).renameLabels Nat.succ).lsubst tag =
          (unpackExits L).packExits.lsubst rightTag := by
        rw [lsubst_renameLabels]
        change (unpackExits L).lsubst (tag ∘ Nat.succ) = ((unpackExits L).lsubst tag).lsubst rightTag
        rw [lsubst_comp]
        rfl
      change SubstitutionEquiv (P :: Γ)
        (.case (.var 0) ((Region.br 0 (.var 0)).lsubst (liftLSubstVars tag))
          (((unpackExits L).renameLabels Nat.succ).lsubst (liftLSubstVars tag)))
        (.br 0 (.var 0)) [P]
      rw [show liftLSubstVars tag = tag from packFamily_liftVars, rightBody]
      have left : Region.HasType (A :: P :: Γ) (.br 0 (.inl (.var 0)) : Region Φ) [P] :=
        .br rfl (.inl (.var rfl))
      have hcase := SubstitutionEquiv.case
        (Tm.HasType.var (Φ := Φ) (Γ := P :: Γ) (i := 0) (A := P) rfl)
        (SubstitutionEquiv.base (.refl left)) right
      have hbody : Region.HasType (P :: P :: Γ) (.br 0 (.var 0) : Region Φ) [P] :=
        .br rfl (.var rfl)
      have eta := SubstitutionEquiv.caseValue (Γ := P :: Γ) (A := A) (B := Q)
        (Tm.BranchValue.var (Φ := Φ) (i := 0) (A := P) rfl) hbody
      exact hcase.trans eta

private theorem pack_unpackExits_pointwise (Γ : VCtx τ) (L : LCtx τ) :
    ∀ ⦃i A⦄, At [packedExitType L] i A → SubstitutionEquiv (A :: Γ)
      (compLSubst (fun _ => unpackExits L) (fun j => .br 0 (packedExitArg j (.var 0))) i)
      (labelId i : Region Φ) [packedExitType L] := by
  intro i A hi
  cases i with
  | zero =>
      cases Option.some.inj hi
      unfold compLSubst
      rw [packFamily_liftVars]
      exact pack_unpackExits_payload Γ L
  | succ i => simp [At] at hi

theorem pack_unpackExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r [packedExitType L]) :
    SubstitutionEquiv Γ (r.lsubst (fun _ => unpackExits L)).packExits r [packedExitType L] := by
  unfold packExits
  rw [lsubst_comp]
  simpa only [lsubst_labelId] using hr.lsubst_substitutionEquiv (pack_unpackExits_pointwise Γ L)

theorem nonempty_packedIso {Γ : VCtx τ} (X : ContinuationContext Φ Γ) :
    Nonempty (X ≅ (⟨[packedExitType X.labels]⟩ : ContinuationContext Φ Γ)) := by
  let Y : ContinuationContext Φ Γ := ⟨[packedExitType X.labels]⟩
  let pack : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels :=
    ⟨_, packExits_valueFamily Γ X.labels⟩
  let unpack : ContinuationFamily (Φ := Φ) Γ Y.labels X.labels :=
    ⟨_, unpackExits_valueFamily Γ X.labels⟩
  refine ⟨⟨pack.toHom, unpack.toHom, ?_, ?_⟩⟩
  · rw [← ContinuationFamily.compose_toHom, ← ContinuationFamily.identity_toHom]
    exact ContinuationFamily.toHom_eq_iff.mpr (unpack_packExits_pointwise Γ X.labels)
  · rw [← ContinuationFamily.compose_toHom, ← ContinuationFamily.identity_toHom]
    exact ContinuationFamily.toHom_eq_iff.mpr (pack_unpackExits_pointwise Γ X.labels)

theorem packExits_equiv_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    SubstitutionEquiv Γ r.packExits s.packExits [packedExitType L] ↔ SubstitutionEquiv Γ r s L := by
  constructor
  · intro h
    have hdecode : LSubst.HasType Γ [packedExitType L] L (fun _ => unpackExits L : Nat → Region Φ) :=
      fun _ _ hi => ((unpackExits_valueFamily Γ L) hi).hasType
    exact (unpack_packExits hr).symm.trans ((h.lsubst hdecode).trans (unpack_packExits hs))
  · intro h
    exact h.lsubst (fun _ _ hi => ((packExits_valueFamily (Φ := Φ) Γ L) hi).hasType)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

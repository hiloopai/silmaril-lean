module

public import Silmaril.Raw.SSA.Isotope.Semantics.Relation
public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Monadic

/-! # Direct relational semantics

Evaluation composes primitive relations existentially, without selecting a
particular outcome. Its successful outcomes agree with the powerset model.
-/

@[expose] public section

universe u v w q

open Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

variable {τ : Type u} [HasProduct τ] [HasUnit τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  (R : RelationModel D Φ)

/-- Direct relational evaluation of exact typing data. -/
def denoteRelation : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
    FreeEnv D Γ → BoundEnv D β → D A → Prop
  | _, _, _, _, _, .fv h, γ, _, x => x = γ _ _ h
  | _, _, _, _, _, .bv, _, ρ, x => x = ρ _
  | _, _, _, _, _, .op (f := f) ha, γ, ρ, x =>
      ∃ a, denoteRelation ha γ ρ a ∧ R.eval f a x
  | _, _, _, _, _, .let₁ ha hb, γ, ρ, x =>
      ∃ a, denoteRelation ha γ ρ a ∧ denoteRelation hb γ (ρ.snoc a) x
  | _, _, _, _, _, .unit, _, _, x => x = (UnitModel.unitEquiv (D := D)).symm PUnit.unit
  | _, _, _, _, _, .pair ha hb, γ, ρ, x =>
      ∃ a, denoteRelation ha γ ρ a ∧ ∃ b, denoteRelation hb γ ρ b ∧
        x = (ProductModel.productEquiv (D := D) _ _).symm (a, b)
  | _, _, _, _, _, .let₂ ha hc, γ, ρ, x =>
      ∃ ab, denoteRelation ha γ ρ ab ∧
        let p := ProductModel.productEquiv (D := D) _ _ ab
        denoteRelation hc γ ((ρ.snoc p.1).snoc p.2) x

/-- Pointwise equality of direct relational evaluation and powerset membership. -/
theorem denoteRelation_iff_mem {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (x : D A) :
    denoteRelation D R d γ ρ x ↔ x ∈ (denote D R.toSetModel d γ ρ).run := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih =>
      simp only [denoteRelation, denote, Relation.setM_bind_iff, ih]
      rfl
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp only [denoteRelation, denote, Relation.setM_bind_iff, Relation.setM_pure_iff,
        iha, ihb]

/-- The set of direct relational outcomes is exactly the monadic interpretation. -/
theorem denoteRelation_eq_run {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    {x | denoteRelation D R d γ ρ x} = (denote D R.toSetModel d γ ρ).run :=
  Set.ext (denoteRelation_iff_mem D R d γ ρ)

/-- Direct relational evaluation of a closed exactly typed term. -/
def denoteRelationClosed {t : Tm Empty Φ 0} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) .nil t A) : D A → Prop :=
  denoteRelation D R d (fun x => nomatch x) (fun i => Fin.elim0 i)

end Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

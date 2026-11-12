module

public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Monadic

/-! # Function semantics

Exact sequential terms evaluate directly to values. Primitive implementations
are ordinary total functions, expressed using the shared instruction interface
at `Id`. The evaluator recurses independently of the monadic interpreter.
-/

@[expose] public section

universe u v w q

open Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

variable {τ : Type u} [HasProduct τ] [HasUnit τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  (M : InstructionModel D Φ Id)

/-- Interpret exact derivations as ordinary functions on environments. -/
def denoteFunction : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
    FreeEnv D Γ → BoundEnv D β → D A
  | _, _, _, _, _, .fv h, γ, _ => γ _ _ h
  | _, _, _, _, _, .bv, _, ρ => ρ _
  | _, _, _, _, _, .op ha, γ, ρ => M.eval _ (denoteFunction ha γ ρ)
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denoteFunction hb γ (ρ.snoc (denoteFunction ha γ ρ))
  | _, _, _, _, _, .unit, _, _ => (UnitModel.unitEquiv (D := D)).symm PUnit.unit
  | _, _, _, _, _, .pair ha hb, γ, ρ =>
      (ProductModel.productEquiv (D := D) _ _).symm
        (denoteFunction ha γ ρ, denoteFunction hb γ ρ)
  | _, _, _, _, _, .let₂ ha hc, γ, ρ =>
      let p := ProductModel.productEquiv (D := D) _ _ (denoteFunction ha γ ρ)
      denoteFunction hc γ ((ρ.snoc p.1).snoc p.2)

/-- The independent function interpretation agrees with the identity monad. -/
theorem denoteFunction_eq_denote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    d.denoteFunction D M γ ρ = d.denote D M γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih =>
      simp only [denoteFunction, denote, ih]
      rfl
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp only [denoteFunction, denote, iha, ihb]
      rfl

/-- A closed exact term evaluates to a value without an environment. -/
def denoteFunctionClosed {t : Tm Empty Φ 0} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) .nil t A) : D A :=
  denoteFunction D M d (fun x => nomatch x) (fun i => Fin.elim0 i)

theorem denoteFunctionClosed_eq_denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) .nil t A) :
    d.denoteFunctionClosed D M = d.denoteClosed D M :=
  denoteFunction_eq_denote D M d _ _

end Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

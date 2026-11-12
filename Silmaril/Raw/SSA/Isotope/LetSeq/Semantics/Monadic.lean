module

public import Silmaril.Raw.SSA.Isotope.Semantics.Model
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Derivation

/-! # Monadic semantics

Terms are interpreted in any monad, with left-to-right evaluation.
Exact typing and effect annotations remain separate. -/

@[expose] public section

universe u v w q

open Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

variable {τ : Type u} [HasProduct τ] [HasUnit τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m]
  (M : InstructionModel D Φ m)

/-- Evaluate coercion-free typing data, preserving left-to-right evaluation. -/
def denote : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
    FreeEnv D Γ → BoundEnv D β → m (D A)
  | _, _, _, _, _, .fv h, γ, _ => pure (γ _ _ h)
  | _, _, _, _, _, .bv, _, ρ => pure (ρ _)
  | _, _, _, _, _, .op ha, γ, ρ => denote ha γ ρ >>= M.eval _
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ (ρ.snoc a)
  | _, _, _, _, _, .unit, _, _ => pure ((UnitModel.unitEquiv (D := D)).symm PUnit.unit)
  | _, _, _, _, _, .pair ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a =>
      denote hb γ ρ >>= fun b =>
      pure ((ProductModel.productEquiv (D := D) _ _).symm (a, b))
  | _, _, _, _, _, .let₂ ha hc, γ, ρ =>
      denote ha γ ρ >>= fun ab =>
      let p := ProductModel.productEquiv (D := D) _ _ ab
      denote hc γ ((ρ.snoc p.1).snoc p.2)

/-- A closed typed program denotes a computation. -/
def denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) .nil t A) : m (D A) :=
  denote D M d (fun x => nomatch x) (fun i => Fin.elim0 i)

end Silmaril.Isotope.LetSeq.LocallyNameless.Derivation

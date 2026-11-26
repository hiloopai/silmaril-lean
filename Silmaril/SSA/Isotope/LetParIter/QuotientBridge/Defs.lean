module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs

/-! Relations used to compare raw judgments with the exact upper congruence. -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.QuotientBridge

open Parallel (Derivation)

universe u v w q r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ}

/-- A generated upper equation at some exact derivations of the raw endpoints. -/
def Witness (pe : ε) (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (a b : LetParIter.Tm ν Φ n) (A : τ) : Prop :=
  ∃ (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A),
    LetParIter.Equiv pe Γ da db

/-- All derivations of this judgment determine one class of the exact upper quotient. -/
abbrev Aligned (pe : ε) (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (a : LetParIter.Tm ν Φ n) (A : τ) : Prop :=
  ∀ (da da' : Derivation Φ Γ β a A), LetParIter.Equiv pe Γ da da'

/-- Existential upper witnesses for embedded native LetIter terms. -/
abbrev NativeWitness (pe : ε) (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (a b : LetIter.LocallyNameless.Tm ν Φ n) (A : τ) :=
  Witness pe Γ β (LetParIter.embed a) (LetParIter.embed b) A

/-- Existential upper witnesses for widened LetParCase terms. -/
abbrev CaseWitness (pe : ε) (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (a b : LetParCase.Tm ν Φ n) (A : τ) :=
  Witness pe Γ β (LetParIter.ofLetParCase a) (LetParIter.ofLetParCase b) A

end Silmaril.Isotope.LetParIter.QuotientBridge

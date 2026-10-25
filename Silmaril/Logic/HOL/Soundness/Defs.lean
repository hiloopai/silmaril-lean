module

public import Silmaril.Logic.HOL.Semantics

@[expose] public section

/-! # Semantic consequence for signature-parametric HOL

The underlying pointed-carrier model erases subtype predicates. These definitions
refer to that model, without asserting predicate-subset semantics.
-/

namespace Silmaril.Logic.HOL

universe u

def HypsTrue {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    (hypotheses : List (Tm Sig depth)) : Prop :=
  ∀ p, p ∈ hypotheses → Eval Γ freeEnv boundEnv p .boolTy true

def Entails {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} (hypotheses : List (Tm Sig depth))
    (conclusion : Tm Sig depth) : Prop :=
  ∀ (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ),
    HypsTrue freeEnv boundEnv hypotheses → Eval Γ freeEnv boundEnv conclusion .boolTy true

end Silmaril.Logic.HOL

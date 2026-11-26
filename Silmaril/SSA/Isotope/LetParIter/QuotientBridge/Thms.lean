module

public import Silmaril.SSA.Isotope.LetParIter.QuotientBridge.Defs
public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs
public import Silmaril.SSA.Isotope.Bridge.Defs
import Silmaril.Proofs.SSA.Isotope.LetParIter.QuotientBridge

/-! Conditional compatibility of the raw square with exact upper equations. -/

public section

namespace Silmaril.Isotope.LetParIter.QuotientBridge

open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics

universe u v w q r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ}

variable {n : Nat} {β : BoundCtx τ n} {a b c : LetParIter.Tm ν Φ n} {A : τ}

/-- Compose witnessed equations using alignment on the middle judgment. -/
theorem witness_trans (atMiddle : Aligned pe Γ β b A)
    (hab : Witness pe Γ β a b A) (hbc : Witness pe Γ β b c A) :
    Witness pe Γ β a c A :=
  Proofs.witness_trans atMiddle hab hbc

/-- Alignment promotes a witnessed equation to the specified endpoint derivations. -/
theorem witness_at (atLeft : Aligned pe Γ β a A) (atRight : Aligned pe Γ β b A)
    (hab : Witness pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    LetParIter.Equiv pe Γ da db :=
  Proofs.witness_at atLeft atRight hab da db

section Native

open LetIter.LocallyNameless (HasType Pure CoreAxiom)

/-- The native raw closure lifts from compatibility of core axiom instances,
compatibility of uniformity at a lifted square, and alignment on native fibers. -/
theorem native_witness
    (align : ∀ {n : Nat} {β : BoundCtx τ n} {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ},
      Aligned pe Γ β (LetParIter.embed t) A)
    (core : ∀ {n : Nat} {β : BoundCtx τ n} {a b : LetIter.LocallyNameless.Tm ν Φ n} {A : τ},
      CoreAxiom pe a b → HasType Φ Γ β a A → HasType Φ Γ β b A →
        NativeWitness pe Γ β a b A)
    (uniformity : ∀ {n : Nat} {β : BoundCtx τ n} {a : LetIter.LocallyNameless.Tm ν Φ n}
      {h b b' : LetIter.LocallyNameless.Tm ν Φ (n + 1)} {A A' B : τ},
      HasType Φ Γ β a A → HasType Φ Γ (.snoc β A) h A' → Pure pe h →
      HasType Φ Γ (.snoc β A) b (coprod B A) →
      HasType Φ Γ (.snoc β A') b' (coprod B A') →
      NativeWitness pe Γ (.snoc β A)
        (.case b (.inl (.bv 0)) (.inr h.underBinder)) (b'.underBinder.instantiate h) (coprod B A') →
      NativeWitness pe Γ β (.iter a b) (.iter (.let₁ a h) b') B)
    {a b : LetIter.LocallyNameless.Tm ν Φ n}
    (h : LetIter.LocallyNameless.Equiv pe Γ β a b A) :
    NativeWitness pe Γ β a b A :=
  Proofs.native_witness align core uniformity h

end Native

section LowerCase

/-- The case-tier raw closure lifts from compatibility of its three families
of generators and alignment on widened case fibers. -/
theorem case_witness
    (align : ∀ {n : Nat} {β : BoundCtx τ n} {t : LetParCase.Tm ν Φ n} {A : τ},
      Aligned pe Γ β (LetParIter.ofLetParCase t) A)
    (seqRule : ∀ {n : Nat} {β : BoundCtx τ n} {a b : LetParCase.Tm ν Φ n} {A : τ},
      Parallel.SeqRule pe a b → Parallel.HasType Φ Γ β a A → Parallel.HasType Φ Γ β b A →
        CaseWitness pe Γ β a b A)
    (parRule : ∀ {n : Nat} {β : BoundCtx τ n} {a b : LetParCase.Tm ν Φ n} {A : τ},
      Parallel.ParRule pe a b → Parallel.HasType Φ Γ β a A → Parallel.HasType Φ Γ β b A →
        CaseWitness pe Γ β a b A)
    (caseRule : ∀ {n : Nat} {β : BoundCtx τ n} {a b : LetParCase.Tm ν Φ n} {A : τ},
      Parallel.CaseRule pe a b → Parallel.HasType Φ Γ β a A → Parallel.HasType Φ Γ β b A →
        CaseWitness pe Γ β a b A)
    {a b : LetParCase.Tm ν Φ n} (h : LetParCase.Equiv pe Γ β a b A) :
    CaseWitness pe Γ β a b A :=
  Proofs.case_witness align seqRule parRule caseRule h

end LowerCase

section Model

variable [TypeModel.{u, v} τ] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] (P : Elgot.ParallelPairing m)

/-- An existential upper equation yields equality at arbitrary exact endpoints
whenever this model's denotation is coherent on the typing fibers. -/
theorem denote_eq_of_witness
    (γ : CtxDen Γ) (ρ : BoundDen β)
    (coherent : ∀ {t : LetParIter.Tm ν Φ n} (d e : Derivation Φ Γ β t A),
      LetParIter.denote (ε := ε) P d γ ρ = LetParIter.denote (ε := ε) P e γ ρ)
    (h : Witness (⊥ : ε) Γ β a b A)
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    LetParIter.denote (ε := ε) P da γ ρ = LetParIter.denote (ε := ε) P db γ ρ :=
  Proofs.denote_eq_of_witness P γ ρ coherent h da db

end Model

end Silmaril.Isotope.LetParIter.QuotientBridge

module

public import Silmaril.SSA.Isotope.LetParIter.QuotientBridge.Defs
public import Silmaril.SSA.Isotope.LetParIter.Thms
public import Silmaril.SSA.Isotope.Bridge.Defs

public section

namespace Silmaril.Isotope.LetParIter.QuotientBridge.Proofs

open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics

universe u v w q r
variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ}

variable {n : Nat} {β : BoundCtx τ n} {a b c : LetParIter.Tm ν Φ n} {A : τ}

theorem witness_trans (atMiddle : Aligned pe Γ β b A)
    (hab : Witness pe Γ β a b A) (hbc : Witness pe Γ β b c A) :
    Witness pe Γ β a c A := by
  obtain ⟨da, db, hab⟩ := hab
  obtain ⟨db', dc, hbc⟩ := hbc
  exact ⟨da, dc, .trans hab (.trans (atMiddle db db') hbc)⟩

theorem witness_at (atLeft : Aligned pe Γ β a A) (atRight : Aligned pe Γ β b A)
    (hab : Witness pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    LetParIter.Equiv pe Γ da db := by
  obtain ⟨da', db', hab⟩ := hab
  exact .trans (atLeft da da') (.trans hab (atRight db' db))

section Native

open LetIter.LocallyNameless (HasType Pure CoreAxiom)

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
    NativeWitness pe Γ β a b A := by
  induction h with
  | refl h =>
      obtain ⟨d⟩ := LetIter.LocallyNameless.Derivation.ofHasType h
      exact ⟨_, _, .refl (LetParIter.derivation d)⟩
  | symm _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .symm h⟩
  | trans _ _ h k => exact witness_trans align h k
  | op _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .op h⟩
  | let₁ _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .let₁ h k⟩
  | unit => exact ⟨.unit, .unit, .refl .unit⟩
  | pair _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .pair h k⟩
  | let₂ _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .let₂ h k⟩
  | inl _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .inl h⟩
  | inr _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .inr h⟩
  | case _ _ _ ihe ihl ihr =>
      obtain ⟨_, _, he⟩ := ihe
      obtain ⟨_, _, hl⟩ := ihl
      obtain ⟨_, _, hr⟩ := ihr
      exact ⟨_, _, .case he hl hr⟩
  | abort _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .abort h⟩
  | iter _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .iter h k⟩
  | ax h ha hb => exact core h ha hb
  | uniformity ha hh hp hb hb' _ ih => exact uniformity ha hh hp hb hb' ih

end Native

section LowerCase

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
    CaseWitness pe Γ β a b A := by
  induction h with
  | refl h =>
      obtain ⟨d⟩ := h
      exact ⟨_, _, .refl (LetParIter.ofLetParCaseDerivation d)⟩
  | symm _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .symm h⟩
  | trans _ _ h k => exact witness_trans align h k
  | op _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .op h⟩
  | let₁ _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .let₁ h k⟩
  | pair _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .pair h k⟩
  | let₂ _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .let₂ h k⟩
  | inl _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .inl h⟩
  | inr _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .inr h⟩
  | case _ _ _ ihe ihl ihr =>
      obtain ⟨_, _, he⟩ := ihe
      obtain ⟨_, _, hl⟩ := ihl
      obtain ⟨_, _, hr⟩ := ihr
      exact ⟨_, _, .case he hl hr⟩
  | abort _ ih =>
      obtain ⟨_, _, h⟩ := ih
      exact ⟨_, _, .abort h⟩
  | iter => contradiction
  | par _ _ ih₁ ih₂ =>
      obtain ⟨_, _, h⟩ := ih₁
      obtain ⟨_, _, k⟩ := ih₂
      exact ⟨_, _, .par h k⟩
  | seqRule rule ha hb => exact seqRule rule ha hb
  | parRule rule ha hb => exact parRule rule ha hb
  | extraRule rule ha hb => exact caseRule rule ha hb

end LowerCase

section Model

variable [TypeModel.{u, v} τ] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] (P : Elgot.ParallelPairing m)

theorem denote_eq_of_witness
    (γ : CtxDen Γ) (ρ : BoundDen β)
    (coherent : ∀ {t : LetParIter.Tm ν Φ n} (d e : Derivation Φ Γ β t A),
      LetParIter.denote (ε := ε) P d γ ρ = LetParIter.denote (ε := ε) P e γ ρ)
    (h : Witness (⊥ : ε) Γ β a b A)
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    LetParIter.denote (ε := ε) P da γ ρ = LetParIter.denote (ε := ε) P db γ ρ := by
  obtain ⟨da', db', eq⟩ := h
  exact (coherent da da').trans ((LetParIter.sound P eq γ ρ).trans (coherent db' db))

end Model

end Silmaril.Isotope.LetParIter.QuotientBridge.Proofs

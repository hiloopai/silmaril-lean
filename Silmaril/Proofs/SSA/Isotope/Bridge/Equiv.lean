module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Typing

/-!
# Bridge between legacy and thesis let-iter: the equational theories (proofs)

The two locally nameless axiom sets agree constructor for constructor (`StructuralAxiom`:
9 schemes, `SequencingAxiom`: 6, `IterationAxiom`: 4, with the same purity side condition on
`letBeta`), and the two typed closures `Equiv` / `Eqv` have the same congruence rules, the
same `ax` rule with both endpoint typings, and the same `uniformity` rule. Hence, under the
three compatibility hypotheses, the translation preserves and reflects typed equivalence.
Restated in `Silmaril.SSA.Isotope.Bridge.Thms`.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Proofs.SSA.Isotope.Bridge

open Silmaril.Isotope.Bridge

local notation "LTm" => Silmaril.Isotope.LetIter.LocallyNameless.Tm
local notation "TTm" => Silmaril.Thesis.LambdaIter.LocallyNameless.Tm

variable {τ : Type u} [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
variable {ε : Type r} [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]

/-! ## Axiom schemes -/

omit [DecidableEq ν] in
theorem coreAxiom_toThesis (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {a b : LTm ν Φ n}
    (h : Silmaril.Isotope.LetIter.LocallyNameless.CoreAxiom pe a b) :
    Silmaril.Thesis.LambdaIter.LocallyNameless.CoreAxiom pe (toThesis a) (toThesis b) := by
  cases h with
  | structural h =>
      refine .structural ?_
      cases h with
      | letBeta hp =>
          simp only [toThesis, toThesis_instantiate]
          exact .letBeta (pure_toThesis hE pe hp)
      | letEta a => simp only [toThesis]; exact .letEta _
      | unitEta a => simp only [toThesis]; exact .unitEta _
      | pairBeta a b c => simp only [toThesis, toThesis_lift]; exact .pairBeta _ _ _
      | pairEta a => simp only [toThesis]; exact .pairEta _
      | caseBetaL e l r => simp only [toThesis]; exact .caseBetaL _ _ _
      | caseBetaR e l r => simp only [toThesis]; exact .caseBetaR _ _ _
      | caseEta e => simp only [toThesis]; exact .caseEta _
      | emptyInitial a b c => simp only [toThesis]; exact .emptyInitial _ _ _
  | sequencing h =>
      refine .sequencing ?_
      cases h with
      | bindOp a c => simp only [toThesis, toThesis_underBinder]; exact .bindOp _ _
      | bindLet a b c => simp only [toThesis, toThesis_underBinder]; exact .bindLet _ _ _
      | bindLetPair e c d =>
          simp only [toThesis, toThesis_underBinder]; exact .bindLetPair _ _ _
      | bindLetCase e l r d =>
          simp only [toThesis, toThesis_underBinder]; exact .bindLetCase _ _ _ _
      | bindPair a c => simp only [toThesis, toThesis_underTwoBinders]; exact .bindPair _ _
      | bindCase e l r => simp only [toThesis, toThesis_underBinder]; exact .bindCase _ _ _
  | iteration h =>
      refine .iteration ?_
      cases h with
      | fixpoint a b => simp only [toThesis, toThesis_underBinder]; exact .fixpoint _ _
      | naturality a b c => simp only [toThesis, toThesis_underBinder]; exact .naturality _ _ _
      | codiagonal a b => simp only [toThesis, toThesis_underBinder]; exact .codiagonal _ _
      | iterBind a b => simp only [toThesis, toThesis_underBinder]; exact .iterBind _ _

omit [DecidableEq ν] in
theorem coreAxiom_ofThesis (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {a b : TTm ν Φ n}
    (h : Silmaril.Thesis.LambdaIter.LocallyNameless.CoreAxiom pe a b) :
    Silmaril.Isotope.LetIter.LocallyNameless.CoreAxiom pe (ofThesis a) (ofThesis b) := by
  cases h with
  | structural h =>
      refine .structural ?_
      cases h with
      | letBeta hp =>
          simp only [ofThesis, ofThesis_instantiate]
          exact .letBeta (pure_ofThesis hE pe hp)
      | letEta a => simp only [ofThesis]; exact .letEta _
      | unitEta a => simp only [ofThesis]; exact .unitEta _
      | pairBeta a b c => simp only [ofThesis, ofThesis_lift]; exact .pairBeta _ _ _
      | pairEta a => simp only [ofThesis]; exact .pairEta _
      | caseBetaL e l r => simp only [ofThesis]; exact .caseBetaL _ _ _
      | caseBetaR e l r => simp only [ofThesis]; exact .caseBetaR _ _ _
      | caseEta e => simp only [ofThesis]; exact .caseEta _
      | emptyInitial a b c => simp only [ofThesis]; exact .emptyInitial _ _ _
  | sequencing h =>
      refine .sequencing ?_
      cases h with
      | bindOp a c => simp only [ofThesis, ofThesis_underBinder]; exact .bindOp _ _
      | bindLet a b c => simp only [ofThesis, ofThesis_underBinder]; exact .bindLet _ _ _
      | bindLetPair e c d =>
          simp only [ofThesis, ofThesis_underBinder]; exact .bindLetPair _ _ _
      | bindLetCase e l r d =>
          simp only [ofThesis, ofThesis_underBinder]; exact .bindLetCase _ _ _ _
      | bindPair a c => simp only [ofThesis, ofThesis_underTwoBinders]; exact .bindPair _ _
      | bindCase e l r => simp only [ofThesis, ofThesis_underBinder]; exact .bindCase _ _ _
  | iteration h =>
      refine .iteration ?_
      cases h with
      | fixpoint a b => simp only [ofThesis, ofThesis_underBinder]; exact .fixpoint _ _
      | naturality a b c => simp only [ofThesis, ofThesis_underBinder]; exact .naturality _ _ _
      | codiagonal a b => simp only [ofThesis, ofThesis_underBinder]; exact .codiagonal _ _
      | iterBind a b => simp only [ofThesis, ofThesis_underBinder]; exact .iterBind _ _

omit [DecidableEq ν] in
theorem coreAxiom_iff (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {a b : LTm ν Φ n} :
    Silmaril.Isotope.LetIter.LocallyNameless.CoreAxiom pe a b ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.CoreAxiom pe (toThesis a) (toThesis b) :=
  ⟨coreAxiom_toThesis hE pe, fun h => by
    simpa only [ofThesis_toThesis] using coreAxiom_ofThesis hE pe h⟩

/-! ## Typed equivalence -/

theorem equiv_toThesis (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm ν Φ n} {A : τ}
    (h : Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe Γ β a b A) :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe (Ctx.toThesis Γ) (BoundCtx.toThesis β)
      (toThesis a) (toThesis b) A := by
  induction h with
  | refl h =>
      obtain ⟨d⟩ := hasType_toThesis hT hI h
      exact .refl d
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik
  | op _ ih =>
      rw [hI.src] at ih
      rw [hI.trg]
      exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => rw [hT.unit]; exact .unit
  | pair _ _ iha ihb => rw [hT.product]; exact .pair iha ihb
  | let₂ _ _ ihe ihc => rw [hT.product] at ihe; exact .let₂ ihe ihc
  | inl _ ih => rw [hT.coprod]; exact .inl ih
  | inr _ ih => rw [hT.coprod]; exact .inr ih
  | case _ _ _ ihe ihl ihr => rw [hT.coprod] at ihe; exact .case ihe ihl ihr
  | abort _ ih => rw [hT.empty] at ih; exact .abort ih
  | iter _ _ iha ihb => rw [hT.coprod] at ihb; exact .iter iha ihb
  | ax hax ha hb =>
      obtain ⟨da⟩ := hasType_toThesis hT hI ha
      obtain ⟨db⟩ := hasType_toThesis hT hI hb
      exact .ax (coreAxiom_toThesis hE pe hax) da db
  | uniformity ha hh hp hb hb' _ ih =>
      obtain ⟨da⟩ := hasType_toThesis hT hI ha
      obtain ⟨dh⟩ := hasType_toThesis hT hI hh
      obtain ⟨db⟩ := hasType_toThesis hT hI hb
      obtain ⟨db'⟩ := hasType_toThesis hT hI hb'
      rw [hT.coprod] at db db' ih
      simp only [toThesis, toThesis_underBinder, toThesis_instantiate] at ih ⊢
      exact .uniformity da dh (pure_toThesis hE pe hp) db db' ih

theorem eqv_ofThesis (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ} {n : Nat}
    {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n} {a b : TTm ν Φ n} {A : τ}
    (h : Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe Γ β a b A) :
    Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe (Ctx.ofThesis Γ) (BoundCtx.ofThesis β)
      (ofThesis a) (ofThesis b) A := by
  induction h with
  | refl h => exact .refl (hasType_ofThesis hT hI h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik
  | op _ ih =>
      rw [← hI.src] at ih
      rw [← hI.trg]
      exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => rw [← hT.unit]; exact .unit
  | pair _ _ iha ihb => rw [← hT.product]; exact .pair iha ihb
  | let₂ _ _ ihe ihc => rw [← hT.product] at ihe; exact .let₂ ihe ihc
  | inl _ ih => rw [← hT.coprod]; exact .inl ih
  | inr _ ih => rw [← hT.coprod]; exact .inr ih
  | case _ _ _ ihe ihl ihr => rw [← hT.coprod] at ihe; exact .case ihe ihl ihr
  | abort _ ih => rw [← hT.empty] at ih; exact .abort ih
  | iter _ _ iha ihb => rw [← hT.coprod] at ihb; exact .iter iha ihb
  | ax hax ha hb =>
      exact .ax (coreAxiom_ofThesis hE pe hax) (hasType_ofThesis hT hI ha)
        (hasType_ofThesis hT hI hb)
  | uniformity ha hh hp hb hb' _ ih =>
      have la := hasType_ofThesis hT hI ha
      have lh := hasType_ofThesis hT hI hh
      have lb := hasType_ofThesis hT hI hb
      have lb' := hasType_ofThesis hT hI hb'
      rw [← hT.coprod] at lb lb' ih
      simp only [ofThesis, ofThesis_underBinder, ofThesis_instantiate] at ih ⊢
      exact .uniformity la lh (pure_ofThesis hE pe hp) lb lb' ih

/-- **Equivalence bridge.** Legacy typed equivalence holds exactly when thesis typed
equivalence holds between the translated terms in the translated contexts. -/
theorem equiv_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm ν Φ n} {A : τ} :
    Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe Γ β a b A ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe (Ctx.toThesis Γ) (BoundCtx.toThesis β)
        (toThesis a) (toThesis b) A :=
  ⟨equiv_toThesis hT hI hE pe, fun h => by
    simpa only [Ctx.ofThesis_toThesis, BoundCtx.ofThesis_toThesis, ofThesis_toThesis] using
      eqv_ofThesis hT hI hE pe h⟩

/-- The equivalence bridge read from the thesis side. -/
theorem eqv_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ} {n : Nat}
    {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n} {a b : TTm ν Φ n} {A : τ} :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe Γ β a b A ↔
      Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe (Ctx.ofThesis Γ) (BoundCtx.ofThesis β)
        (ofThesis a) (ofThesis b) A :=
  ⟨eqv_ofThesis hT hI hE pe, fun h => by
    simpa only [Ctx.toThesis_ofThesis, BoundCtx.toThesis_ofThesis, toThesis_ofThesis] using
      equiv_toThesis hT hI hE pe h⟩

end Silmaril.Proofs.SSA.Isotope.Bridge

module

public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter
public import Silmaril.Raw.SSA.Isotope.Theory.Refinement

/-!
# Theory preservation by the let calculus inclusions

The fragment theories are independent presentations. Their constructor inclusions
preserve the raw schemes, exact equations, and directed refinements whenever the
primitive rewrite generators are preserved. No converse conservativity assertion
is needed or assumed.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.SeqCase

open LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type r} [HasEff Φ ε]
  {pureEff : ε} {n : Nat} {a b : Tm ν Φ n}

/-- Constructor inclusion preserves every structural axiom scheme. -/
theorem embed_structural (h : StructuralAxiom pureEff a b) :
    LetCase.LocallyNameless.StructuralAxiom pureEff (embed a) (embed b) := by
  cases h with
  | letBeta hp =>
    simp only [embed, embed_instantiate]
    exact .letBeta (embed_pure hp)
  | letEta _ => exact .letEta _
  | unitEta _ => exact .unitEta _
  | pairBeta a b c =>
    simpa only [embed, embed_lift] using
      LetCase.LocallyNameless.StructuralAxiom.pairBeta (pureEff := pureEff)
        (embed a) (embed b) (embed c)
  | pairEta _ => exact .pairEta _

omit [HasEff Φ ε] in
/-- Inclusion commutes with the binder renamings in sequencing conversions. -/
theorem embed_sequencing (h : SequencingAxiom pureEff a b) :
    LetCase.LocallyNameless.SequencingAxiom pureEff (embed a) (embed b) := by
  cases h with
  | bindOp a c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetCase.LocallyNameless.SequencingAxiom.bindOp (pureEff := pureEff)
        (embed a) (embed c)
  | bindLet a b c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetCase.LocallyNameless.SequencingAxiom.bindLet (pureEff := pureEff)
        (embed a) (embed b) (embed c)
  | bindLetPair e c d =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetCase.LocallyNameless.SequencingAxiom.bindLetPair (pureEff := pureEff)
        (embed e) (embed c) (embed d)
  | bindPair a c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetCase.LocallyNameless.SequencingAxiom.bindPair (pureEff := pureEff)
        (embed a) (embed c)

theorem embed_core (h : CoreAxiom pureEff a b) :
    LetCase.LocallyNameless.CoreAxiom pureEff (embed a) (embed b) := by
  cases h with
  | structural h => exact .structural (embed_structural h)
  | sequencing h => exact .sequencing (embed_sequencing h)

/-- All raw equational derivations translate, not merely the generating axioms. -/
theorem embed_rawEquiv (h : RawEquiv pureEff a b) :
    LetCase.LocallyNameless.RawEquiv pureEff (embed a) (embed b) := by
  induction h with
  | refl a => exact .refl (embed a)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | ax h => exact .ax (embed_core h)
  | op h ih => exact .op ih
  | let₁ h k ih ik => exact .let₁ ih ik
  | pair h k ih ik => exact .pair ih ik
  | let₂ h k ih ik => exact .let₂ ih ik

/-- Directed preservation is relative to preservation of primitive rewrites. -/
theorem embed_rawRefinement {R : RawRelation ν Φ}
    {Q : LetCase.LocallyNameless.RawRelation ν Φ}
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b))
    (h : RawRefinement pureEff R a b) :
    LetCase.LocallyNameless.RawRefinement pureEff Q (embed a) (embed b) := by
  apply RawRefinement.least
    (Q := fun {_} a b => LetCase.LocallyNameless.RawRefinement pureEff Q (embed a) (embed b)) _ h
  exact {
    equiv := fun h => .equiv (embed_rawEquiv h)
    primitive := fun h => .primitive (hRQ h)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
  }

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Inclusion preserves exact equational derivations and endpoint typing. -/
theorem embed_equiv (h : Equiv pureEff Γ β a b A) :
    LetCase.LocallyNameless.Equiv pureEff Γ β (embed a) (embed b) A := by
  induction h with
  | refl h => exact .refl (embed_hasType h)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | ax h ha hb => exact .ax (embed_core h) (embed_hasType ha) (embed_hasType hb)
  | op h ih => exact .op ih
  | let₁ h k ih ik => exact .let₁ ih ik
  | unit => exact .unit
  | pair h k ih ik => exact .pair ih ik
  | let₂ h k ih ik => exact .let₂ ih ik

/-- Directed preservation is relative to preservation of primitive rewrites. -/
theorem embed_refinement {R : TypedRelation ν Φ τ}
    {Q : LetCase.LocallyNameless.TypedRelation ν Φ τ}
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}, R β a b A → Q β (embed a) (embed b) A)
    (h : Refinement pureEff Γ R β a b A) :
    LetCase.LocallyNameless.Refinement pureEff Γ Q β (embed a) (embed b) A := by
  apply Refinement.least
    (Q := fun {_} β a b A => LetCase.LocallyNameless.Refinement pureEff Γ Q β (embed a) (embed b) A) _ h
  exact {
    equiv := fun h => .equiv (embed_equiv h)
    primitive := fun h ha hb => .primitive (hRQ h) (embed_hasType ha) (embed_hasType hb)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
  }

end Silmaril.Isotope.Morphism.SeqCase

namespace Silmaril.Isotope.Morphism.CaseIter

open LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type r} [HasEff Φ ε]
  {pureEff : ε} {n : Nat} {a b : Tm ν Φ n}

/-- Constructor inclusion preserves every structural axiom scheme. -/
theorem embed_structural (h : StructuralAxiom pureEff a b) :
    LetIter.LocallyNameless.StructuralAxiom pureEff (embed a) (embed b) := by
  cases h with
  | letBeta hp =>
    simp only [embed, embed_instantiate]
    exact .letBeta (embed_pure hp)
  | letEta _ => exact .letEta _
  | unitEta _ => exact .unitEta _
  | pairBeta a b c =>
    simpa only [embed, embed_lift] using
      LetIter.LocallyNameless.StructuralAxiom.pairBeta (pureEff := pureEff)
        (embed a) (embed b) (embed c)
  | pairEta _ => exact .pairEta _
  | caseBetaL e l r => exact .caseBetaL (embed e) (embed l) (embed r)
  | caseBetaR e l r => exact .caseBetaR (embed e) (embed l) (embed r)
  | caseEta _ => exact .caseEta _
  | emptyInitial a b c => exact .emptyInitial (embed a) (embed b) (embed c)

omit [HasEff Φ ε] in
/-- Inclusion commutes with the binder renamings in sequencing conversions. -/
theorem embed_sequencing (h : SequencingAxiom pureEff a b) :
    LetIter.LocallyNameless.SequencingAxiom pureEff (embed a) (embed b) := by
  cases h with
  | bindOp a c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindOp (pureEff := pureEff)
        (embed a) (embed c)
  | bindLet a b c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindLet (pureEff := pureEff)
        (embed a) (embed b) (embed c)
  | bindLetPair e c d =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindLetPair (pureEff := pureEff)
        (embed e) (embed c) (embed d)
  | bindPair a c =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindPair (pureEff := pureEff)
        (embed a) (embed c)
  | bindLetCase e l r d =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindLetCase (pureEff := pureEff)
        (embed e) (embed l) (embed r) (embed d)
  | bindCase e l r =>
    simpa only [embed, embed_underBinder, embed_underTwoBinders] using
      LetIter.LocallyNameless.SequencingAxiom.bindCase (pureEff := pureEff)
        (embed e) (embed l) (embed r)

theorem embed_core (h : CoreAxiom pureEff a b) :
    LetIter.LocallyNameless.CoreAxiom pureEff (embed a) (embed b) := by
  cases h with
  | structural h => exact .structural (embed_structural h)
  | sequencing h => exact .sequencing (embed_sequencing h)

/-- All raw equational derivations translate, not merely the generating axioms. -/
theorem embed_rawEquiv (h : RawEquiv pureEff a b) :
    LetIter.LocallyNameless.RawEquiv pureEff (embed a) (embed b) := by
  induction h with
  | refl a => exact .refl (embed a)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | ax h => exact .ax (embed_core h)
  | op h ih => exact .op ih
  | let₁ h k ih ik => exact .let₁ ih ik
  | pair h k ih ik => exact .pair ih ik
  | let₂ h k ih ik => exact .let₂ ih ik
  | inl h ih => exact .inl ih
  | inr h ih => exact .inr ih
  | case e l r ie il ir => exact .case ie il ir
  | abort h ih => exact .abort ih

/-- Directed preservation is relative to preservation of primitive rewrites. -/
theorem embed_rawRefinement {R : RawRelation ν Φ}
    {Q : LetIter.LocallyNameless.RawRelation ν Φ}
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b))
    (h : RawRefinement pureEff R a b) :
    LetIter.LocallyNameless.RawRefinement pureEff Q (embed a) (embed b) := by
  apply RawRefinement.least
    (Q := fun {_} a b => LetIter.LocallyNameless.RawRefinement pureEff Q (embed a) (embed b)) _ h
  exact {
    equiv := fun h => .equiv (embed_rawEquiv h)
    primitive := fun h => .primitive (hRQ h)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
    inl := .inl
    inr := .inr
    case := .case
    abort := .abort
  }

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Inclusion preserves exact equational derivations and endpoint typing. -/
theorem embed_equiv (h : Equiv pureEff Γ β a b A) :
    LetIter.LocallyNameless.Equiv pureEff Γ β (embed a) (embed b) A := by
  induction h with
  | refl h => exact .refl (embed_hasType h)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | ax h ha hb => exact .ax (embed_core h) (embed_hasType ha) (embed_hasType hb)
  | op h ih => exact .op ih
  | let₁ h k ih ik => exact .let₁ ih ik
  | unit => exact .unit
  | pair h k ih ik => exact .pair ih ik
  | let₂ h k ih ik => exact .let₂ ih ik
  | inl h ih => exact .inl ih
  | inr h ih => exact .inr ih
  | case e l r ie il ir => exact .case ie il ir
  | abort h ih => exact .abort ih

/-- Directed preservation is relative to preservation of primitive rewrites. -/
theorem embed_refinement {R : TypedRelation ν Φ τ}
    {Q : LetIter.LocallyNameless.TypedRelation ν Φ τ}
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}, R β a b A → Q β (embed a) (embed b) A)
    (h : Refinement pureEff Γ R β a b A) :
    LetIter.LocallyNameless.Refinement pureEff Γ Q β (embed a) (embed b) A := by
  apply Refinement.least
    (Q := fun {_} β a b A => LetIter.LocallyNameless.Refinement pureEff Γ Q β (embed a) (embed b) A) _ h
  exact {
    equiv := fun h => .equiv (embed_equiv h)
    primitive := fun h ha hb => .primitive (hRQ h) (embed_hasType ha) (embed_hasType hb)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
    inl := .inl
    inr := .inr
    case := .case
    abort := .abort
  }

end Silmaril.Isotope.Morphism.CaseIter


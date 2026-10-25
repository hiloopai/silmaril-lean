module

public import Silmaril.Logic.HOLLight.Inference
public import Silmaril.Logic.HOLLight.Classical.ExcludedMiddle
public import Silmaril.Logic.Metatheory.InferenceMorphism
public import Cslib.Logics.Propositional.NaturalDeduction.Theory

@[expose] public section

/-!
# Propositional reasoning inside HOL Light

CSLib's natural-deduction formulas may use any well-typed HOL Boolean terms as
atoms. Translation constructs a HOL derivation, using the derived logical
rules, rather than appealing to semantic validity or completeness.

Source theories can be infinite sets of propositional axioms. Their use is
justified by supplied HOL derivations, and does not extend HOL's finite object
theory. Both source and target assumption contexts are explicit.
-/

namespace Silmaril.Logic.HOLLight.Propositional

universe u

open Cslib.Logic

variable {Atom : Type u} {sig : Signature}

/-- Interpret propositional atoms by checked Boolean HOL terms. -/
def interpret (atoms : Atom → Formula sig) : PL.Proposition Atom → Formula sig
  | .atom a => atoms a
  | .and p q =>
      ⟨Tm.conj (interpret atoms p).term (interpret atoms q).term,
        (interpret atoms p).typing.conj (interpret atoms q).typing⟩
  | .or p q =>
      ⟨Tm.disj (interpret atoms p).term (interpret atoms q).term,
        (interpret atoms p).typing.disj (interpret atoms q).typing⟩
  | .imp p q =>
      ⟨Tm.imp (interpret atoms p).term (interpret atoms q).term,
        (interpret atoms p).typing.imp (interpret atoms q).typing⟩

@[simp] theorem interpret_atom (atoms : Atom → Formula sig) (a : Atom) :
    interpret atoms (.atom a) = atoms a := rfl

@[simp] theorem interpret_and (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    interpret atoms (.and p q) = HasAnd.and (interpret atoms p) (interpret atoms q) := rfl

@[simp] theorem interpret_or (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    interpret atoms (.or p q) = HasOr.or (interpret atoms p) (interpret atoms q) := rfl

@[simp] theorem interpret_imp (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    interpret atoms (.imp p q) = HasImp.imp (interpret atoms p) (interpret atoms q) := rfl

/-- Interpreting substituted propositions is the same as interpreting their
new atoms first. This includes noninjective atom assignments. -/
theorem interpret_subst {Atom' : Type u} (atoms : Atom' → Formula sig)
    (σ : Atom → PL.Proposition Atom') (p : PL.Proposition Atom) :
    interpret atoms (p.subst σ) = interpret (fun a => interpret atoms (σ a)) p := by
  induction p with
  | atom a => rfl
  | and p q ihp ihq => exact congrArg₂ HasAnd.and ihp ihq
  | or p q ihp ihq => exact congrArg₂ HasOr.or ihp ihq
  | imp p q ihp ihq => exact congrArg₂ HasImp.imp ihp ihq

/-- The raw syntax underlying the checked interpretation. -/
abbrev translate (atoms : Atom → Formula sig) (p : PL.Proposition Atom) : Tm :=
  (interpret atoms p).term

@[simp] theorem translate_atom (atoms : Atom → Formula sig) (a : Atom) :
    translate atoms (.atom a) = (atoms a).term := rfl

@[simp] theorem translate_and (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    translate atoms (.and p q) = Tm.conj (translate atoms p) (translate atoms q) := rfl

@[simp] theorem translate_or (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    translate atoms (.or p q) = Tm.disj (translate atoms p) (translate atoms q) := rfl

@[simp] theorem translate_imp (atoms : Atom → Formula sig) (p q : PL.Proposition Atom) :
    translate atoms (.imp p q) = Tm.imp (translate atoms p) (translate atoms q) := rfl

theorem translate_typed (atoms : Atom → Formula sig) (p : PL.Proposition Atom) :
    HasType sig [] (translate atoms p) .bool := (interpret atoms p).typing

theorem translate_subst {Atom' : Type u} (atoms : Atom' → Formula sig)
    (σ : Atom → PL.Proposition Atom') (p : PL.Proposition Atom) :
    translate atoms (p.subst σ) = translate (fun a => interpret atoms (σ a)) p :=
  congrArg Checked.term (interpret_subst atoms σ p)

/-- Map a finite propositional context, allowing distinct atoms to coincide. -/
def translateCtx (atoms : Atom → Formula sig) (Γ : PL.Ctx Atom) : Hyps :=
  Γ.image (translate atoms)

@[simp] theorem translateCtx_empty (atoms : Atom → Formula sig) :
    translateCtx atoms ∅ = ∅ := Finset.image_empty _

@[simp] theorem translateCtx_insert [DecidableEq Atom] (atoms : Atom → Formula sig)
    (p : PL.Proposition Atom) (Γ : PL.Ctx Atom) :
    translateCtx atoms (insert p Γ) = insert (translate atoms p) (translateCtx atoms Γ) :=
  Finset.image_insert _ _ _

theorem translateCtx_typed (atoms : Atom → Formula sig) (Γ : PL.Ctx Atom) :
    TypedHyps sig [] (translateCtx atoms Γ) := by
  intro t ht
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
  exact translate_typed atoms p

private theorem typedUnion {H K : Hyps} (hH : TypedHyps sig [] H)
    (hK : TypedHyps sig [] K) : TypedHyps sig [] (H ∪ K) := by
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact hH t ht
  · exact hK t ht

private theorem typedInsert {H : Hyps} {p : Tm} (hH : TypedHyps sig [] H)
    (hp : HasType sig [] p .bool) : TypedHyps sig [] (insert p H) := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact hp
  · exact hH t ht

variable [DecidableEq Atom] {T : PL.Theory Atom} {theory : Theory}
  {Γ : PL.Ctx Atom} {H : Hyps} {p : PL.Proposition Atom}

/-- Translate a natural-deduction tree, retaining a fixed HOL context for the
supplied source axioms and adjoining the translated source hypotheses. -/
theorem translate_derivation (atoms : Atom → Formula sig) (typedH : TypedHyps sig [] H)
    (axioms : ∀ a ∈ T, Derives sig theory H (translate atoms a))
    (proof : T.Derivation Γ p) :
    Derives sig theory (H ∪ translateCtx atoms Γ) (translate atoms p) := by
  induction proof with
  | ax member =>
      exact (axioms _ member).weaken Finset.subset_union_left
        (typedUnion typedH (translateCtx_typed atoms _))
  | ass member =>
      exact Derives.assumeIn (typedUnion typedH (translateCtx_typed atoms _))
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, member, rfl⟩))
  | andI _ _ ih₁ ih₂ => exact ih₁.conjIntroSame ih₂
  | andE₁ _ ih => exact Derives.conjElimLeft (translate_typed atoms _) (translate_typed atoms _) ih
  | andE₂ _ ih => exact Derives.conjElimRight (translate_typed atoms _) (translate_typed atoms _) ih
  | orI₁ _ ih => exact ih.disjIntroLeft (translate_typed atoms _)
  | orI₂ _ ih => exact Derives.disjIntroRight (translate_typed atoms _) ih
  | orE _ _ _ ih ih₁ ih₂ =>
      apply Derives.disjElim (translate_typed atoms _) (translate_typed atoms _)
        (translate_typed atoms _) ih
      · simpa only [translateCtx_insert, Finset.union_insert] using ih₁
      · simpa only [translateCtx_insert, Finset.union_insert] using ih₂
  | implI _ _ ih =>
      apply Derives.impIntro (translate_typed atoms _)
      simpa only [translateCtx_insert, Finset.union_insert] using ih
  | implE _ _ ih₁ ih₂ => exact Derives.impElimSame (translate_typed atoms _) ih₁ ih₂

/-- Preserve a source derivation in the user-specified fixed HOL context when
that context proves the translated source assumptions and axioms. -/
theorem deriveAt (atoms : Atom → Formula sig) (typedH : TypedHyps sig [] H)
    (axioms : ∀ a ∈ T, Derives sig theory H (translate atoms a))
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate atoms a))
    (proof : T.Derivation Γ p) : Derives sig theory H (translate atoms p) := by
  apply (translate_derivation atoms typedH axioms proof).substituteHyps typedH
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Derives.assumeIn typedH ht
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    exact hypotheses a ha

/-- The fixed-context inference-system tag for CSLib natural deduction. -/
inductive ContextSystem (T : PL.Theory Atom) (Γ : PL.Ctx Atom) : Type where
  | tag

instance (T : PL.Theory Atom) (Γ : PL.Ctx Atom) :
    InferenceSystem (ContextSystem T Γ) (PL.Proposition Atom) where
  derivation p := T.Derivation Γ p

/-- A proof-preserving map between the two fixed-context inference systems. -/
def morphism (atoms : Atom → Formula sig) (typedH : TypedHyps sig [] H)
    (axioms : ∀ a ∈ T, Derives sig theory H (translate atoms a))
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate atoms a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism (ContextSystem T Γ)
      (HOLLight.ContextSystem sig theory H) (PL.Proposition Atom) (Formula sig) where
  map := interpret atoms
  mapDerivation := deriveAt atoms typedH axioms hypotheses

/-- Identity atom interpretation: every checked HOL Boolean may be used as a
propositional atom, with both assumption contexts fixed explicitly. -/
def formulaMorphism {T : PL.Theory (Formula sig)} {Γ : PL.Ctx (Formula sig)}
    (typedH : TypedHyps sig [] H)
    (axioms : ∀ a ∈ T, Derives sig theory H (translate id a))
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate id a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism (ContextSystem T Γ)
      (HOLLight.ContextSystem sig theory H) (PL.Proposition (Formula sig)) (Formula sig) :=
  morphism id typedH axioms hypotheses

/-- Minimal propositional derivability needs no additional HOL axiom. -/
theorem minimal (atoms : Atom → Formula sig)
    (proof : (PL.Theory.MPL Atom).Derivation Γ p) :
    Derives sig theory (translateCtx atoms Γ) (translate atoms p) := by
  have hH : TypedHyps sig [] (∅ : Hyps) := by intro t ht; simp at ht
  simpa only [Finset.empty_union] using
    translate_derivation (theory := theory) atoms hH (fun _ h => False.elim h) proof

/-- Minimal propositional reasoning as a morphism into an arbitrary HOL
theory and fixed hypothesis context. -/
def minimalMorphism (atoms : Atom → Formula sig) (typedH : TypedHyps sig [] H)
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate atoms a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism (ContextSystem (PL.Theory.MPL Atom) Γ)
      (HOLLight.ContextSystem sig theory H) (PL.Proposition Atom) (Formula sig) :=
  morphism atoms typedH (fun _ h => False.elim h) hypotheses

/-- Direct proposition-valued preservation for the fixed source context. -/
theorem derivableAt (atoms : Atom → Formula sig) (typedH : TypedHyps sig [] H)
    (axioms : ∀ a ∈ T, Derives sig theory H (translate atoms a))
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate atoms a))
    (proof : InferenceSystem.DerivableIn (ContextSystem T Γ) p) :
    Derives sig theory H (translate atoms p) := by
  obtain ⟨proof⟩ := proof
  exact deriveAt atoms typedH axioms hypotheses proof

private theorem exFalso {t : Tm} (ht : HasType sig [] t .bool) :
    Derives sig theory ∅ (Tm.imp Tm.falsity t) := by
  apply Derives.impIntro HasType.falsity
  apply Derives.falsityElim ht
  simpa only [Finset.insert_empty] using (Derives.assume (sig := sig) (theory := theory) HasType.falsity)

private theorem doubleNegation {t : Tm} (ht : HasType sig [] t .bool) :
    Derives sig classicalTheory ∅ (Tm.imp (Tm.neg (Tm.neg t)) t) := by
  have h₀ : TypedHyps sig [] (∅ : Hyps) := by intro r hr; simp at hr
  let H := insert (Tm.neg (Tm.neg t)) (∅ : Hyps)
  have hH : TypedHyps sig [] H := typedInsert h₀ ht.neg.neg
  have alternatives : Derives sig classicalTheory H (Tm.disj t (Tm.neg t)) :=
    (Derives.excludedMiddle ht).weaken (Finset.empty_subset _) hH
  have left : Derives sig classicalTheory (insert t H) t :=
    Derives.assumeIn (typedInsert hH ht) (Finset.mem_insert_self _ _)
  have right : Derives sig classicalTheory (insert (Tm.neg t) H) t := by
    have hK := typedInsert hH ht.neg
    have hnnt : Derives sig classicalTheory (insert (Tm.neg t) H) (Tm.neg (Tm.neg t)) :=
      Derives.assumeIn hK (by simp [H])
    have hnt : Derives sig classicalTheory (insert (Tm.neg t) H) (Tm.neg t) :=
      Derives.assumeIn hK (by simp)
    exact Derives.falsityElim ht (Derives.impElimSame HasType.falsity hnnt hnt)
  exact Derives.impIntro ht.neg.neg (Derives.disjElim ht ht.neg ht alternatives left right)

section Bottom

variable [Bot Atom]

omit [DecidableEq Atom] in
/-- The designated false atom is the only extra condition needed to
interpret intuitionistic and classical source theories. -/
theorem translate_neg (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) (p : PL.Proposition Atom) :
    translate atoms p.neg = Tm.neg (translate atoms p) := by
  change Tm.imp (translate atoms p) (atoms ⊥).term = _
  rw [bottom]
  rfl

omit [DecidableEq Atom] in
@[simp] theorem interpret_neg (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) (p : PL.Proposition Atom) :
    interpret atoms p.neg = HasNot.not (interpret atoms p) :=
  Formula.ext (translate_neg atoms bottom p)

omit [DecidableEq Atom] in
@[simp] theorem interpret_bot (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) :
    interpret atoms (⊥ : PL.Proposition Atom) = (⊥ : Formula sig) :=
  Formula.ext bottom

omit [DecidableEq Atom] in
theorem intuitionisticAxioms (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) :
    ∀ a ∈ PL.Theory.IPL Atom, Derives sig theory ∅ (translate atoms a) := by
  rintro a ⟨p, rfl⟩
  change Derives sig theory ∅ (Tm.imp (atoms ⊥).term (translate atoms p))
  rw [bottom]
  exact exFalso (translate_typed atoms p)

omit [DecidableEq Atom] in
theorem classicalAxioms (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) :
    ∀ a ∈ PL.Theory.CPL Atom, Derives sig classicalTheory ∅ (translate atoms a) := by
  rintro a ⟨p, rfl⟩
  change Derives sig classicalTheory ∅ (Tm.imp (translate atoms p.neg.neg) (translate atoms p))
  rw [translate_neg atoms bottom, translate_neg atoms bottom]
  exact doubleNegation (translate_typed atoms p)

/-- Intuitionistic propositional proofs translate into every HOL theory. -/
theorem intuitionistic (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity)
    (proof : (PL.Theory.IPL Atom).Derivation Γ p) :
    Derives sig theory (translateCtx atoms Γ) (translate atoms p) := by
  have hH : TypedHyps sig [] (∅ : Hyps) := by intro t ht; simp at ht
  simpa only [Finset.empty_union] using
    translate_derivation atoms hH (intuitionisticAxioms atoms bottom) proof

/-- Classical propositional proofs translate using HOL's derived classical
reasoning, with no additional target axiom. -/
theorem classicalDerivation (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity)
    (proof : (PL.Theory.CPL Atom).Derivation Γ p) :
    Derives sig classicalTheory (translateCtx atoms Γ) (translate atoms p) := by
  have hH : TypedHyps sig [] (∅ : Hyps) := by intro t ht; simp at ht
  simpa only [Finset.empty_union] using
    translate_derivation atoms hH (classicalAxioms atoms bottom) proof

def intuitionisticMorphism (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) (typedH : TypedHyps sig [] H)
    (hypotheses : ∀ a ∈ Γ, Derives sig theory H (translate atoms a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism (ContextSystem (PL.Theory.IPL Atom) Γ)
      (HOLLight.ContextSystem sig theory H) (PL.Proposition Atom) (Formula sig) :=
  morphism atoms typedH
    (fun a ha => (intuitionisticAxioms atoms bottom a ha).weaken (Finset.empty_subset _) typedH)
    hypotheses

def classicalMorphism (atoms : Atom → Formula sig)
    (bottom : (atoms ⊥).term = Tm.falsity) (typedH : TypedHyps sig [] H)
    (hypotheses : ∀ a ∈ Γ, Derives sig classicalTheory H (translate atoms a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism (ContextSystem (PL.Theory.CPL Atom) Γ)
      (HOLLight.ContextSystem sig classicalTheory H) (PL.Proposition Atom) (Formula sig) :=
  morphism atoms typedH
    (fun a ha => (classicalAxioms atoms bottom a ha).weaken (Finset.empty_subset _) typedH)
    hypotheses

end Bottom

/-- Classical propositional formulas over checked HOL Booleans, interpreted by
the identity on atoms, into an explicitly chosen HOL hypothesis context. -/
def classicalFormulaMorphism {Γ : PL.Ctx (Formula sig)} (typedH : TypedHyps sig [] H)
    (hypotheses : ∀ a ∈ Γ, Derives sig classicalTheory H (translate id a)) :
    Silmaril.Logic.Metatheory.InferenceMorphism
      (ContextSystem (PL.Theory.CPL (Formula sig)) Γ)
      (HOLLight.ContextSystem sig classicalTheory H) (PL.Proposition (Formula sig)) (Formula sig) :=
  classicalMorphism id rfl typedH hypotheses

/-- The canonical classical morphism uses exactly the translated source
hypotheses; no proof obligations are left to its caller. -/
def classicalContextMorphism (sig : Signature) (Γ : PL.Ctx (Formula sig)) :
    Silmaril.Logic.Metatheory.InferenceMorphism
      (ContextSystem (PL.Theory.CPL (Formula sig)) Γ)
      (HOLLight.ContextSystem sig classicalTheory (translateCtx id Γ))
      (PL.Proposition (Formula sig)) (Formula sig) :=
  classicalFormulaMorphism (translateCtx_typed id Γ)
    (fun a ha => Derives.assumeIn (translateCtx_typed id Γ) (Finset.mem_image.mpr ⟨a, ha, rfl⟩))

end Silmaril.Logic.HOLLight.Propositional

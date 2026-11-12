module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Theories
public import Silmaril.Raw.SSA.Isotope.Morphism.ProofRelevantModels

@[expose] public section

/-!
# Proof-relevant let calculi in the refinement institution

The proof-relevant typed syntax keeps typing and subtyping witnesses as data
(`Theory/Models/ProofRelevant{Seq,Case}.lean`); it is again a presented signature, and the
constructions of `Isotope.lean` apply verbatim. The let-seq ⊆ let-case inclusion is a theory
morphism whose soundness is the derivation embedding of `RefinementEmbedding.lean`
(`LetSeq.ProofRelevant.LocallyNameless.Refinement.Deriv.embed`), and its reduct is
`Morphism.SeqCase.ProofRelevant.refinementModelRestriction`.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open PSig

universe u v w r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

/-- Proof-relevant typed let-seq syntax in context `Γ`, as a presented signature. -/
abbrev prSeqPSig (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :=
  PSig.mk (TypingIndex τ) (LetSeq.ProofRelevant.LocallyNameless.Models.signature Φ Γ)
    (LetSeq.ProofRelevant.LocallyNameless.Models.syntaxAlgebra Φ Γ)
    (LetSeq.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ)

/-- Proof-relevant typed let-case syntax in context `Γ`, as a presented signature. -/
abbrev prCasePSig (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :=
  PSig.mk (TypingIndex τ) (LetCase.ProofRelevant.LocallyNameless.Models.signature Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.syntaxAlgebra Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.syntaxIsInitial Φ Γ)

/-- The proof-relevant let-seq refinement theory of primitive rewrites `R`. -/
abbrev prSeqTheory (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) :=
  theoryOf (P := prSeqPSig Φ Γ)
    (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R)

/-- The proof-relevant let-case refinement theory of primitive rewrites `S`. -/
abbrev prCaseTheory (pureEff : ε) (Γ : Ctx ν τ)
    (S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) :=
  theoryOf (P := prCasePSig Φ Γ)
    (LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ S)

/-- Consequence of `a ⊑ b` is witness-sensitive generated refinement. A restatement of
`LetSeq.ProofRelevant.LocallyNameless.Models.refinement_iff_all_models`, and derived from
it. -/
theorem prSeq_entails_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ}
    (a b : LetSeq.ProofRelevant.LocallyNameless.Models.Carrier Φ Γ i) :
    (institution.obj (prSeqPSig Φ Γ)).Entails (prSeqTheory pureEff Γ R).sentences
        ([⟨i, a, b⟩] : Sentence (prSeqPSig Φ Γ)) ↔
      LetSeq.ProofRelevant.LocallyNameless.Refinement.Related pureEff Γ R a.2 b.2 :=
  (entails_singleton_iff (P := prSeqPSig Φ Γ)
    (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R) a b).trans
    (LetSeq.ProofRelevant.LocallyNameless.Models.refinement_iff_all_models pureEff Γ R a b)

/-- The proof-relevant let-seq ⊆ let-case inclusion, as a morphism of presented signatures. -/
abbrev prSeqCaseHom (Γ : Ctx ν τ) : prSeqPSig Φ Γ ⟶ prCasePSig Φ Γ :=
  Morphism.SeqCase.ProofRelevant.signatureHom Γ

/-- Its syntax translation is the witness-preserving inclusion
`Morphism.SeqCase.ProofRelevant.algebraHom` (by initiality). -/
theorem translate_prSeqCaseHom (Γ : Ctx ν τ) :
    translate (prSeqCaseHom (Φ := Φ) Γ) = Morphism.SeqCase.ProofRelevant.algebraHom Γ :=
  (prSeqPSig Φ Γ).isInitial.hom_ext _ _

/-- A primitive inclusion `R ≤ restrict S` makes the proof-relevant let-seq ⊆ let-case
inclusion a morphism of refinement theories. Soundness is the derivation embedding
`LetSeq.ProofRelevant.LocallyNameless.Refinement.Deriv.embed` (`RefinementEmbedding.lean`). -/
def prSeqCaseTheoryHom (pureEff : ε) (Γ : Ctx ν τ)
    {R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory.restrict S) :
    prSeqTheory pureEff Γ R ⟶ prCaseTheory pureEff Γ S :=
  theoryHom (prSeqCaseHom Γ) (fun h => by
    rw [translate_prSeqCaseHom]
    exact h.map (LetSeq.ProofRelevant.LocallyNameless.Refinement.Deriv.embed f))

/-- The reduct along `prSeqCaseTheoryHom` is the existing restriction
`Morphism.SeqCase.ProofRelevant.refinementModelRestriction`. -/
theorem prSeqCase_reduct (pureEff : ε) (Γ : Ctx ν τ)
    {R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    {S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ}
    (f : R ≤ LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory.restrict S) :
    Silmaril.Logic.Institution.Theory.reduct (prSeqCaseTheoryHom pureEff Γ f) ⋙
        toOrderedModels (P := prSeqPSig Φ Γ)
          (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R) =
      toOrderedModels (P := prCasePSig Φ Γ)
          (LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ S) ⋙
        Morphism.SeqCase.ProofRelevant.refinementModelRestriction pureEff Γ f :=
  reduct_comp_toOrderedModels (prSeqCaseHom Γ) _

end Silmaril.Isotope.Institution.Refinement

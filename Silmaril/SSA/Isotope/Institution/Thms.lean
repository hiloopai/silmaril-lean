module

public import Silmaril.Raw.SSA.Isotope.Institution.Borrowing
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Comorphism
public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Isomorphism
public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Compilations
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetSeq
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetCase
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetIter
public import Silmaril.Raw.SSA.Isotope.Institution.Observational.Examples
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.CategoriesCase
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.CategoriesSeq
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Example
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Isotope
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.ProofRelevant
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.Embedding
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.EquationEmbedding
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.Refinement
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementCategories
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementEmbedding
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementInference
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementOrder
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementTheory
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.TypedEquiv
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.TypingSubst
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.Refinement
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.RefinementCategories
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.RefinementInference
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.RefinementOrder
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.RefinementTheory
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.TypedEquiv
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.TypingSubst
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.Embedding
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.EquationEmbedding
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.Refinement
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementCategories
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementEmbedding
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementInference
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementOrder
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementTheory
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.TypedEquiv
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.TypingSubst
public import Silmaril.Raw.SSA.Isotope.Morphism.OrderedModels
public import Silmaril.Raw.SSA.Isotope.Morphism.ProofRelevantModels
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Examples
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevant
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevantCase
public import Silmaril.Raw.SSA.Isotope.Theory.Models.ProofRelevantSeq
public import Silmaril.Raw.SSA.Isotope.Theory.Models.RawRefinement
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Refinement

/-!
# Let-family institutions and syntactic initiality

Re-exports the Raw let-family institution development. Checked results, by name:

* Equational institutions `Silmaril.Isotope.Institution.{LetSeq,LetCase,LetIter}.inst :
  InstrSig τ ε ⥤ Room` over instruction signatures, in a fixed free-variable context `Γ`;
  semantic consequence from the base theory is derivable equivalence
  (`entails_base_iff`, `entails_theory_iff`).
* Comorphisms (and their adjoint morphisms) along the inclusions let-seq ⊆ let-case ⊆ let-iter:
  `seqCaseCoHom`, `caseIterCoHom`, `seqCaseHom`, `caseIterHom`; **borrowing** of consequence
  unconditionally: `seqCase_entails_iff_of_any`, `caseIter_entails_iff_of_any`.
* Initiality of syntax: `{LetSeq,LetCase,LetIter}.LocallyNameless.Models.syntaxIsInitial`
  (exact typing derivations, initial operation algebra) and `syntacticModelIsInitial`
  (syntax modulo the equational theory is initial among *algebras of the equational
  presentation* — not among Freyd/Elgot categories), with completeness `semantic_iff`.
* Refinement institution family and the comorphism `Refinement.eqToRef` from equations to
  refinements (model-expansive: `eqToRef_modelExpansive`).
* Observational institutions of let-case, let-iter and λSSA, compilations as comorphisms
  (`Observational.caseIter`, `Observational.iterSSA`), and the **isomorphism in `CoIns`**
  `Observational.iterSSAIso` between let-iter and *single-exit* λSSA observational institutions
  modulo observational equivalence (round trips proved on sentences).

Relation to the thesis port (`Silmaril.SSA.Thesis.Thms`): see `docs/projects/ssa.md`.
-/

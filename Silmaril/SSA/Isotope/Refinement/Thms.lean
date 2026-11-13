module

public import Silmaril.Raw.SSA.Isotope.Refinement.RewriteSystem
public import Silmaril.Raw.SSA.Isotope.Refinement.Categories
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.SubstitutionAdmissibility
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypingTransport
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.SplitDistribution
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlEnvironment
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ContextMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMapVariables
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Directed
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationNaturalityBody
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoaction

/-!
# Quantitative refinement calculus, its operation models and categorical denotation

Re-exports the Raw quantitative refinement development (refinement-model initiality); see
`docs/projects/ssa.md`.
Checked results, by name (namespace `Silmaril.Isotope.Refinement`):

* Quantitative typing (`HasType` over `QCtx`, fragments `Fragment` for seq/case/iter), refinement
  derivations and theories, with structural rules (weakening, splitting, substitution) and
  closure of generated theories under renaming and substitution
  (`RewriteSystem.generatedTheory_renaming`, `generatedTheory_substitution`).
* Initiality of syntax among operation algebras of exact typing derivations:
  `Models.syntaxIsInitial` (with `Models.fold_unique`); syntax modulo a written theory is
  initial among its **algebraic** models: `Models.syntacticModelIsInitial` (equational) and
  `Models.orderedSyntacticModelIsInitial` (ordered, directed rules); completeness
  `Models.refinement_iff_all_models`, `Models.mutual_refinement_iff_all_models`,
  `Models.equation_iff_all_models`. These are initiality among algebras of the presentation,
  not among Freyd/Elgot categories.
* Contextual categories of theories (`Theory.refinementFunctor`, `Theory.equationalFunctor`).
* Categorical interpretation of typing derivations in `SeqModel`/`CaseModel`/`IterModel`
  (`Models.Denotation.denoteSeq`, `denoteCase`, `denoteIter`, uniqueness `fold_unique`) and
  its coherence/naturality lemmas (context splitting, weakening, slots, iteration coaction).
  Soundness and initiality of the *categorical* models (later inventory batches) are not here.
-/

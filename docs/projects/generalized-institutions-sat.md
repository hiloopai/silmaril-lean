# Generalized institutions studies C2 and C8 — SAT valuations

A signature is a type of atoms `A` and a signature morphism is any function `f : A → B`.
A sentence `Problem A` is a conjunction of clauses, each a disjunction of signed atoms.
`Problem.rename` maps atoms and keeps their polarity. `reduct f v` precomposes a target
valuation with `f`. This is the renaming and reduct pattern of the existing
[classical propositional institution](../../Silmaril/Logic/Institution/Examples/Propositional.lean).
`Problem.ofCNF` reads the existing DIMACS CNF as a problem over `Nat`, with evaluation
preserved pointwise by `Problem.eval_ofCNF`. Thus existing SAT and UNSAT still quantify
existentially and universally, respectively, over total Boolean assignments.
[Definitions](../../Silmaril/Logic/SAT/Institution/Defs.lean)

## Compositional evaluation

| Models | Values | Connectives |
| --- | --- | --- |
| Total valuations `A → Bool` | true, false | Boolean operations |
| Strong Kleene valuations `A → K3` | true, false, unknown | Negation fixes unknown. A single false conjunct or true disjunct is decisive. |
| Evidence valuations `A → FDE` | true only `(1,0)`, false only `(0,1)`, neither `(0,0)`, both `(1,1)` | Negation swaps the bits. Conjunction uses AND on support and OR on refutation. Disjunction uses OR on support and AND on refutation. |

The empty clause is false and the empty problem is true in each algebra. In the evidence
**truth order**, support increases and refutation decreases. Conjunction and disjunction
are meet and join. False only is bottom, true only is top, and both and neither are
incomparable. In the **information order**,
both bits increase, with neither at the bottom and both at the top. The strong Kleene
truth order is false < unknown < true. Its information order has unknown below both
definite values, which are incomparable. Both compositional evaluators are monotone in
their respective information orders.
[Finite algebra laws](../../Silmaril/Logic/ManyValued/Thms.lean)

Partial Boolean assignments still have type `A → Option Bool`, with `none` marking an
unassigned atom. `PartialValuation.toK3` converts pointwise. `Problem.evalK3Partial` applies
the typed evaluator after that conversion. For callers that read `Option Bool` results,
`Problem.evalK3Option` projects the result back. `Problem.evalK3Option_eq_evalWith` proves
agreement with the historical strong Kleene fold. Translation and reduct commute at
both boundaries.

`Problem.eval_rename`, `Problem.evalK3_rename` and `Problem.evalEvidence_rename` give exact
evaluation after translation and reduct for every atom map. `Problem.evalK3_total` and
`Problem.evalEvidence_total` give agreement on total assignments. `Problem.evalEvidence_ofK3`
gives agreement throughout the three-value fragment with at most one evidence bit set.
`Problem.evalEvidence_bits` gives the original coordinate-wise Boolean fold for every FDE
valuation, including conflicts.
[Semantic theorems](../../Silmaril/Logic/SAT/Institution/Thms.lean)

## Total completions

A total completion agrees with every known atom. Filling missing atoms with false witnesses
`exists_completion`. `Problem.superEvalK3` returns the typed verdict. Its `Option Bool`
projection is `Problem.superEval`. `Problem.superEval_eq_some` characterizes a definite
result by unanimity among completions. `Problem.superEval_eq_none` characterizes unknown
by a true completion and a false completion. `Problem.completionEvidence_support_iff` and
`Problem.completionEvidence_refute_iff` characterize the independently defined universal
flags. `Problem.completionEvidence_consistent` rules out simultaneous flags because the
completion family is nonempty. `Problem.superEval_total` gives agreement on total assignments, and
`Problem.evalK3_informationLE_superEval` says a definite compositional result survives
completion. Supervaluation here quantifies over total assignments to a strong Kleene partial
valuation. The four-valued evidence semantics also permits conflicting information.

Every target completion reduces to a source completion. By `completion_lifts_iff`, a source
completion lifts exactly when it assigns equal values to atoms identified by the map. A lift
uses the common value on each occupied fibre and fills missing values outside the image.
Consequently injections give equality (`Problem.superEval_rename_of_injective`). For arbitrary
maps, the target quantifies over a possibly smaller collection of reducts. Its result refines
the source in the information order (`Problem.superEval_rename_informationLE`). The same
laws for the two flags are `Problem.completionEvidence_rename_of_coverage` and
`Problem.completionEvidence_rename_informationLE`. The covering hypothesis is stated as
`CompletionCovers`; `completion_reduct_image_subset` and `completion_reduct_image_eq_of_coverage`
give the corresponding set-image laws. [Set-image lemmas](../../Silmaril/Logic/SAT/Institution/Ordinary/Thms.lean)

For `p ∨ ¬q` with both atoms unknown, the source has a falsifying completion `p = false,
q = true` and a satisfying completion. Identifying the atoms rules out the falsifying
completion, so `p ∨ ¬p` is supertrue. Compositional evaluation of the renamed clause at the
unknown atom still gives unknown. [Checked counterexample](../../Silmaril/Logic/SAT/Institution/Examples.lean)

## Ordinary observations and consequence

A predicate on values yields an ordinary satisfaction relation when its truth is invariant
under translation and reduct. Exact value equality gives that condition for every predicate.
The ordinary bundles use discrete valuation categories and the existing `Room` API. The two
strong Kleene bundles observe truth and falsity separately. The two evidence bundles observe
support and refutation separately. An evidence value of `both` meets both predicates and
`neither` meets neither. For supervaluation, injections give the required equivalence. On all
maps, supertruth is preserved from reduct to translation and can be strengthened by
identifying atoms, as the checked example shows. Superfalsity can also be strengthened
when `p ∧ ¬q` becomes `p ∧ ¬p`.
[Ordinary bundles](../../Silmaril/Logic/SAT/Institution/Ordinary/Defs.lean)

In each bundle, `Room.Entails Γ F` quantifies over every valuation that meets the chosen
observation for every premise in `Γ`. Local evaluation produces one value at one model.
For example, entailment in the evidence refutation bundle takes refutation of all premises
as its hypothesis and asks for refutation of the conclusion. Global UNSAT of a CNF says
that every total valuation falsifies it. [Room consequence API](../../Silmaril/Logic/Institution/Room.lean)

## Generalized-core integration

The three exact instances reuse the ordinary sentence and valuation functors and return
`Bool`, `K3` and `FDE`, respectively. `kleeneExact_toOptionBool` relates the K3 result
to the compatibility adapter. The lax instance reads both bits of SAT's noncomputable
completion result as propositions using `fdeToGeneralizedEvidence`.
`completionLax_eval_eq_ofCompletions` identifies those propositions with universal
satisfaction and universal refutation over total completions.
`completionLax_eval_eq_ofSuperEvalK3` gives the same result via the typed K3 embedding
into FDE. Each exact evaluator can use a single type code. A typed instance with all
three evaluations would need a shared model functor, since their valuation carriers differ.
[Generalized instances](generalized-institutions.md#sat-and-per-instances)

For terminology and background, see
[Many-Valued Logic](https://plato.stanford.edu/entries/logic-manyvalued/),
[Belnap, *A Useful Four-Valued Logic*](https://doi.org/10.1007/978-94-010-1161-7_2),
and [Fine, *Vagueness, Truth and Logic*](https://doi.org/10.1007/BF00485047).

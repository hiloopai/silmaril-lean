# Generalized institution evaluation

Import `Silmaril.Logic.Institution.Generalized.Thms` for the interface and laws.
The starting point is the satisfaction condition in Goguen and Burstall,
*Institutions: Abstract Model Theory for Specification and Programming* (1992),
§2.1, Definition 1, and the distinction from semantic consequence in §2.2,
Definition 2(9). The existing `goguen-burstall-1992` entry records the DOI and
artifact hash. [Bibliography](../../references.bib)

## Evaluation and consequence

`ExactInstitution Sign D` uses the sentence functor `Sen : Sign ⥤ Type` and
model functor `Mod : Signᵒᵖ ⥤ Cat` of `ClassicInstitution`. For `σ : S ⟶ T`,
a model `M` over `T` and a sentence `φ` over `S`, `eval_map` gives

```text
eval T M (Sen.map σ φ) = eval S (reduct σ M) φ.
```

The two evaluations are elements of the same fixed type `D`. A lattice is one
choice of `D`. The exact law works with any value type. In a
`TypedInstitution Sign Denote`, the type code `t` and its denotation
`Denote t` are fixed across signatures. Each `Sen t` is a functor, so
translation of syntax at that type preserves identities and composition.
`atType t` gives an exact institution with value type `Denote t`.

`observe P` reads a value as satisfaction by applying a fixed predicate
`P : D → Prop`. It keeps the sentence functor and the entire model functor,
and its `ClassicInstitution` can be used as a room functor via `toRoomFunctor`.
The induced consequence `Evaluation.entails P Γ φ` says every model that passes
`P` on each premise in `Γ` also passes `P` on `φ`. The theorem
`ExactInstitution.entails_iff_room_entails` identifies this with the existing
`Room.Entails`. The existing corridor laws then give preservation under
translation and reflection when the reduct is surjective on models.
[Classic API](../../Silmaril/Logic/Institution/Basic.lean) ·
[Room laws](../../Silmaril/Logic/Institution/Room.lean)

`ExactInstitution.ofClassic` and `toClassic` are inverse at `D = Prop`.
`toTyped` embeds a fixed value type as a singleton family and `atType`
recovers it. For a typed family, `propInstitution` uses an equivalence
`Denote t ≃ Prop` to read the designated propositional fiber. This also
accommodates a lifted `Prop` in a higher universe.
A predicate observation can identify different values. The checked example
with the predicate `0 ≤ ·` gives values 1 and 0 the same satisfaction result.
Recovering a general value from one observation would require additional data.
[Definitions](../../Silmaril/Logic/Institution/Generalized/Defs.lean) ·
[Examples](../../Silmaril/Logic/Institution/Generalized/Examples.lean)

## Order-lax evaluation and upper cuts

`LaxInstitution` requires a preorder. Its orientation is
`eval S (reduct σ M) φ ≤ eval T M (Sen.map σ φ)`. For composable signature
maps both functors compute the composite and `le_eval_map_comp` chains the
inequalities. The upper cut at `k` passes from reduct to target by
`cut_preserved`. It is an ordinary institution with the given functors and
cut exactly when `ReflectsCut k` holds. In a partial order, all upper cuts
reflect iff the evaluation law is equality. The example where evaluation is
the signature number has an exact cut at zero. At threshold one, the map
from zero to one gives a passing target and a failing reduct.
[Cut laws](../../Silmaril/Logic/Institution/Generalized/Thms.lean)

## Three and four values

A three-valued evaluator can return `some true`, `some false`, or `none`.
`Evidence.ofThree` embeds these into two independent proposition flags, with
`none` setting neither. Four-valued evaluators can also set both flags.
`Evidence` orders values by implication in each flag, the information order.
A producer chooses the meaning of each flag.

`Evidence.ofCompletions C P` uses universal satisfaction and universal
refutation, expressed as `∀ x ∈ C, P x` and `∀ x ∈ C, ¬ P x`. A mixed family has neither
flag, and an empty family has both by vacuity. When `C` is inhabited, the two
flags cannot both hold. Taking a subset can only add flags in the information
order. A reduct preserving `P` yields the same flags as its image of `C`.
A covering reduct therefore gives equality with the full source family.
`Evaluation.entailmentEvidence` takes `C` to be the models of the observed
premises. Its positive flag is ordinary entailment after observation. The
negative flag requires every such model to refute the observed conclusion.
A single countermodel suffices to disprove ordinary entailment, even when
other models still satisfy the conclusion. The completion flags encode a
different question from whether witnesses for either answer exist.
[Completion laws](../../Silmaril/Logic/Institution/Generalized/Thms.lean)

## SAT and PER instances

| Evaluation at one model | Signature change | Where to start |
| --- | --- | --- |
| SAT Boolean, strong Kleene and FDE values | `totalExact`, `kleeneExact` and `evidenceExact` return `Bool`, `K3` and `FDE`. They commute with every atom map. Their truth, support and refutation observations agree with the ordinary SAT rooms. | [SAT study](generalized-institutions-sat.md) · [SAT bridges](../../Silmaril/Logic/SAT/Institution/Generalized/Thms.lean) |
| SAT supervaluation over total extensions of a partial assignment | `completionLax` uses the same universal flags as `Evidence.ofCompletions`. Reducts may lose coverage when atoms are identified. Injections cover every source completion. | [`completionLax_eval_eq_ofCompletions` and `completionLax_eval_map_of_coverage`](../../Silmaril/Logic/SAT/Institution/Generalized/Thms.lean) |
| PER CNF over completions between relation bounds | `intervalLax` pulls back both bounds. The guarded `intervalLaxWith` profile requires admissibility to survive pullback. Coverage gives equality, and unrestricted intervals have coverage on injective term maps. | [PER study](per-constraints.md#intervals-and-admissible-completions) · [PER bridges](../../Silmaril/Calculi/PERConstraints/Interval/Institution/Thms.lean) |

- **Local values and consequence.** Each evaluator takes one valuation or interval and one CNF. Consequence selects models by their observations of the premises and then quantifies over those models. A lattice of local values alone leaves that selection and aggregation open. A threshold gives a predicate for ordinary consequence. A value-valued alternative can take the meet of the conclusion values over a chosen premise-model class when the relevant meet exists, for example in a complete lattice.
- **Compositional values and completions.** Strong Kleene combines local truth values. An unknown atom leaves `p ∨ ¬p` unknown compositionally, while every total completion satisfies it. FDE combines independent support and refutation. Its truth order increases support and decreases refutation. The shared information order increases both flags, which is the order used by both completion instances. [SAT identification example](../../Silmaril/Logic/SAT/Institution/Examples.lean)
- **Coverage, empty and mixed families.** Pulling back a target family produces a subset of the source family. Both universal flags can increase when quantifying over this smaller set. Coverage identifies the two families and gives equality. A mixed family gives neither flag. An empty family gives both by vacuity, while FDE can assign both as evidence at an individual model. SAT partial valuations always have total completions. PER admissibility can give an empty family. [PER examples](../../Silmaril/Calculi/PERConstraints/Interval/Examples/Thms.lean)
- **PER bounds and solutions.** Endpoints bound the permitted PERs. They give endpoint tests for monotone EQ-only queries when admissible, and the least or greatest admissible solution exists only under additional conditions. CNF disjunction and DISTINCT can leave incomparable minimal or maximal solutions. On a singleton unrestricted interval, `intervalLax_eval_exact` recovers ordinary satisfaction and its negation. [Interval laws](../../Silmaril/Calculi/PERConstraints/Interval/Thms.lean)

Build the interface, instances and examples with

```sh
make check CHECK_TARGETS='+Silmaril.Logic.Institution.Generalized.Examples +Silmaril.Logic.SAT.Institution.Generalized.Thms +Silmaril.Logic.SAT.Institution.Examples +Silmaril.Calculi.PERConstraints.Interval.Institution.Thms +Silmaril.Calculi.PERConstraints.Interval.Examples.Thms'
```

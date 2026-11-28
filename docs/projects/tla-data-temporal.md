# Named TLA+ temporal denotations over mathematical data

Import `Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms`. Resolve the
parsed module registry with `Resolution.resolveWith .levelSyntax`, then
select a nullary source definition by its resolved `BindingId` with
`Temporal.lowerFormula registry externalLevels signature maxDepth id`.
`lowerState` and `lowerAction` select a state predicate or a two-endpoint
relation. Each entry checks levels on the supplied registry before lowering.
A constant or state predicate is also a formula. A raw action is rejected
in a formula position. `lowerStatement` selects an anonymous, proof-free
theorem expression at its resolved module-unit site. Each selector uses
the core data fragment by default and also accepts `.collections` with the
matching collection interpretation.
[Entry points](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Defs.lean) ·
[Level checking](tla-expression-levels.md)

Supply an `Interpretation` with DataElab operations, Boolean policy and
admitted primitive interpretations. The pure-set and tagged adapters both
fit this interface. For example, use
`⟨policy.operations, policy.booleans, policy.external table⟩` with the tagged
numeric signature. Then use `checked.toFormula interpretation rigid` for a
standalone Simple TLA formula. The rigid valuation is fixed throughout
satisfaction. Each state is a total map from flexible declaration IDs to
values in the chosen carrier. A primed data operand uses the target map
and the same rigid valuation.
[Denotations](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Semantics.lean) ·
[DataElab adapters](tla-data-elab.md) · [Standalone semantics](tla.md#typed-simple-tla)

| Form | Lowering |
| --- | --- |
| State and step predicates | DataElab expressions in the selected fragment, with prime in step positions. Negation, the four binary Boolean operators, and junction lists compose predicates, including modal predicates, using the data Boolean policy. |
| Observations | A DataElab state expression or an inline flat tuple of such expressions. The evaluator compares their values position by position at the two endpoints. It rejects a retained prime even when a primitive level signature masks that operand's contribution. |
| `UNCHANGED e`, `[A]_e`, `<<A>>_e` | Observation equality, disjunction with equality, and conjunction with inequality, respectively. A square step can change coordinates outside its observation. |
| `ENABLED A` | Exists a successor flexible valuation satisfying the action at the current state. The witness ranges over the whole carrier at each coordinate. It is independent of any next state in a behavior. |
| Temporal Boolean composition | Negation, conjunction, disjunction, implication, equivalence and junction lists. State children contribute their truth at the current instant. |
| `[]F`, `<>F`, `F ~> G` | Standalone always, eventually and leads-to. The matching action forms are `[][A]_e` and `<><<A>>_e`. |
| Rigid `\A` and `\E` | A temporal body may bind one or more ordinary names, with or without domains. Each witness ranges over the interpretation's value carrier and stays fixed throughout the body, including visits to later suffixes. |
| Flexible `\EE` and `\AA` | A comma-separated list of unbounded variable names. The body is a supported constant, state or temporal formula. Each existential takes a behavior with one additional state coordinate and hides that coordinate up to stuttering. The universal is the negated existential of the negated body. |
| `WF_e(A)` and `SF_e(A)` | Standalone weak and strong fairness of the changing steps of `A` under observation `e`. Fairness uses the same full successor space as ENABLED. |

Bounded temporal quantifiers check each domain as a core data expression at
state level or below, in the scope outside the entire binder list. They test
membership at the instant where the quantifier is evaluated. Universal bodies
are guarded by implication and existential bodies by conjunction. A domain
for a group of names supplies the same membership test for each name.
Resolved binder identities map to fresh witness slots. Nested data expansion
checks its scope against the active slots, and a primed operand reads the
same witnesses at the target endpoint. Level checking still enforces
operand rules and rechecks requirements after operator substitution.

## Flexible hiding

The resolver assigns each bound name its own lexical declaration ID. The
current state supplies an unprimed read, and the target state supplies a
primed read of the same coordinate. An observation can read any coordinate
in scope at its endpoint. ENABLED and fairness quantify over successors
in that same extended state space. A rigid variable in scope continues
to use one fixed value.

A flexible binder has temporal level. In its body each bound name has
state level. The level checker rejects a bare action operand, including
when a call supplies an action to a parameterized definition whose body
uses that parameter under a flexible binder. The parser accepts ordinary
unbounded identifiers. The resolver rejects duplicate binders, name
collisions in the active scope, and uses outside the binder body. A list
expands to nested single-name binders in source order. Flexible and rigid
binders may nest in either order wherever the body is admitted. Temporal
binder lifting through parameterized operators and LET, and flexible
quantifiers in the separate INSTANCE profile, are outside this slice.
[Specifying Systems §§8.8, 16.2.4 and 17.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=330) ·
[Pinned SANY binder syntax and scope](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Generator.java#L3927)

Both source hiding and standalone General TLA use `hide`. Each witness
must satisfy the whole operand on its own extended behavior. Dropping the
bound coordinate leaves a behavior stutter-equivalent to the input suffix.
A hidden change can occur while the projection repeats a visible state.
The product-state binder inherits the checked reduction law.
[Lamport, *The Temporal Logic of Actions*, equations (48)–(49)](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf#page=33) ·
[Canonical reduction theorem](../../Silmaril/Logic/Temporal/TLA/StutterReduction/Thms.lean) ·
[#3227](https://github.com/hiloopai/silmaril-lean/pull/3227)

The parsed `Delayed` example has a hidden Boolean that starts false.
A visible change is allowed only on a step where the hidden value moves
from true to false. Lean proves that an input with an immediate visible
change satisfies the hiding formula. Its witness first repeats the visible
state while setting the hidden value to true. Lean also rules out an
extension with exactly the input projection and rules out satisfaction on
a permanently unchanged visible behavior. Further parsed checks compare
a changing flexible witness to its rigid counterpart and exercise
universal, nested and mixed binders.
[Checked examples](../../tests/semantics/tla-temporal-source/Flexible.lean)

The standalone semantics proves whole-state stutter invariance for every
lowered formula. Source raw actions remain relations on two endpoints. Data
predicates use the fixed interpretation's truth test and malformed-Boolean
policy. Once composition reaches temporal level, its Boolean connectives
combine propositions about behaviors.
[Action and stuttering laws](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Thms.lean) ·
[Lamport, *Specifying Systems*, §16.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=330)

The temporal syntax expands nullary module operators at their original
resolved sites, including operators reached through EXTENDS. DataElab
leaves retain their ordinary first-order calls, LET expansion and data
binders. Lifting modal forms through parameterized calls, LET, value
constructors or IF is a further slice. Below temporal level, quantifiers
use the selected data fragment. Tuple patterns in temporal binders are outside
this source profile. Other boundaries include INSTANCE replay, temporal
primitives, action composition, guarantees and checking source proofs.
This is a mathematical semantics with a source admission check.
There is no general source adequacy or finite model-checking claim.

Value-level tuple constructors require the collection fragment. The pinned
BoundedQueue fixture uses that fragment to check its source assumption,
specification and temporal safety statement.
[BoundedQueue source contract](tla-sequences.md#library-identity-and-source-check)

## Intact LiveHourClock

The fixture uses the pinned parser revision and checks all four downloaded
source hashes before parsing.

| Source at `bc1b506bdcad80bb518bf3776a9161c34ff0fc4c` | SHA-256 |
| --- | --- |
| [LiveHourClock.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/LiveHourClock.tla) | `d363d32fa6a20f7aa6b2590ba95e2a4ffd7849107423ae3bbc5ac96d10693064` |
| [HourClock.tla and Naturals.tla](tla-source-acceptance.md#inputs-and-library-contract) | Existing source acceptance pins |
| [TLCExt.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLCExt.tla) | `6c3e7e54cf1b8a4d2d1c7a5fd088f06452edce68ec28d8be99392cc0037a5399` |

The registry parses the intact LiveHourClock and HourClock modules and
attests the two needed Naturals infix declarations from the parsed standard
module. TLC contributes an empty signature to this fixture. The parsed
TLCExt module attests a nullary `CounterExample` used to resolve and
level-check the original postcondition. The fixture does not admit a TLC
counterexample interpretation.

The fixture checks the original anonymous statement's shape. Lean proves
that the lowered `LSpec` entails the conjunction of `AlwaysTick`,
`AllTimes` and `TypeInvariance` over arbitrary tagged behaviors for every
fixed tagged adapter policy. The proof preserves the range 1 through 12
across updates and idle steps. It uses weak fairness to obtain a changing
tick after every starting time. On a suffix that avoids a given hour, each
tick would decrease the remaining distance around the clock and idle steps
would preserve it. Thus every hour recurs. `ClockSettles` lowers as a rigid
existential, and Lean proves that `LSpec` rules it out. Selecting
`PostCondition` reports the missing `CounterExample` interpretation.
[Fixture proof and admission checks](../../tests/semantics/tla-temporal-source/LiveHourClock.lean)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Examples
python3 -I tests/semantics/tla-temporal-source/check.py
make tla-import-check
```

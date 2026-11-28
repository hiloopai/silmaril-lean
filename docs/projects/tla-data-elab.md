# TLA+ data expression lowering

Import `Silmaril.Logic.Temporal.TLA.DataElab.Defs`. Parse with
`Surface.Parser.parseModule`, resolve a registry with `Resolution.resolve`,
then call `DataElab.lowerDefinition registry signature maxDepth id` on a
resolved, nullary source operator. Resolve the operator's declaration ID
through the root's final scope when selecting an entry by name. Use
`checked.eval ops booleans external valuation` for its value in one
state. Use `booleans.holds` on that value when a caller needs a proposition.

[Lowering API](../../Silmaril/Logic/Temporal/TLA/DataElab/Defs.lean) ·
[Denotation](../../Silmaril/Logic/Temporal/TLA/DataElab/Semantics.lean) ·
[Module resolution](tla-module-resolution.md) · [Mathematical data model](tla-data.md)

## Scope and substitution

- The lowering reads each use from the resolver at its original module and
  path. An imported operator expands in its home module, where it can still
  refer to LOCAL definitions. LET definitions capture the incoming lexical
  bindings, including earlier LET definitions and enclosing formals.
- Expression actuals substitute expanded terms. Named and symbolic operator
  actuals retain their resolved identity or lexical closure. A lambda keeps
  its own body site and captures the actual's lexical context. Operator
  formals can be forwarded through another invocation.
- Rigid constants and flexible variables have separate assignments keyed by
  declaration identity. A caller evaluating across states fixes the rigid
  assignment and varies the flexible one. Each expansion of a binder gets a
  fresh witness slot. The result carries a check that witnesses are scoped and
  that each external node has the admitted arity.
- The depth bound starts at the selected body and counts descent through the
  source, including expansion into called bodies. `expansionLimit` gives the
  next unvisited site. The resolver checks names and arities even in unused
  bodies. Lowering checks the requested expression and the bodies it expands,
  including expression actuals even when unused. An uncalled LET operator
  or unapplied operator actual does not require a data denotation.

## Checked source and target evaluation

Import `Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Thms` for the endpoint
entry points and equations. Call
`Endpoints.lowerState registry externalLevels signature maxDepth id` for a
constant- or state-level definition. Call `Endpoints.lowerAction` with the
same arguments for an action-level definition. Both run `Levels.check` on the
registry they lower and select a declared nullary source operator by
`BindingId`. Level failures retain their use and requirement-origin sites.
A selection at the wrong level reports the selected body's site and level.
Level checking covers the reachable registry, including unsupported
operator-valued formals even when they are unused by the selected operator.
The original `lowerDefinition` entry continues to reject prime.

Evaluate a checked action with
`action.eval ops booleans external ⟨rigid, source, target⟩`. The flexible maps
supply the source and target values. Prime uses the target map for the entire
expanded operand, including actual terms substituted through LET and calls.
The rigid map and any surrounding witnesses stay fixed. Binders inside the
operand evaluate their bounds and bodies at the target. `Term.eval_prime`
states the shift equation, and `CheckedAction.eval_diagonal` gives evaluation
with a common flexible map at both endpoints.

Lowering rejects a retained prime inside another prime after expansion. State
selection also rejects a retained prime, for example in an evaluated external
argument whose level signature gives that slot zero weight. An action argument
discarded by an expanded source operator leaves no such read. The checked
core subset excludes temporal values, action brackets, ENABLED, UNCHANGED,
INSTANCE, and proof interpretation.
[Endpoint API](../../Silmaril/Logic/Temporal/TLA/DataElab/Endpoints/Defs.lean) ·
[Endpoint laws](../../Silmaril/Logic/Temporal/TLA/DataElab/Endpoints/Thms.lean) ·
[Level checking](tla-expression-levels.md) ·
[Lamport, *Specifying Systems*, §§16.2 and 17.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)

## Values and admitted syntax

- `DataOperations` supplies a `Nat → V` interpretation of natural literals,
  membership, enumeration, separation, images, and a fixed
  `Data.ChoicePolicy`. `DataOperations.ofModel model numeral` inherits the
  pure-set operations and their laws on the entire carrier. The caller
  supplies its numeral meaning. The evaluator requires no set extensionality.
  Set images bind one identifier. Rigid quantifiers support multiple plain
  names and groups. Bounded domains are lowered in the incoming scope.
  Bounded quantifiers and bounded CHOOSE restrict witnesses
  through the supplied membership operation. Equality is Lean equality on
  the common carrier. [Pure-set model](tla-data.md)
- `Booleans` provides TRUE and FALSE, a predicate interpretation with laws for
  those two values, and a policy for invalid operands. Equality, inequality,
  membership, nonmembership, and rigid quantification return the Boolean
  values. `BOOLEAN` enumerates the two Boolean values. IF and logical operators
  have their usual behavior on Boolean guards and operands. Absorbing values
  such as FALSE in conjunction also determine the result with a non-Boolean
  operand. The `invalid` policy supplies the result in the remaining cases.
  A predicate position in a binder uses the supplied `holds`.
  [Lamport, §§16.1.3–16.1.4](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=314)
- `ExternalSignature` lists admitted declaration IDs and expression arities.
  A used signature-only operator or positive-arity CONSTANT operator must
  match both the resolved signature and the admission table. A nullary
  CONSTANT uses the rigid valuation unless its ID has an explicit admission.
  Source definitions always expand from their bodies. At evaluation,
  `ExternalInterpretation` supplies a `Primitive` for each admitted ID,
  with a Lean implementation and a proof of the caller's stated contract
  for argument lists of that arity. A caller may parameterize a result over
  that contract explicitly. The API assigns no standard-module semantics
  by name.

The core fragment excludes decimal and string literals, tuples and tuple
binders, multi-binder images and CASE. The original entry point produces a
single-state data denotation. Endpoint selection adds prime in the checked
fragment. Level checking can classify a proof-free theorem statement without
treating it as a selectable definition or proof.

## State-level collection expressions

Import `Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged` and call
`Collections.lowerState registry externalLevels signature maxDepth id`.
Use the checked registry of the original module and select the nullary
definition by its resolved ID. Evaluate the result with
`checked.eval (policy.collectionOperations invalid) policy.booleans external valuation`.
The collection fragment takes a `CollectionOperations` adapter. The pure-set,
scalar and `Endpoints` entry points use the core fragment.

- `[x \in S |-> e]` forms a graph with exactly the domain `S`. The body
  receives the graph key in a fresh slot. The unary expansion retains the
  constructor site and the resolved binder ID. The grouped forms are below.
- `[a |-> e, b |-> f]` forms a graph with exactly the listed string keys.
  `[S -> T]` contains the graphs with domain `S` and all outputs in `T`.
  `[a : S, b : T]` contains the graphs with exactly the listed keys and
  each field value in its own bound. Field expressions use their original
  indexed sites. A repeated label is rejected at its second occurrence.
- The tagged adapter uses a fixed `CollectionPolicy` for an unrecognized
  function bound, either unrecognized function-set operand, or a malformed
  record schema. The policy receives the original operands and the record-set
  error identifies the first non-set field in source order. No graph or set
  is assembled from a partial schema.

`Collections.lowerAction` also lowers `UNCHANGED e` to equality of the
primed and current values of `e`. It uses the same expanded-operand
checks as explicit prime, including the lexical `@` restriction.
The pinned ACP_SB fixture checks the `Init` and `TypeInv` graph schemas
and proves `TypeInv` preservation across every `progN` transition.
[ACP_SB fixture](tla-acp-sb-source-acceptance.md) ·
[Collection entry point](../../Silmaril/Logic/Temporal/TLA/DataElab/Collections/Defs.lean) ·
[Tagged adapter](../../Silmaril/Logic/Temporal/TLA/DataElab/Collections/Tagged.lean)

## Grouped and tuple binders

All bounds in one construct are evaluated in the incoming scope. Bound names
are visible together in the body. In `x, y \in S, z \in T`, `x` and `y`
vary independently in `S`, and `z` varies in `T`.

- Bounded rigid quantifiers and set images accept multiple groups and mixtures
  of plain names and tuple patterns. Set filters and bounded or unbounded
  `CHOOSE` accept a single tuple pattern. Quantifiers, filters and `CHOOSE`
  match only values that are tuples of exactly the pattern's length.
  A tuple `CHOOSE` without a witness returns the model's `CHOOSE z : FALSE`,
  which can be any value.
- `[x, y \in S, z \in T |-> e]` has flat triple keys. In
  `[<<x, y>> \in S, z \in T |-> e]` the key is a pair whose first
  component is the original member of `S`. A single tuple group uses members
  of its bound directly as keys. For both functions and images, a set bound
  can contain a nonmatching member. The reference translation keeps that
  member in the domain and binds the individual names to projections of
  `CHOOSE z : FALSE`, using the adapter's ordinary graph application policy.
- The tagged adapter builds flat products from one selection per factor.
  The product membership and exact tuple decoding laws are checked in Lean.
  Products used by functions and images with multiple arguments report
  unrecognized set operands through `.binderBounds`, with the original
  bounds in written order once per group. A single group with one pattern
  uses the original function or image policy.

This entry supports anonymous function constructors and data-level selection.
Explicit source `\X`, named function definitions (including recursive
definitions), and temporal binder lowering remain outside this entry.
[Reference §§16.1.1–2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=311) ·
[Reference §§16.1.6–9](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=317) ·
[Tagged binder laws](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Collections/Binders/Thms.lean)

### WriteThroughCache corpus gate

`python3 -I tests/semantics/tla-collection-binders/check.py` downloads and
verifies the existing parser corpus pin, parses the full module, and selects
the original `Coherence` operator. It resolves and lowers that operator in a
standalone fixture with rigid inputs `Proc`, `Adr`, `NoVal` and flexible
`cache`. The gate checks the shared `Proc` bound, separate `Adr` bound,
and the binding of all four `cache` reads. It also instances that projection
from a parsed host, checking the replacement bounds, the graph supplied by
WITH at all four reads, and the host bindings. The Lean examples independently
check the mathematical denotations of in-memory source cases.

The whole-module check without a dependency registry stops at the first
`EXTENDS` edge, `Naturals`. It requires the imported modules and the
`InternalMemory` and `Memory` instance dependencies. Lowering `vmem`
requires recursive LET function support, and checking other collection
clauses needs sequence primitives and additional set operators.
[Pinned module](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/CachingMemory/WriteThroughCache.tla) ·
[Corpus gate](../../tests/semantics/tla-collection-binders/WriteThroughCache.lean) ·
[Parser hashes](../../tests/semantics/tla-parser/check.py)

## Graph access and ordered EXCEPT

- `f[k]` applies a function to one key. `f[a, b]` uses the single tuple key
  `<<a, b>>`. Tuple literals use `Value.tuple`, whose checked graph has integer
  keys `1..n`, indexed lookup and injectivity. `r.field` applies `r` to
  `Value.string "field"`, the same encoding used for source string literals
  and record constructor labels. `DOMAIN f` gives the set of graph keys.
  [Tagged graph and tuple laws](tla-functions.md)
- `[f EXCEPT !.field[k] = e, ...]` uses `Value.updateClauses` in written
  order. Each clause evaluates its bracket keys in the enclosing valuation
  and lexical scope. Dot components use string keys. At each clause, `@` in
  the RHS is the leaf reached from the result of the preceding clauses along
  that clause's path. In a nested update, its base and selectors can use the
  enclosing `@`. Its RHS binds the new one by resolved clause identity.
  [Mathematical path and clause laws](tla-except.md)
- `policy.collectionOperations invalid` uses `policy.numeric` as the fixed
  tagged `Unspecified` policy for graph operations by default. A caller can
  pass an explicit `unspecified` policy and fix it across valuations.
  `DOMAIN` on a non-function calls `.domain` with the operand. Application
  on a non-function or at a missing key calls `.apply` with the root and
  key. EXCEPT preserves the root when a path through recognized functions
  encounters a missing key. At a non-function step it composes `.apply` and
  `.update` as specified by the tagged path API. These are value policies
  in the mathematical adapter. [Tagged graph policies](tla-except.md#clause-and-path-semantics)

`Collections.lowerAction` checks levels on the same registry and selects a
closed action-level definition. Evaluate it with
`action.eval (policy.collectionOperations invalid) policy.booleans external ⟨rigid, source, target⟩`.
Prime on a whole operand shifts all flexible reads within it, including graph
operands, selectors and an EXCEPT whose `@` is bound inside that operand.
Explicit primes in a selector or RHS shift only their operands. A prime
whose expanded operand reads `@` from an enclosing EXCEPT reports
`primeCrossesOldValue` at the prime site, including through a substituted
actual. Retained nested primes also report a lowering diagnostic.
[Collection action API](../../Silmaril/Logic/Temporal/TLA/DataElab/Collections/Defs.lean)

For checked first-order module calls, use the collection selectors in
`DataElab.Instances`. Source limits include explicit Cartesian product syntax,
`STRING`, decimal literals, recursion, and temporal and proof forms.
The resolver diagnoses an `@` outside an active RHS. The parser and resolver
reject malformed empty index and update forms before lowering.
[Collection INSTANCE replay](tla-instance-denotation.md)

## Tagged interpretation

Import `Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms`. Fix one
`DataElab.Tagged.Policy` across valuations and use `policy.operations` and
`policy.booleans` when evaluating. Its numeral slot maps a natural literal to
`Value.integer (Int.ofNat n)`. Predicate truth is `Value.isTrue`. The core
Boolean rules determine the result for Boolean inputs and absorbing values.
The configured `invalidBoolean` supplies the other results.
[Tagged evaluator API](../../Silmaril/Logic/Temporal/TLA/DataElab/Tagged/Defs.lean)

`Policy.mem_enum` gives the enumeration law. `Policy.mem_sep_set`,
`Policy.mem_image_set`, and `Policy.set_eq_iff` give characteristic laws on
recognized set values. An unrecognized bound has no members at the tagged
value level. A bounded existential is false, a bounded universal is vacuous,
and bounded CHOOSE uses the no-witness policy in that case. Separation and
image instead return `invalidSet` for their operation and bound.
[Adapter laws](../../Silmaril/Logic/Temporal/TLA/DataElab/Tagged/Thms.lean) ·
[Tagged value model](tla-tagged-values.md)

Supply a computable table `BindingId → Option Tagged.NumericPrimitive` mapping
the attested declaration IDs to `.interval`, `.add`, `.modulo`, `.le`,
`.lt`, `.naturals` or `.integers`. Pass `Tagged.numericSignature table` to
lowering and `policy.external table` to evaluation. The binary primitive
contracts state results on integer inputs. The modulo equation requires a
positive divisor. All the operations use the same `policy.numeric`, including
the underlying arithmetic behavior on inputs outside the integer contracts.
The two nullary primitives return the tagged natural and integer sets.
`Policy.mem_naturals` and `Policy.mem_integers` give their exact membership
laws. [Scalar laws](tla-tagged-values.md#scalar-handoff)

The HourClock registry can attest the required Naturals declarations as a
signature entry. Pinned Naturals has dummy source bodies for arithmetic, so
parsing it as a source module selects those bodies. Callers can use the same
signature registry for level checking and lowering. With `Resolution.resolveWith .levelSyntax`,
the endpoint entry points can select the initial and next-state definitions
from a registry that also contains its temporal specification and proof-free
theorem statement. [Level checking](tla-expression-levels.md)

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Examples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Examples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples
scripts/check-layout.sh
```

The fixture runs the existing parser and resolver, then lowers selected
definitions from two in-memory source modules and one signature module. The
test elaborator quotes the resulting terms as ordinary Lean data. The kernel
checks the witness-scope and external-admission proofs and equations for the
resulting denotations over the pure-set adapter and arbitrary valuations. A
separate equation checks that image uses an interpretation's supplied policy
on an unrecognized bound. The fixture exercises home-module lookup,
forwarding and LET capture, repeated expansion of the same binder, set image
and filtering, rigid quantification, CHOOSE, and a proved external
implementation. Guards check prime, unsupported tuples, depth
exhaustion, wrong arity, and a same-named external from a different module ID.
The endpoint fixture checks double-prime provenance, level selection, and
first-order admission. Its kernel-checked equations cover a compound formal
primed through LET, source and target reads, and witness scope on both sides
of a prime. The parser, resolver, and level checker run during elaboration.
A general source adequacy theorem is outside the fixture's scope.

[In-memory regression](../../Silmaril/Logic/Temporal/TLA/DataElab/Examples.lean)

The tagged regression checks the resolved and lowered shapes for a clock
interval test and update value, an admitted nullary constant, and a parsed
operator whose ID is also in the external table. Lean checks the interval and
arithmetic equations for the corresponding terms, plus the policies on
unrecognized set bounds and a zero modulus divisor.
[Tagged regressions](../../Silmaril/Logic/Temporal/TLA/DataElab/Tagged/Examples.lean)

The collection regressions stage the terms produced by parsing, resolution,
level checking and lowering. The kernel checks the scopes and equations for
the constructed graphs, exact record and function-set recognition, graph
access, tuple-key update, nested lexical scope, and repeated updates on found
and missing paths. The checked action equations distinguish whole-operand
prime from primes in selectors and RHSs. Equations cover malformed value
operands through the fixed policies. Guards cover duplicate labels, malformed
syntax, an unbound `@`, a prime crossing `@` after expansion, and unsupported
forms with their original operand sites. Binder examples check flat and nested
tuple keys, empty products, grouped images, tuple arity, CHOOSE with and without
a witness, and the wrong-shape projection rule for functions and images. Guards
check cross-group scope, duplicate binder names, and a primed bound's level.
[Collection regressions](../../Silmaril/Logic/Temporal/TLA/DataElab/Collections/Examples.lean)

# Free undefined behaviour in Isotope refinement

In the ordered institution, the inequation `a ⊑ b` is interpreted as
`⟦a⟧ ≤ ⟦b⟧`. In the observational institution it is inclusion of the
outcomes of `a` in those of `b`. UB, which permits every outcome, is on the
right of `t ⊑ ub`. A compiler contract can accordingly place the target on
the left and the source on the right. See [ordered satisfaction][ordered],
[observational satisfaction][obs], and [the compiler convention][compiler].

## Construction

The native term and region grammars have empty-type elimination. Literal UB
is introduced here through the extended presentation and the unit-fed
instruction spelling. [LetCase typing][case-typing] [LambdaSSA syntax][ssa-syntax]
[LambdaRTL syntax][rtl]

- `UB.dialectMonad e` acts on `InstrSig τ ε` for fixed types, effects, and UB
  effect `e`. A primitive has one typed input and one result. The new symbol
  at result type `A` has profile `unit → A` and effect `e`. A morphism
  extending a relabelling can choose any symbol with precisely that profile.
  The unbundled `SignatureMap` also changes types and effects. A corresponding
  lift needs to preserve unit and transport the chosen effect as well as the
  ordinary typing and effect premises. [Primitive extension][primitive]
  [Instruction morphisms][instr] [Varying signatures][sigmap]
- `UB.signatureMonad` acts on the contextual `PSig` used by the ordered
  institution. It adds a literal arity-zero operation per judgment sort.
  For LetCase and LetIter a sort includes a bound context and a result type,
  with the free-variable context fixed by the presentation. The independent
  explicit constructor `Expr.ub` has the unique fold into any algebra for
  the extended signature. [Explicit syntax][syntax] [Signature monad][signature]
- `UB.Specification.monad` acts on the institution's specifications. A map
  must send axioms to consequences. The extension transports the old axioms
  and adds `t ⊑ ub` for **every** term at its sort, including expressions
  under binders. `homEquiv` states the universal property for targets with
  designated nullaries above every denotable term. Restriction along the unit
  and extension using the designated symbols are inverse. In each monad the
  unit includes the old operations and multiplication identifies the inner
  and outer fresh symbols. In the ordered case the two symbols may still be
  distinguished before applying multiplication. [Specifications][spec]
  [Institutional consequence][institution]
- Monotone algebra operations place the inequalities under well-sorted
  constructors. The whole expression in any such context lies below UB at
  the result sort. An equation saying a context around UB evaluates to UB
  would need separate absorption laws. In arbitrary validating algebras the
  top rule bounds the image of the syntax fold. In the initial ordered
  quotient every element is represented by syntax, and `initial_le_ub`
  bounds the entire carrier at every sort. The ground inequations alone
  cannot constrain elements outside that image. `model_without_top` gives
  a two-point validating algebra whose carrier has no greatest element.
  [Ordered algebra and quotient][models]
  [Initial model][spec]

## Ordered LetCase bridge

`refinement_iff` preserves and reflects refinement between literal-unit
endpoints. `quotientIso` identifies the explicit quotient by mutual
refinement with the quotient of canonical native terms by the inherited
native order. The native presentation uses the full well-typed extended
dialect as syntax. Its generators are the relabelled original sentences and
`t ⊑ op (ub A) unit` for every native `t : A`. The proof uses monotone
constructor operations, retains the chosen primitive effect, and imposes no
purity requirement on it. Canonical elaboration always supplies literal unit,
so it never erases an effectful operand. Readback on arbitrary operands is
used internally to compare these generated axioms. [Bridge][case-refinement]

With the original sentences taken from `caseTheory`, `preserves_native`
also gives a derivation in LetCase's full native refinement calculus with
the transported primitive rules and the top rule. Reflection into the
original free extension fails for that stronger target. Native case beta
drops an unselected branch containing UB, even with effectful UB and
canonical endpoints. The Boolean occurrence model validates the interpreted
axioms and distinguishes the two terms. Its `true` is greatest and
`encode_eval` gives agreement with the induced explicit interpretation.
The flag includes both branches and describes UB occurrence in syntax.
[Model][case-model] [Checked counterexample][case-regression]

## Ordered LetIter bridge

LetIter's exact typing judgments have free and bound contexts and a result
type. They carry no usage quantities or effect bound. The literal-unit
round trip holds at each such sort, including the iteration body at
`β.snoc A` with result `B ⊕ A`. The chosen UB effect is preserved on
the native instruction. Readback is inverse on canonical terms, where
each fresh instruction has a literal unit operand. `refinement_iff` and
`quotientIso` compare the explicit and interpreted orders on those terms.
The latter is generated over the full native syntax by the relabelled
old sentences and a UB upper bound for each typed native term.
[Typed round trip][iter-ub] [Ordered bridge][iter-ub-refinement]

With inherited sentences from `iterTheory`, `preserves_native` embeds
the explicit order into the full native refinement rules. The checked
regression separates native fixpoint unrolling from the interpreted
axioms. Its two-point model ignores the iteration body when reading a
loop and reads the scrutinee when reading a case. The unrolling moves
the UB body into a scrutinee, so the native equation can give a
comparison the matched axioms do not entail. This model only witnesses
the algebraic separation. [Checked fixpoint example][iter-ub-regression]

Quantitative LetIter uses a separate typing judgment. At bound `b`,
`op (ub A) unit` typechecks exactly when `Γ.Discardable` and
`ubEffect ≤ b`. In the iteration rule, the ambient context `Γl`
already has `Γl.linearity = ⊤`. The body context `Γl.snoc A` is
discardable exactly when the incoming state's type admits discarding
(`Quantity.affine ≤ quantity A`). A linear state blocks literal-unit
UB in that body even at the top effect bound. The stable rewrite
presentation in `topRules` keeps formed endpoints under native
weakening and pure substitution. The comparison to literal UB holds
exactly for formed left endpoints in discardable contexts.
`typeIterLiteralBody` adds the ordinary iteration guard `iterable b`,
and `iter_body_refines_literal` uses native iteration congruence at the
original context split. [Quantitative typing and refinement][iter-ub-quant]

## LambdaSSA's empty-label boundary

In the exact LambdaSSA typing judgment, a region with no external labels
must contain a local block. `not_noLocalBlocks` excludes even regions that
wrap their bodies in zero-block CFGs. A unit-state CFG that branches to
itself gives a typed region at every value and label context. A unit-fed
instruction can be sequenced before that CFG, with the local backedge
ignoring its result. Exact LambdaSSA typing here has no quantitative
usage or effect-bound premise. [Typing][ssa-typing] [Witnesses][ssa-ub-defs]

`Refines` compares sets of return, fault and divergence observations by
inclusion in every model of the observational institution. In the
`faultModel` every primitive faults, with no successful primitive
transitions and no primitive divergence. The unit-fed prefix faults
and the bare CFG diverges. A simultaneous upper bound would need both
observations from the same initial state. Mutual induction through
nested CFGs and block traversal proves that fault and internal divergence
are exclusive when successful primitive steps are deterministic and a
faulting primitive call cannot also return. Thus `no_common_upper_bound`
and `no_greatest` hold for every exact typing interface of an alphabet
with a unit-taking operation. This includes the fresh `unit → A`
instruction in `UB.dialect P e`, for any effect label `e`. The obstruction
quantifies over all typed native regions, so it also bounds what can be
encoded using typed native substitution or feedback. [Observation order][ssa-observations]
[Obstruction][ssa-ub] [Dialect regression][ssa-ub-regression]

At a fixed model, an empty-label region has no finite return. Its
observations are contained in the set of all faults and divergences.
The unit-fed prefix attains that greatest set if its primitive can fault
from every initial state to every final state and can, at each initial state,
either diverge or return to the backedge. The regression instantiates this
with a model in which the instruction both faults and can diverge.
Greatest behaviour here is a law of that model. [Fixed-model result][ssa-ub]
[Model regression][ssa-ub-regression]

### Explicit region UB with substitution and feedback

The independent `Overlay.Region` embeds any exactly typed native region,
adds a UB region at every interface, and provides label substitution and
feedback. A continuation or block receives the exit payload in its own
value binder and retains the original captured context. Native regions may
contain arbitrary nested CFGs. [Overlay syntax][ssa-ub-overlay-defs]

For each observational model, bound environment and initial state, the
carrier is `WithTop (Set Outcome)`. An outcome carries a scoped exit and
payload, a fault state, or divergence. The refinement order is pointwise
subset on ordinary sets with a distinct greatest UB element. An ordinary
universal set stays ordinary. The projection back to native observations
recovers the original observations on every native region, and the embedding
preserves and reflects the original refinement preorder. [Conservativity][ssa-ub-overlay]

`lsubst_mono` proves directed congruence in the source and all continuations.
Sequencing propagates source faults and divergence and runs continuations
only on successful exits. UB in the source or a reached continuation lifts
the whole behaviour to greatest at that initial state. Substituting into UB
preserves UB even when the target has new labels. For all-native inputs,
`denote_native_lsubst` proves exact agreement with one typed dispatch CFG
whose blocks run the continuations, including faults, external divergence,
and internal divergence of the existing native regions. [Substitution laws][ssa-ub-overlay]

Using ordinary universal outcomes as UB would lose this absorption law.
An empty label interface has no successful exit, so ordinary sequencing
cannot turn even its universal set into a return at a target label.
The regression uses a native region that already has all empty-interface
outcomes in one model. Its ordinary projection equals the projection of
explicit UB at the source, yet their substituted projections differ at a
single-exit target. Thus ordinary outcome equality at a fixed model is
insufficient for a compositional interpretation with both native sequencing
and absorbing UB. The lifted order retains precisely the distinction used
in this counterexample. [Checked obstruction][ssa-ub-overlay-regression]

Feedback splits the outgoing interface as `R ++ L`. An ordinary return to
`R` invokes the corresponding local block with the returned payload and
machine state. A return to `L` exits. Fresh top occurs exactly when a finite
path of ordinary internal returns reaches a component at fresh top. Below
top, finite paths collect external returns and faults, and divergence comes
from a finitely reached component divergence or an actual infinite
sequence of internal returns. `feedback_mono` proves directed congruence
in the entry and all blocks, including refinements that expose UB earlier.
The top and ordinary parts also satisfy one-step unfolding.
[Feedback laws][ssa-ub-feedback]

For native entry and blocks, `denote_native_feedback` agrees with the
repository's typed recursive CFG at every existing observational model.
The regression checks a block whose first visit takes a backedge and whose
second visit reaches UB, an immediate exit that bypasses a UB block, and a
native self-loop whose divergence is absent from finite closure.
[Native agreement][ssa-ub-feedback] [Regressions][ssa-ub-feedback-regression]

Feedback uniformity compares two graphs with the same external interface.
The local theorem assumes that at each reachable source point, a
deterministic point map sends each source step to a target step and lifts
every step out of the image to a source successor with that exact image. The matched points must agree on
fresh UB and ordinary external returns, faults, and divergence. These
conditions are required only on reachable source points. They preserve and
reflect finite paths, reached UB, and actual infinite paths. The reverse
infinite proof lifts the selected target path one step at a time, choosing
a source successor at each step. The exact criterion for equality of
closed behaviours is agreement on whether UB is reachable and, below UB,
equality of the resulting ordinary outcome sets. [Uniformity][ssa-ub-uniformity]

A type-preserving label map keeps payloads and machine states and may merge
labels of the same type. `close_slide` proves the deterministic routing
instance of the Conway sliding law. Closing a body with routing on its
block inputs gives the same behaviour as closing it with routing on its
internal returns. Permutations give block relabeling invariance as a
corollary. The one-way counterexample preserves local marks and ordinary
outcomes on reached source points, yet a new target edge can expose UB or
enable infinite replay.
[Sliding and relabeling][ssa-ub-uniformity] [Checked counterexample][ssa-ub-uniformity-regression]

Two-level elimination views the same overlay semantics as a graph of
ordinary transfers, local UB and terminal observations. The graph's
one-shot closure agrees definitionally with `Feedback.close`. Closing
the inner group exposes each transfer to an outer point as a boundary
outcome, carrying the label, payload and machine state. The outer closure
consumes these boundary outcomes. `close_two_levels` proves equality
with the flat closure for the typed hidden interface `I ++ O`.
`close_partition` allows any partition of the invocations.

Finite paths split at outer visits. An outer step consists of zero or more
inner transfers and a final original edge into an outer point, so every
such step consumes at least one original edge. If a reachable inner UB
suppresses an otherwise available boundary transfer, the outer closure
already has a witness to UB. Below UB, the finite terminal comparisons
retain the original outcomes.

For a selected infinite flat path, either all visits after some index
are inner, or a later outer visit exists after every index. The proof
in the first case uses the finite prefix to reach the final inner replay.
In the second case `Nat.find` selects the least next outer visit, so the
intervals between selected visits are finite inner segments. In reverse,
an inner replay can be prefixed by the finite flattened outer path.
An infinite outer replay provides nonempty flat segments. Classical
choice selects a real successor at each original step, maintaining a
finite suffix to a segment boundary. The regressions exercise both kinds of
replay, a finite external outcome, and early UB in an inner segment.
Full Conway and Elgot laws remain open.
[Elimination theorem][ssa-ub-elimination] [Regressions][ssa-ub-elimination-regression]

### Descent through the native CFG entry quotient

`cfgDenotation` lifts the map `r ↦ denote (.native r)` through the
installed `Region.CfgQuotient` at each exact value and label interface.
`cfgEquiv_obs` covers empty CFG elimination, an outward entry branch,
and unfolding a local entry branch into its block. It uses the existing
observational congruences for lets, cases, and CFGs and preserves returns,
faults, and both sources of may-divergence in every observational model.
The descended map supports overlay substitution and recursive CFG assembly.
Semantic relabeling and two-level elimination apply to feedback over the
resulting quotient denotations. [Native quotient][ssa-cfg-quotient]
[Descent][ssa-ub-native-quotient]

The guarded `Paper.Hom` and the native `ContinuationHom` admit checked
counterexamples to the same representative contract. Paper's product η
identifies a split and rebuild with a direct return. A bound value of unit
at the product-typed input makes only the direct return succeed. Native
initiality identifies a return with an empty-typed elimination, which
the same model separates when it supplies unit at an empty-typed input.
Both witnesses have constructor-valued branch arguments and use no
primitive transitions. The observation model indexes bound values by scope
and imposes no payload shape. Shape-aware environments would exclude
these witnesses. The installed categorical soundness theorem for Paper
uses a coherent typed region denotation and its stated categorical
hypotheses. [Paper soundness][ssa-paper-soundness]
[Obstructions][ssa-ub-descent-obstruction]

The regressions check one UB-producing branch of a nondeterministic
producer, an outward CFG entry that bypasses blocks leading to UB after
substitution, and a local entry unfolding whose infinite replay remains
ordinary divergence. The outward example also checks semantic relabeling
and staged feedback on the native quotient inputs.
[Descent regressions][ssa-ub-descent-regression]

### Shape-respecting observations

Over the free type algebra `Ty κ`, the shaped model reuses the runtime
typing of the LambdaSSA resumption machine. The model assigns types to atoms
and requires every bound slot to have its declared type. Unit, pairs and
injections retain their runtime tags, and empty has no runtime inhabitant.
When a primitive succeeds on a source-typed argument, its payload must have
the target type. Fault and primitive-divergence relations have no reply
payload. The semantics uses the original observation relations and lifted
subset order. [Model][ssa-ub-shaped-model]

Finite evaluation preserves expression types and the payload type of each
native region exit, including through CFG blocks. In the overlay, reachable
ordinary returns carry the declared label type through substitution and
feedback. This uses finite path induction for feedback transfers. An
infinite path contributes divergence, and fresh UB is greatest in the
unchanged lifted order. [Preservation][ssa-ub-shaped-laws]

The installed variable product η step preserves the full lifted behaviour
at every shaped input and state. Native initiality's exact constructor-value
premise entails that the value context has no shaped model. The fixture
passes a primitive-produced pair through an internal CFG label, checks
product η on that payload, and exhibits a faulting empty-result primitive
that separates the equation when the constructor-value guard is dropped.
[Laws][ssa-ub-shaped-laws] [Fixture][ssa-ub-shaped-regression]

### Native continuation quotient in shaped models

`ContinuationHom` is the quotient of constructor-branch continuation
families by pointwise `SubstitutionEquiv`. At input label `i`, its shaped
denotation takes a model for the exact context `L.get i :: Γ` and uses the
native representative at the output interface `K`.
[Quotient][ssa-native-continuation] [Denotation][ssa-ub-shaped-continuation]

| Installed relation | Generators and closure used by the descent |
|---|---|
| `CfgEquiv` | `cfgZero`, `cfgBrExit`, `cfgBrLocal`, reflexivity, symmetry, transitivity, and congruence for let₁, let₂, case, and recursive CFG. These reuse the unrestricted native CFG observation proof. |
| `RewriteEquiv` | `entry` embeds `CfgEquiv`. `letBr` uses constructor-value substitution. `caseInl` and `caseInr` evaluate the same argument and select the same arm. The relation includes symmetry, transitivity, and the same four congruences. |
| `SubstitutionEquiv` | `base` embeds `RewriteEquiv`. `letValue` and `caseValue` use state-preserving constructor substitutions. `caseCfg` routes once into the selected arm. `cfgOutward` shifts every exit beyond the local blocks. `initial` requires a constructor value of empty type. The relation includes symmetry, transitivity, and the same four congruences. |

The shaped congruences check successful term replies before entering
let and case bodies. CFG entry and each successful backedge establish
the target label type. Finite execution and faults follow this invariant,
and coinduction carries it through infinite replay. Constructor-value
substitution preserves returns and final states, faults, and both
sources of divergence. The fixture reaches a rewritten block with either
tag from one nondeterministic primitive. One tag replays the backedge
and the other exits. The primitive can also fault.
[Regression][ssa-ub-shaped-continuation-regression]

### Guarded Paper collapse and simulation square

The exact `Paper.Eqv.collapsePost` generator preserves lifted observations
in shaped models. The theorem allows arbitrary typed outgoing
continuations, including effectful ones. It pushes the common literal
substitution through both CFG forms with the proper value and label lifts.
The operational proof then follows the native dispatch relation. A
two-label graph keeps both possible backedges before two-level elimination.
Its staged graph represents the nested CFG, while merging the labels
represents the flat CFG. Step transport in both directions retains the
payload and machine state. The native observations include successful
exits, faults, divergence inside a primitive or body, and infinite CFG
replay. The proof of the underlying duplicate-label observation law works
with arbitrary native primitive relations. [Collapse][ssa-ub-paper-collapse]
[Stateful regression][ssa-ub-paper-regression]

For `Paper.Eqv.uniform`, the installed premises guard the entry and source
body's branch arguments and give a constructor state map `a`. The target
body `q` is exactly typed and may have effects. The premise equates the
literal substitution of the lifted local map into the source body with
substitution of the lifted target body into `br 0 a`. The shaped lemmas
interpret the right-hand region as a single binding of `a` followed by
`q`. The whole left-hand region forwards each successful source exit
at the state the source reached. The local payload passes through `a`
and external payloads pass through unchanged. Under any nested CFG
the protected prefix keeps its dispatch labels and payloads. This
preserves all faults and both primitive divergence and internal replay.
[Installed rule][ssa-ub-paper-rewrite] [Forwarding][ssa-ub-paper-uniformity]

`uniform_of_observed_square` takes observational equality of the exact
literal square as its induction premise and proves equality for the
installed uniformity endpoints. A chosen target backedge with payload
`d′` and final state `s′` lifts to a source backedge ending at the same
`s′` with a payload that maps to `d′`. The typing invariant lets the
square be applied again at that source payload, even for a non-injective
state map. Forward transport alone permits additional target steps and can
add internal replay. [Uniformity][ssa-ub-paper-uniformity]
[One-way discriminator][ssa-ub-uniformity-regression]

`uniform_native_square` discharges the premise when the square has a
native `SubstitutionEquiv` derivation. The fixture checks the installed
Paper constructor with a native let-value rewrite in its square, a
non-injective constructor map, and effects inside a protected nested CFG.
It observes a return at the updated state, a fault, primitive divergence
and internal replay. [Native-square fixture][ssa-ub-paper-uniformity-regression]

### Shaped descent for the guarded Paper quotient

`Shape.Paper.eqv_denote` interprets all constructors of the installed
`Paper.Eqv` over free SSA types in shaped models. `Shape.Paper.denote`
descends to the existing continuation quotient `Paper.Hom` by applying
the theorem pointwise to exactly typed representatives. The proof assumes
typed environments and successful primitive replies of the declared type.
Primitive transitions may be nondeterministic and stateful, and the
fault and primitive divergence relations remain arbitrary.
[Shaped descent][ssa-ub-paper-descent]

| Installed constructors | Operational argument |
|---|---|
| `cfgEta` | Native substitution soundness covers the native subrelation. The separate `etaPost` step compares dispatch from the entry's selected payload, then runs the same arbitrary postcontinuation. |
| `productBeta`, `productEta` | The constructor pair has two pure components, bound in de Bruijn order. Product η uses the existing shaped product law. |
| `symm`, `trans`, `let₁`, `let₂`, `case`, `cfg` | Reuse observational congruence with typed replies at each reached binder or local block. |
| `lsubstCongr`, `lsubstPost` | A guarded literal substitution runs its continuation only after a successful producer exit, using that payload and final state. It preserves internal transitions and infinite replay, carries through producer faults and divergence, and admits new observations from a reached continuation. |
| `substVars`, `renameLabels` | Realize in-scope constructor images as a typed environment. Reflect label renamings through successful exits, preserving faults and divergence. |
| `collapsePost`, `uniform` | Reuse duplicate-label elimination and apply `uniform_of_observed_square` to the recursive hypothesis for the exact literal square. |

The stateful fixture also checks a uniformity square derived from Paper
product β and an instance of CFG η with an effectful postcontinuation.
The quotient maps native representatives to their ordinary observations
in the fresh-top overlay. The enriched Paper presentations have separate
generators and require their own soundness theorems.
[Regression][ssa-ub-paper-uniformity-regression]

### Guarded Paper category interpretation

For a fixed shaped model and captured environment, `Shape.Paper.interpretation`
maps the installed guarded `Paper.Interface` category to shaped
stateful observations. Objects carry exact label types. An arrow receives
a typed payload and a machine state and returns an existing lifted
`Behaviour`. Each ordinary return has the type of its exit label. Identity
returns the incoming label, payload and state. Composition uses
`Behaviour.bind`, which invokes the second arrow at the first arrow's final
state. Faults and may-divergence propagate, and fresh top propagates from
the first arrow or a reached continuation. The target satisfies both identity
laws and associativity. [Target category][ssa-ub-shaped-category]

The map on arrows is the descended `Paper.Hom` denotation at the chosen
typed payload. Its composition proof interprets the actual literal
`ContinuationFamily.compose` representative, including the weakening that
keeps the producer's input out of the second arrow's captures. The guarded
literal substitution theorem equates it with sequencing at the returned
state and payload. This preserves faults, primitive divergence, and
infinite CFG replay. The same functor restricts to the installed
empty-capture singleton category via `singletonInterpretation`.
[Functor][ssa-ub-paper-category]

The singleton regression runs a nondeterministic producer that updates
state from zero to one and a continuation whose successful execution
requires state one and returns at state three. It checks faults in both
arrows, a primitive divergence in the continuation, and infinite replay
in the producer. The source uses native representatives. Preservation of
structural operations and iteration is a separate question.
[Composition regression][ssa-ub-paper-category-regression]

### Exact sums and the empty type

The shaped observation category has a binary coproduct at the singleton
label of exact type `A ⊕ B`, with its universal property against any
shaped target interface. The injections return the chosen tag and keep
the state. Copairing passes the unwrapped payload and incoming state to
the selected arrow and returns its entire behaviour, including faults,
may-divergence, and fresh top. Every shaped sum payload is a left or right
tag with its declared type. The empty-typed singleton is initial because
it has no well-typed input. These facts follow from the free runtime
shapes for any atom typing relation.
[Target laws][ssa-ub-shaped-exact-sum]

The guarded singleton interpretation maps the installed exact injections,
copair and empty eliminator to these operations. The image of the exact
sum cocone is colimiting. The binary and initial proofs give the Mathlib
`PreservesFiniteCoproducts` property. The stateful regression takes the
installed Paper copair of two effectful arrows, checks distinct final
states and faults, and verifies that the right arm's fault and divergence
are absent from the left-tagged execution.
[Preservation][ssa-ub-paper-exact-sum] [Regression][ssa-ub-paper-exact-sum-regression]

### Product values and fixed-factor actions

The shaped singleton target identifies a product payload with a pair
of typed payloads. Building and splitting the pair are inverse. For
state-preserving value maps, pairing is pointwise and the two projections
determine it uniquely. The guarded singleton interpretation maps the
installed projections and diagonal to these value maps. It also maps
each constructor return to a value map and sends the installed
`pairArrows` to pointwise pairing whenever both interpreted legs are
certified to be value maps. The shaped model constrains successful
primitive reply types. An effect annotation alone supplies no operational
purity law. The regression gives a syntactically pure return whose
primitive changes the state in an admissible shaped model.
[Value laws][ssa-ub-shaped-product] [Preservation][ssa-ub-paper-product]

Both installed fixed-factor actions interpret over arbitrary guarded
singleton arrows. The active component starts at the incoming state.
Literal substitution repackages successful returns with the fixed
component and preserves their final state. Faults and may-divergence
pass through. The stateful regression checks that increment then double
returns state four from state one, and double then increment returns
state three, with the original tagged payload pair in both results.
It also checks pairing the projections in reverse order.
The product universal property here is for typed value maps.
[Regression][ssa-ub-paper-product-regression]

### Bind-first exact-sum iteration

The installed guarded singleton `iterateSum` for a step `A → B ⊕ A`
interprets as repeated observations of that step. The left tag returns
the payload and its final machine state. The right tag transfers that
payload and final state to the next invocation. The comparison uses the
one-label native CFG, guarded literal substitution, and the typed
payload invariant at reachable blocks. The one-step unfolding composes
the interpreted step with the exact-sum copair of identity and the
interpreted iterator.

Finite returns and faults agree in both directions. May-divergence is
either divergence in a finitely reached step or an infinite chain of
ordinary repeat observations. This uses the native CFG agreement theorem,
including its coinductive divergence proof. The interpreted native
arrows yield ordinary observations. The target closure retains its
reachable-top rule for general observation arrows. The comparison is
at the installed empty-capture exact-sum iterator. Its one-step law
follows from the guarded source law and exact-sum preservation.

The regression makes a state-changing request before a tag-producing
request. From state zero it repeats once before returning at state two,
faulting at state twelve, or diverging in the second step. From state
two it has an infinite chain of repeats.
[Preservation][ssa-ub-paper-iteration] [Regression][ssa-ub-paper-iteration-regression]

### Iteration refinement

The empty-capture `iterateSum` is monotone at each shaped model for
pointwise inclusion of complete step behaviours over typed inputs and
machine states. More permissive behaviours are on the right. Ordinary
outcomes use subset inclusion, and fresh UB is greatest. Retagging
preserves this order, so the repeated-observation comparison transports
the existing feedback monotonicity theorem to the guarded iterator.
An `Overlay.Refines` proof on typed step representatives supplies the
pointwise hypothesis in every shaped model.

A fault is a finite outcome at its exact final state. Divergence has
its own observation and can arise in a finite reached step or from an
infinite chain of repeats. With an ordinary upper behaviour each path
is matched at the same payload and intermediate state. If a reached
upper step exposes fresh UB, the upper closure is top.

The regression adds a fault while keeping the repeat to state one and
checks that the return survives. A second comparison matches every
step after erasing only the repeat's final state. Changing that state
from one to two removes the original return and reaches a fault
instead, so the erased comparison does not imply iterator refinement.
[Monotonicity][ssa-ub-paper-iteration] [Refinement regression][ssa-ub-paper-iteration-refinement]

### Exact-sum iteration of explicit overlay steps

An exactly typed overlay step with one input binder and one exact-sum
exit interprets directly as a shaped singleton arrow at a fixed capture
environment.
`iterateOverlay` closes that arrow through the existing directed feedback
and returns an arrow whose ordinary successful outputs have the result
type. The same `WithTop (Set Outcome)` carrier applies at each initial
machine state. `Overlay.Refines` on two steps implies pointwise
refinement of their iterators through the existing feedback order.

The closed behaviour is greatest exactly when finitely many ordinary
right-tagged repeats reach a step at fresh top, including zero repeats.
Every repeat carries a typed payload and its exact final machine state.
A start whose first step is ordinary and has no repeat sees exactly the
terminal observations of that step. With native representatives the
whole shaped arrow agrees with the installed guarded `iterateSum`,
including ordinary divergence.

The regression runs the same overlay step at two initial states. From
one it repeats at a new state and takes the explicit `ub` continuation,
so the result is greatest. From the other it returns at once, and its
exact ordinary singleton behaviour is independent of the unused
continuation. Replacing an ordinary continuation with `ub` is checked
as a typed refinement. This regression uses the empty-capture instance.
[Overlay iteration][ssa-ub-shaped-overlay-iteration] [Regression][ssa-ub-shaped-overlay-iteration-regression]
[Native agreement][ssa-ub-paper-iteration]

### Fixed capture packs

A step in context `[A, X]` can iterate on a product input `X × A`.
The outer product is unpacked once. Its left field supplies the fixed
capture of type `X`, which can itself contain products, and its right
field supplies the initial loop payload. Every right-tagged repeat
changes only the loop payload and machine state. Fresh top at an
initial input and state is equivalent to a finite path of such repeats
to a step at fresh top, with the original capture in scope throughout.
The existing `Overlay.Refines` order gives pointwise monotonicity.

At a fixed typed environment, the interpretation agrees with the
installed `CfgEta.TypeCategory.iterateSum` projected to Paper and with
`Paper.feedback` using the installed exact-sum dispatcher. For the
product input, the concrete native packing equation compares the
overlay arrow with `let₂ (var 0)` around that native iterator
representative. The body skips the original product slot after binding
the seed at slot zero and the capture at slot one. This equation keeps
the whole observed behaviour, including faults and both sources of
may-divergence. The product-input comparison uses one capture binder of
arbitrary exact type.

The literal-UB regression starts both runs with the same seed and
machine state zero. Both repeat with a changed payload at state one.
The first capture then reaches UB. The second reaches an ordinary
return at state two.
[Packed iterator][ssa-ub-shaped-capture-iteration] [Native comparisons][ssa-ub-paper-capture-iteration]
[Regression][ssa-ub-shaped-capture-regression]

### Certified finite deterministic iteration

The finite checker compares two overlay steps in the same shaped model.
Its carrier enumerates supported captures and pairs of loop payload and
machine state. The caller supplies executable tables and a certificate
that each row equals the complete observation of the corresponding
typed step. A repeat names another coded invocation under the same
capture. Returns and faults carry an exact final state. The result
payload and final-state decoders are injective, so comparison of the
codes reflects comparison of ordinary singleton observations.

The evaluator scans at most as many rows as there are invocation codes
along the deterministic path. If that scan sees only repeats, the path has
revisited a code and repeats forever. The proof constructs the infinite
feedback path and excludes any reachable terminal row or fresh UB.
This gives an ordinary divergence observation, which is also the
result of an in-step divergence row. A reached UB row instead yields
fresh top. Exact classification gives a Boolean decision for the
existing shaped observation order at every coded start, with more
permissive behaviour on the right. Each certified row must have exactly
one ordinary outcome or be fresh top. Empty and nondeterministic step
behaviours are outside this table presentation.

The certified regression reaches literal UB after a state-changing
repeat, follows a two-state cycle with no reachable UB, and checks an
ordinary fault and an in-step divergence. Replacing the UB continuation
with an ordinary return passes refinement toward the UB variant. The
reverse comparison fails.
[Checker and exactness][ssa-ub-finite-iteration] [Certified regression][ssa-ub-finite-regression]

The executable step syntax generates these tables and their certificates.
It uses exact free types over `Empty`, constructor expressions, typed calls,
exact-sum case with a payload binder, and literal overlay UB. Each program
elaborates to a typed overlay region using native atoms and label substitution.
The shaped model is the graph of the deterministic typed primitive interpreter
on `Fin states`. The compositional proof equates structural evaluation with
the complete observation of that region. A successful call evaluates its
continuation at the reply's final state. Faults and primitive divergence stop
the step. A case evaluates only its selected continuation.

Capture codes select the supported captures, and seed and result equivalences
code all values at the two exact exit types. At every supported capture, seed
and machine state, the decision compares the existing captured feedback
observations. Recursive native CFGs and arbitrary overlay representatives
are outside this executable step grammar.
[Syntax and certificates][ssa-ub-finite-syntax] [Generated comparison][ssa-ub-finite-syntax-regression]

### Packet-local cyclic overlay CFGs

A positional overlay CFG can use a finite table of these acyclic blocks.
All internal labels accept the same exact payload type. The entry is a
native jump with a constructor expression, and each block sees its incoming
payload and the original capture. A successful block chooses the external
exit or a packet carrying a destination label and its next payload. Native
case and branch atoms decode that packet at the reply's final machine state.
The empty alternative used to terminate the packet type cannot carry a
shaped value.

The bounded traversal of generated rows classifies both the actual positional
`Region.feedback` observation and the exact-sum iterator that dispatches to
the same typed block denotations. The agreement includes fresh UB, return
and fault states, primitive divergence, and infinite replay. At each coded
capture, the existing Boolean checker decides refinement at every common
entry label, typed constructor input and initial state. The fragment uses
deterministic finite-state primitives, homogeneous internal labels, one
external label and a fixed capture. It elaborates to the existing evaluator
and does not accept arbitrary native CFG representatives.

The regression follows label zero to label one and back, changing the
machine state at each jump before reaching literal UB. It also exercises a
return after the same backedge, an unaffected external exit, a two-label
silent cycle, and a fault with a distinct final state.
[CFG agreement and decision][ssa-ub-finite-cfg] [Two-label regression][ssa-ub-finite-cfg-regression]

### Heterogeneous packets and ordered exits

The positional variant assigns each internal and external label its own exact
payload type. The packet for a label list is the dependent sum of an index and
a value of the type at that index. It is equivalent to shaped values at the
installed `packedExitType`. Seed and result codes are equivalences for the two
packet interfaces. Invocation codes include the machine state. Return codes
keep the external position even when two exits carry the same type and value.

Each generated row gives the complete observation of its installed typed
routed block. The same scan classifies the positional overlay CFG and, after
packing the external return tags, the exact-sum iterator. The Boolean decision
compares the shaped observation order directly at all common entry labels,
typed constructor inputs, machine states, and coded captures. The source
fragment uses acyclic typed blocks and the shaped graph of deterministic
finite-state primitives.

The regression crosses between a unit label and a product label, replays a
silent cycle, and follows a state-changing backedge to literal UB. Two
variants that return unit at distinct exits fail comparison in both
directions. A third exit carries a product.
[Dependent packets and decision][ssa-ub-dependent-cfg] [Heterogeneous regression][ssa-ub-dependent-cfg-regression]

### Native packed CFG readback

A typed native CFG can supply the block table directly. The readback takes
the expected capture and label interfaces and inspects a native `cfg` with a
constructor entry jump. Each block links a packed producer to the canonical
positional dispatcher. Producers return constructor expressions or sequence
primitive calls through one-block native links. The final check compares the
whole re-emitted native syntax, including every dispatcher, to the input.

Successful readback gives equality of typed representatives. Native
substitution and feedback conservativity transport the #3980 row
certificates and complete shaped observations to the original CFG.
The executable comparison uses each accepted CFG's actual entry, its
deterministic finite-state primitive interpreter, and the supplied exact
packet codebooks and coded captures. The native syntax covers ordinary
returns, faults, and divergence. Explicit UB remains an overlay operation.

The regression reads a native unit/product cycle, checks a state-changing
backedge, and distinguishes two entries that return the same unit at different
external positions. It also rejects a well-typed dispatcher with an extra
native binder after the entry and producers have been read.
[Native readback and transport][ssa-ub-native-packed-readback] [Native regression][ssa-ub-native-packed-regression]

### Checked router normalization

The optional normalization accepts finite stacks of redundant literal unit
binders at packed routers. It counts the leading binders at each router,
re-emits the CFG at those depths, and checks exact syntax equality. Each
wrapper weakens the whole stack below it. Repeated application of the
installed pure let substitution rule cancels the weakening. Native CFG
congruence and shaped soundness give equality of complete observations
at the original entry. The existing exact recognizer runs on the
canonical form.

The regression accepts a router with two nested binders and exact
two-slot weakening. A well-typed variant with the same depth passes its
outer bound unit to another exit. It passes the initial producer read
and fails the exact wrapper check. The accepted program retains its
ordered return, fault state, primitive divergence and infinite replay. A literal UB continuation at the first exit is reached
after the return and skipped during silent replay. The original entry
comparison still distinguishes equal payloads at different exits.
[Normalization and soundness][ssa-ub-native-router-normalize]

### Native comparison in the stateful observational institution

For two recognized native packed CFGs, the comparison decides satisfaction
of the installed observational refinement sentence at each coded capture in
the model of the supplied deterministic finite-state primitives. It compares
the original typed CFGs at their respective entries. This bridge uses native
observations, which are ordinary outcomes. Fresh overlay UB remains the
distinct greatest behaviour in the lifted order.

A failed comparison computes a capture code and initial state where the
original observations violate refinement. That model refutes the existing
all-model native refinement judgment. The regression compares the same
two CFGs under two primitive interpreters. One gives matching observations,
including a fault and divergence. The other finds the missing ordered
return after a state-changing backedge. A successful finite check therefore
certifies satisfaction for the supplied models.
[Institutional specification and witnesses][ssa-ub-native-packed-institution]

### Designated UB exits of native packed CFGs

A typed overlay continuation can send selected ordered exits of a recognized
native CFG to literal UB. Each other continuation forwards its payload to
the same exit at the incoming state. The checker reuses the native finite
execution and changes only a terminal return to a selected exit into fresh
top. Its classification theorem equates this result with the installed
label-substitution observation on the original typed CFG and entry.

The decision compares the lifted shaped order for the supplied deterministic
finite-state primitives and coded captures. With no selected exits, the
wrapper agrees with the native observation in every shaped model. The native
institution's sentences range over native CFGs. The explicit continuation
endpoints use the existing overlay denotation and order.

The regression reaches a selected exit after a state-changing backedge.
It checks ordinary-to-top refinement and a counterexample in the reverse
direction. An equal payload at another exit keeps its ordered return.
Silent replay and primitive divergence remain ordinary, and a fault
retains its final state.
[Decision and witnesses for designated exits][ssa-ub-native-exit-ub]

### Separation for one-request native CFGs

The tested fragment has no captured values and runs a shared unit-to-unit
instruction before one acyclic native block. The block forwards the reply or
emits literal unit at one of two ordered unit exits. The unused exit always
has a literal UB continuation. The used exit either returns or takes its
literal UB continuation.

The installed order is inclusion of ordinary outcomes with a fresh greatest
element at each initial state. The shaped normal form records the used exit
and whether it reaches UB. Lean proves soundness for every shaped primitive
relation, including nondeterministic replies, faults and may-divergence.
A single deterministic shaped interpreter with states zero and one separates
every failed comparison by replying with unit in state one. The exact
classification also retains fault states and primitive divergence when the
request has no return. This grammar has no internal replay.

The unrestricted observational models can answer the unit instruction with
a sum-shaped value. Forwarding that reply and emitting literal unit yield
different ordinary outcomes, although all shaped models identify the two
endpoints. Keeping the reply projection in the normal form gives an exact
characterization of the unrestricted order on this fragment. Soundness in
both classes holds at arbitrary value and state universes. The statements
combining soundness and separation use the finite witnesses' universes.
[One-request theorems][ssa-ub-single-request]

| Existing result | Scope of its separation or universal property |
|---|---|
| Ordered free UB | The initial ordered quotient has a greatest UB class at each sort. In arbitrary ordered models, the ground rules bound denotable elements. This universal property supplies no operational separator. [Ordered specification][spec] |
| Native LambdaSSA and raw rewrite obstructions | Native regions have no uniformly greatest region. Existing raw failures of guarded Paper and continuation descent use unshaped bound inputs. The one-request example is closed and obtains the unshaped value through a primitive reply. [Native obstruction][ssa-ub] [Quotient obstructions][ssa-ub-raw-obstruction] |
| Finite acyclic common requests | The packed captured grammar has a trace separator and a derivability reflection theorem in its validated Kleisli institution. Here the comparison uses complete stateful observations with literal exit UB. [Common request replay and reflection][ssa-ub-common-request] |

### Finite separation for two Boolean-dependent requests

A closed endpoint makes a unit-input request and branches on its exact
Boolean reply. The selected arm may repeat the first key or call a different
key. A second successful Boolean reply selects either an ordered unit return
or a literal UB continuation. The construction uses the native effectful
case regions and the installed typed overlay label substitution. The request
denotation retains the final state, ordinary faults, and primitive
may-divergence. Fresh top occurs exactly when two reachable successful
replies select a UB continuation.

The normal-form order requires agreement on the first key and on the second
key after each first reply. For each pair of reply tags, the ordered return
must agree or the right continuation must be UB. Monotonicity of the installed
sequencing proves soundness for arbitrary shaped primitive relations, including
nondeterministic ones.

Every failure has a deterministic three-state prefix interpreter. For a
key mismatch, it makes the left key fault and the right key diverge before
either continuation can run. For a continuation mismatch, it chooses the
two distinguishing Boolean tags and advances through distinct machine
states. Repeated keys therefore need no conflicting replies at one state.
The regression proves that one-state deterministic handlers cannot
distinguish a particular pair with this repeat. It also checks that a
competing reply in a nondeterministic model can reach UB and mask the pair's
ordered-exit difference, while the prefix interpreter keeps that reply out
of the run. The theorem covers two requests with literal unit arguments and
terminal UB. Its soundness uses arbitrary value and state universes, and its
equivalence with all-model validity uses the finite witnesses' universes.
[Two-request theorems][ssa-ub-two-request]

### Depth-bounded separation for finite request trees

The tree elaboration reuses the typed native effectful cases and terminal
continuations from the two-request fragment. It permits any finite depth,
including different lengths on different branches. Its signature has two
unit-input Boolean keys, and its leaves return unit at one of two ordered
exits or expose literal UB.

The structural order accepts any tree below a literal UB leaf. Two ordinary
leaves compare by their exit positions. Two request nodes compare when the
keys agree and both pairs of reply branches compare recursively. All other
pairs fail. In particular, immediate UB does not refine a pending request
whose successful continuations are all UB. A fault or primitive divergence
can stop the pending request before it reaches UB.

Induction proves soundness for arbitrary shaped relations and also for the
unrestricted observational relations. A failed comparison yields a
deterministic shaped interpreter with at most one plus the smaller tree depth
machine states. It advances once per selected common reply and uses the
current state to expose the first mismatch. A key mismatch faults on the
left key and diverges on the right key. A pending request can also diverge
against a leaf. Repeated keys can reply differently at different prefix
states. The closed all-model equivalences use the witnesses' universes,
and the soundness theorem also accepts arbitrary ambient contexts and
value and state universes.
[Request-tree theorems][ssa-ub-request-tree]

### Finite request trees with key-indexed replies

The dependent request tree stores a closed, exactly typed constructor
operand at each node. The signature relates the declared reply type of
each key to the packed sum of a finite list of payload types. The adapter
emits the original operand in the native request and uses the installed
typed packet router to pass the selected payload and final state to the
continuation. Leaves return at two ordered unit exits or expose literal UB.

The comparison first checks the key and the evaluated constructor
argument. It then compares branches at inhabited reply tags. At a
zero-reply key, equal queries have no branch obligations. Different keys
or evaluated arguments can still be observed through faults or divergence.
A pending request and an ordinary return fail the comparison in either
direction. Immediate UB on the right is greatest.

Soundness over arbitrary shaped relations uses the checked fact that equal
evaluated operands in this closed constructor grammar emit identical
native terms. The comparison is stated on values. The current grammar
already has canonical emissions, so the proof requires no additional
normalization assumption. Executing a prefix uses decidable key equality
and the installed decidable equality on constructor values in `Value Unit`.
It needs no enumeration of argument values. A key or argument mismatch
uses a fault for the first query and divergence for the second at the last
state. The bound is still one plus the smaller tree depth. The all-model
equivalence is for closed trees at the witness universes. Soundness allows
arbitrary shaped environments and value and state universes over the same
free types.
[Dependent request-tree theorems][ssa-ub-dependent-request-tree]

### Extraction from rank-certified native request tables

A typed table witness describes the entry packet and the literal native
rows. Each request row supplies its own closed constructor operand and
routes each typed reply to a local label. Terminal rows return unit at an
ordered exit.
The check re-emits the whole native table, including all written rows, and
compares its exact syntax with the supplied typed CFG. The entry-reachable
rank check then permits unfolding a shared destination at each incoming
edge. Selected exits continue to the existing literal UB overlay.

The extracted tree agrees with the original decorated native CFG for every
deterministic shaped interpreter in the finite primitive API, including
interpreters that inspect arguments. This preserves the selected request,
reply payload, final state, ordinary faults and primitive divergence.
The tree comparison is exact over that class. A failed comparison supplies
the existing depth-bounded shaped countermodel at the original native
entries, so it also refutes validity over all shaped models.

The input is a checked typed row witness. The operand is retained when a
row is re-emitted and when it is unfolded into a request node. The diamond
regression calls one key twice with different constructor arguments on
one execution. An edit at the shared row changes only the final operand.
The edited CFG checks against its own witness, and the original witness
rejects it. The separating prefix faults on one argument and diverges on
the other at the same state. A successful prefix preserves the ordered
exit and final state or reaches literal UB through the selected exit.
This extraction covers closed constructor operands at each site.
[Native extraction theorems][ssa-ub-native-request-trees]

### Environment-indexed extraction of open constructor operands

The open extractor takes a checked typed row witness, the original typed
native CFG, and a supplied typed caller packet. It re-emits the written CFG
and checks ranks on the entry-reachable rows. The entry forwards the caller
packet to the first row. A request operand is a pure typed constructor
expression over the incoming packet at slot zero and the original caller
packet at slot one.

A tree node stores the evaluated argument and a continuation indexed by
both the reply position and its typed payload. The continuation evaluates
the next operand with the actual reply as its incoming packet. This
representation needs no enumeration or equality test for reply values.
The rank bounds extraction along a branch and certifies termination.

Successful extraction agrees with the original CFG and its designated
literal-UB exit continuations at every initial machine state of the
deterministic shaped primitive interface. The equality retains ordered
exits and final states, faults and their states, divergence, and fresh top.
The regression sends different Boolean payloads at the same reply position
and uses the payload as the next request's argument. The depth-bounded
separation theorem applies to the closed fragment above.
[Open extraction theorem][ssa-ub-open-operand-extraction]

### Refinement at a fixed typed caller packet

For two successfully extracted endpoints with the same entry packet type,
`Table.refines_iff` identifies the installed shaped order at that packet,
over every deterministic shaped primitive interpreter and initial state in
the finite-state API, with the logical tree relation `Tree.Refines`.
Matching queries agree on the opcode and evaluated argument. They compare
continuations at every actual typed reply position and payload. A tag
with an empty payload type contributes no comparisons; a key with no
successful reply can still fault or diverge. Matching queries run from
the same state, and a reply passes its final state to both continuations.
Ordered exits and fault states remain observable. Literal UB is greatest
on the right. A pending request can diverge or fault before a later UB.

Failure selects a single finite path of shared replies and a final test.
The deterministic handler has one state per shared reply, so repeated
queries can receive different replies at different positions. It faults
on the left query and diverges on the right at an unequal pair of queries.
The successful reply steps use actual typed values. The primitive API
permits those replies at the recorded argument and state. A stricter
handler contract that forbids a recorded reply could prevent this witness.

The checked comparison bounds the number of shared replies by the smaller
of the two extraction budgets (entry rank plus one); the handler adds one
final test state. Witness existence uses classical reasoning and needs no
exhaustive reply enumeration. The regression takes two different payloads
at the same reply tag: one distinguishes a next argument that reads the
reply from one that reads the caller packet, and the other leaves the two
observations equal. This equivalence quantifies over deterministic
finite-state primitive interpretations at the supplied packet.
[Open refinement theorems][ssa-ub-open-operand-refinement]

### Executable refinement at a supplied caller packet

`ReplyEnumeration` supplies a list for each opcode and a proof that it
contains every typed packet in that opcode's dependent sum of reply
positions and payloads. Duplicates are allowed. A key with no possible
reply has an empty list. The comparison uses decidable opcode equality
and the installed decidable equalities for evaluated constructor values
(`Value Unit`) and terminal exits. It takes one typed caller packet,
with no enumeration of the caller interface.

`Table.checkRefinement?` uses the original exact re-emission and rank
checks. Its Boolean verdict agrees with `Table.refines_iff` for
successfully extracted endpoints under the deterministic shaped
primitive interface. An absent verdict indicates failed extraction.
`Table.compare?` also returns the first distinguishing prefix in the
supplied reply order. The existing handler replays that prefix on the
original typed endpoints. The proof certifies both paths and the same
extraction rank bound, with one additional state for the final test.

The native regression puts two payloads at tag zero. The first agrees.
The second changes the evaluated next argument and produces a prefix
with a fault on the source and divergence on the target. The checks
also distinguish reached literal UB from an ordinary return and failed
extraction from a rejected comparison.
[Executable refinement checker][ssa-ub-open-operand-checker]

### Executable refinement over a finite caller interface

`CallerEnumeration` supplies a list of all shaped packets at the shared
entry type and a proof of exhaustiveness. `Table.compareInterface?`
checks both original CFGs once, then scans the caller packets using the
pointwise checker. An absent verdict reports failed exact readback or
ranking, including at an empty caller interface. After successful
readback, acceptance is equivalent to shaped refinement at every typed
caller packet and on every deterministic finite-state primitive
interpreter and initial state.

Rejection returns a caller packet and the actual pointwise prefix.
`Table.compareInterface_counterexample` certifies membership in the caller
list, feasibility in both extracted trees, the existing rank bound, and
failure of refinement between the original endpoints in the prefix model.
The regression compares a second request that reads the caller with one
that uses a literal. The first listed caller packet agrees for every
reply. The later packet fails after a shared reply. An empty caller list
and an exact table with a reachable request backedge exercise the
readback boundary.
[Finite caller checker][ssa-ub-open-caller-interface]

### Rank dependence of a future cyclic product comparison

| Obligation | Current checked use of rank | Requirement for a cyclic product comparison |
|---|---|---|
| Readback and extraction | Exact re-emission uses `sameRegion_eq` independently of rank. `Table.entryCheck` ranks the entry-reachable graph of written reply tags, including tags with no inhabited payload. Unreachable rows still participate in exact syntax comparison. `Table.expand` follows each typed reply edge at a strictly smaller rank. This is what permits an exhaustive tree rather than a cyclic graph. | Use exact re-emission and the rank-free one-step certificate below. Retain cyclic continuations as graph edges. |
| Termination and witness length | `Tree.compare` recurses structurally on its left tree. The reply and caller lists bound their respective scans. Rank supplies the tree and its `Fits` bound, which bounds the length of the certified common prefix. | Use a worklist over finite pairs of exact configurations, including each label and incoming payload with the caller held fixed. Exhaustive reply enumeration gives finite successors. A shortest path in a certified finite product could bound a counterexample, with one additional test state. |
| Semantic soundness and completeness | `Table.observe_extract` proves agreement by induction on extraction fuel. Tree soundness and prefix separation recurse on trees. The native feedback bridge and its finite-UB and infinite-divergence characterizations have no rank premise. | Prove that product steps match actual typed routing at a shared machine state and preserve each reply's final state. Account for finite exits, faults, divergence within a request, and infinite replay of matching requests. Check reachable literal UB in the installed order. A completeness proof also needs the handler to realize each chosen typed reply at its recorded argument and state. |

For a universal comparison over the current primitive interface, a common
query can use the same action on both sides. The witness allocates fresh
handler states along the chosen path. A checker for a single fixed
interpreter instead needs to represent its machine state in the
configurations. The existing cyclic native checker proves an agreement
theorem for a supplied finite deterministic interpreter and coded starts.
The finite caller checker here still requires the entry rank on both
sides.
[Rank checker][ssa-ub-open-ranks] [Native feedback][ssa-ub-feedback]
[Fixed-interpreter cyclic checker][ssa-ub-cyclic-native-checker]

### Rank-free steps for request-guarded native tables

`Table.head?` checks exact re-emission and reads one label and incoming
payload from an existing typed table witness. It uses the same positional
`Packet` as the finite CFG machinery. The caller packet stays fixed.
The step records the opcode, evaluated argument, and the successor for
each exact reply position and payload. `Head.execute` needs a
deterministic shaped primitive interpreter and the current machine state.
It neither follows the successor nor needs an entry rank.

`Table.feedback_step` identifies the complete local native observation.
`Table.feedback_step_iff` identifies every internal feedback edge with
the computed successful reply, including the destination label, typed
payload and final state. The local native observation retains an outward
exit's ordered position. `Table.observe_step` applies the actual exit
continuation at that position, so a designated exit yields fresh top.
Faults keep their state, and in-request divergence remains ordinary.
`Table.observe_entry` connects the initial typed point to the original
decorated CFG after exact re-emission.

The entry is one caller-forwarding jump. Each represented block either
exits or makes one request before any internal edge. The readback
regression rejects a well-typed silent self-cycle. The guarded regression
reaches a backedge with a changed payload and state. It also constructs an infinite replay of
successful requests with ordinary divergence in the installed feedback.
A supplied exhaustive `ReplyEnumeration` makes the possible typed
successors a finite list.
[Guarded step and correspondence][ssa-ub-open-guarded-step]

### Soundness of a closed guarded product certificate

`Table.checkProduct` checks a supplied finite list of paired exact
configurations. The entry pair must be listed. Each listed pair uses the
acyclic checker's local clauses for the two evaluated requests or the
ordered exits. Matching requests agree on the opcode and evaluated
argument. Every typed reply in the exhaustive enumeration must route to
another listed pair, including pairs of terminal rows. An immediate
designated exit on the right permits any left head. Other terminal pairs
must return at the same ordinary exit.

`Table.checkProduct_sound` uses the same deterministic shaped interpreter
on both exact-readback endpoints at their supplied caller packets and a
common initial machine state. An equal request sees the same reply or
fault and its state, or the same in-request divergence. No machine-state
enumeration is needed in the certificate because the proof synchronizes
the actual reply state under every admitted interpreter. A hypothetical
violation at a related pair would have to advance through matched
successful replies forever. `close_infinite_of_singleton` proves that
each of those native feedback closures is the ordinary singleton
divergence observation. Fresh top still requires a reached designated
exit.

The cyclic fixture pairs two different loop labels and needs the pair with
the changed incoming packet.
A second fixture omits the shared successor reached by the later
payload at the same reply tag. Adding that pair exposes different next
arguments. Its concrete prefix makes one native runner fault and the
other diverge. The checker validates supplied relations in the
request-guarded grammar. Search and completeness are separate from this
soundness result.
[Product certificate][ssa-ub-open-guarded-product]

### Reachable search for a guarded product certificate

`Table.searchProduct` starts at the pair of typed entries. Each side
supplies an exhaustive list of exact label-and-payload configurations,
and the opcode signature supplies exhaustive typed reply packets.
Discovering a pair removes its copies from the remaining Cartesian
inventory. The initial inventory length bounds the number of discoveries.
The search uses the label and evaluated payload as its configuration key,
so a backedge can revisit the same label with a new packet.

The local test is `Head.checkPair` with the successor predicate always
true. The outgoing edges enumerate the paired successors of equal
requests. The factorization theorem recovers the entire `Head.checkPair`
check by testing the local clause and the successor predicate on each
edge. A successful search returns a certificate accepted by
`Table.checkProduct`, and every listed pair has a path from the entry.
Search succeeds exactly when some accepted certificate exists.

A rejection reports a reached pair, the failing local comparison and
the shared reply path in forward order. The path records the opcode,
reply position and typed payload at each edge. This is a syntactic
certificate. The scheduled feasibility result below gives conditions
for realizing such a path in one deterministic interpreter. Exact native readback is the separate premise
when applying the existing semantic soundness theorem to an accepted
certificate. The regressions exercise a changed packet on a revisit and
the later payload at the same reply tag.
[Product search and correctness][ssa-ub-open-guarded-search]

### Interpreter feasibility of a scheduled product path

The installed `Syntax.Primitives` domain is the opcode, its exact typed
argument and the current finite machine state. Its answers are a typed
return at a final state, a fault at a final state, or ordinary
divergence. The finite script compares the opcode, evaluated argument
and incoming state together. Equal keys must agree on their entire
typed answer, including the final state. `InterpreterScript.feasible_iff`
proves necessity and sufficiency. Executable first-match lookup extends
the consistent rows with any total typed fallback. Ordinary divergence
provides a fallback even for an opcode with no inhabited reply type.

`Table.schedule_rejection` records the synchronized queries of a reported
path for a supplied initial state and one reply state per edge. It uses
the actual typed reply packet at each edge. `ScheduledPath.feasible_iff`
characterizes realization of that schedule by one interpreter. Under
realization the installed observation on each side agrees with the
observation at its reached configuration and final state.

At two reached exits, a different ordinary return position or a source
designated UB exit refutes refinement against an ordinary target exit.
A pending-query mismatch uses a different test. Appending a source
fault and target divergence must give a consistent script with the
successful prefix. Query disagreement alone supplies no such script at
the chosen final state. These directed rules use the actual native
observations after exact readback. They cover specific semantic
rejections of the guarded fragment.

The regression schedules the search's later-payload rejection and
reconstructs one interpreter that exposes fault versus divergence.
A repeated query at the same state with two requested payloads is
impossible. The same opcode and argument at different states can
produce different replies. A separate fixture distinguishes two
ordered exits carrying unit.
[Scheduled interpreter feasibility][ssa-ub-open-guarded-replay]

`Table.searchSchedule` takes a reported shared path, a fixed initial
machine state and an exhaustive inventory of the states of a fixed
`Fin n` carrier. Each branch assigns the next store and checks agreement
on the whole typed reply, including the final store, before continuing.
Optional terminal tests are chosen at the reached store and checked in
the same script. The returned witness reconstructs one total typed
interpreter for the successful replies and the tests. For a certified
product path, success is equivalent to the existence of such a schedule.
Failure establishes infeasibility for that path, initial store, carrier
and tests. It gives no refinement verdict for the two programs.

The repeated-key fixture needs two stores for the prefix and three when
its final fault-versus-divergence test is included. When the carrier can
grow, a finite prefix can always use a fresh store for each successful
hop. This removes conflicts with prior keys, including at a fresh
terminal store. A fault and divergence still conflict if the two terminal
queries have the same opcode and argument at that store.
[Fixed-carrier schedule search][ssa-ub-open-guarded-schedule]

`Table.checkAllInterpreters?` decides the pointwise shaped refinement of
two original exact-readback guarded CFGs at supplied typed caller packets,
for all total deterministic primitive interpreters and all initial states
of the same fixed `Fin n` carrier. A failed readback returns `none`.
The support is the union of both programs' opcode, evaluated argument and
incoming state keys over their exhaustive typed configuration and state
inventories. At each distinct key the checker enumerates typed successful
replies with their final state, faults with their final state, and ordinary
divergence. The reply packet lists must be exhaustive at each opcode. The
script extension uses ordinary divergence off this support.

For each script the two runners execute independently. The existing
positional feedback classifier bounds a run by the length of its
configuration–state inventory. Exhausting the bound by internal transfers
gives an actual infinite replay and ordinary divergence. A selected ordered
exit produces fresh top. Ordinary singletons compare by exact outcome,
including ordered exit and final state, and every result refines target
top. The regression exercises a state-changing cycle and a failing
comparison whose initial evaluated arguments already differ. Enumeration
has worst-case exponential size in the number of keys. The result applies
to the guarded grammar at fixed callers and the supplied carrier.
[Fixed-carrier refinement][ssa-ub-open-guarded-fixed-carrier]

The payload-aware endpoint uses the same guarded control and emits a
typed constructor expression at each terminal row. The expression can
read the incoming packet and the caller. Its finite result code indexes
the complete typed exit packet, including the ordered tag. Exit selection
runs after decoding that packet. It hides the payload at a selected
exit and preserves the payload and final state at ordinary exits.
The decision reuses the existing fixed-carrier interpreter scan.

For the named weak-tree observer, agreement at each request and each
typed reply continuation, plus exact decoding at returns, gives
agreement with the exact native readback. The named regression reads
one register assigned by the incoming block packet and compares it to a
pure assignment of false. Two reconstructed interpreters produce
different projected bits at ordered exit zero in final state one.
The true reply rejects refinement into the fixed projection at those
same endpoints.
[Payload-aware native endpoint][ssa-ub-open-guarded-payload]
[Named weak-tree transport][ssa-ub-named-guarded-payload]

The packet-local recognizer checks the existing versioner's exact entry,
request decoder, typed reply dispatch, and terminal rows. It infers the
destinations and the ordered exit at each terminal row. The projected
bit can be the terminal bit parameter or a unit-to-bit instruction from
the supplied pure literal table. The unit-packet row needs the literal
form. The recognizer derives the full weak-tree root and typed decoder
equations for every accepted table. A comparison that cannot recognize
a named program or validate a native readback returns no verdict.
A negative verdict after both checks has a witness on the original
named runners on the supplied finite carrier. The regression sends a
changed bit and machine state around a backedge before taking the second
ordered exit.
[Recognized packet-local live-outs][ssa-ub-recognized-liveout]

The two-field profile projects an ordered pair of `Bit` registers beside
the old unit payload. At the bit-packet terminal, either slot may read
the packet parameter. At either terminal, a slot may use a pure literal
assignment from the supplied table. Exact readback checks the resulting
record order and the literal prefix in slot order. The unit-packet
terminal requires both assignments. The observer validates the packed
constructor value at the native exit type and reuses the dependent
packet decoder. The named decision uses the same complete packet and
selected-exit rule as the native decision. The regression holds the
first field, exit position, and final state equal while the second
field witnesses a negative verdict.
[Ordered two-field live-outs][ssa-ub-ordered-liveout]

The ordered named observer also runs over arbitrary deterministic
stores. Exact root and decoder replay agrees with the original native
endpoint before and after exit selection. The theorem specializes to
the existing finite named observer at an accepted readback.

The fixed packet profile has entry rank one exactly when the bit reply
leaves the request block for the bit terminal. Both unit replies go to
the unit terminal. If either endpoint is ranked, the existing cutoff
computes two stores. A differing root query can be tested at the first
store. For a common successful reply, at least one continuation is
terminal. A second store preserves a terminal packet comparison or
lets a remaining request diverge. This gives the ranked decision for
the original named ordered-live-out observations at a supplied typed
caller, with complete packet and result inventories for this profile.
The regression takes a backedge on the unranked side under a Nat store
interpreter and distinguishes its primitive divergence from the
ranked side's selected exit.
[One-ranked ordered live-outs][ssa-ub-ranked-ordered-liveout]

`Table.compareEntries?` lifts the fixed-carrier comparison to the
existing exhaustive `CallerEnumeration` of a shared typed domain. Each
caller is decoded separately into the exact entry type of each original
CFG. The two entry types need no equality proof. A single deduplicated
query support covers both decodings for every caller, and the checker
enumerates the restrictions on that support once.

A positive verdict is equivalent to exact readback at both endpoints and
the shaped order for every caller, every initial store and every total
deterministic interpreter on the supplied `Fin n` carrier. A negative
verdict carries the representative, initial store, and a script whose
reconstructed interpreter refutes that same order at the original
endpoints. An empty domain accepts after both readbacks pass. A failed
readback yields no verdict even there. The theorem fixes the carrier
size. It supplies no completeness or cutoff across different sizes.
[Shared-entry refinement][ssa-ub-open-guarded-entries]

A concrete shared-entry refutation transports along any injection
`Fin n ↪ Fin m`. Map the script's query states and the final states of
successful replies and faults, then reconstruct the total interpreter
with ordinary divergence as fallback. At the mapped initial state both
original decorated observations are the images of their old observations.
The existing bounded rows run inside the image of the injection, retaining
divergence and fresh top. Injectivity reflects the ordinary subset order,
so the refutation still has the same caller and direction.

A rejected shared-entry check therefore rejects on the larger carrier
with exhaustive inventories and the same exact-readback endpoints and
caller domain. The proof supplies the transported witness. The larger
enumeration can find a different witness first. The regression shifts a
three-state script into five states and checks a return, fault, selected
exit and infinite replay. This is an upward rejection law. It gives no
finite cutoff or downward rejection guarantee.
[Carrier embedding][ssa-ub-open-guarded-carrier-embedding]

The guarded observation proof also accepts a deterministic interpreter
on an arbitrary store type. Two finite external derivations of the
installed native feedback graphs give typed query rows, including the
whole reply at each query. `RunSupport.ofRows` takes the deduplicated union
of the common start and the returned or fault stores. Every queried store
and both terminal stores belong to that support. With (q_L) and (q_R)
recorded queries, the carrier has at most (1 + q_L + q_R) states. One
script replays both runs. Its decoded observations equal the original
decorated observations, retaining ordered exits, store equality and
distinction, faults, and fresh top. A refutation therefore yields a
negative pointwise check at the same caller and a negative shared-entry
verdict. The bound depends on these derivations.

A primitive divergence reply is a finite terminal row. An infinite
replay has no terminal row. Exact state coding of an infinite replay
would require finite support containing the states at all its invocations
and closed under their successful replies. The finite typed configuration
inventory would then bound the query keys, and replay would still need to
preserve the infinite internal path. A regression advances a natural
number at every backedge, so no finite list covers that run. The
compression theorem applies to the finite branch.
[Finite refutation support][ssa-ub-open-guarded-finite-support]

For a mixed finite and infinite pair, preserving the observation needs
only the finite side's full typed query table. The infinite side follows
every recorded reply up to its first unlisted key. That lookup gives
primitive divergence, with no further replay. If every key is listed,
the compressed runner has a genuine infinite path. All stores through the
cut or along the retained path belong to the finite run's support, so the
bound is one plus the finite run's query count. Both cases give the same
ordinary divergence as the original infinite run, while the finite
observation still decodes exactly. A mixed refutation in either direction
therefore gives a negative pointwise check at the same caller and a
negative shared-entry verdict. The bound is specific to the finite run.

Ordinary divergence refines itself and a selected-exit top. Returns,
faults and selected-exit top all fail to refine ordinary divergence.
Two infinite guarded runs give the same singleton divergence and cannot
refute each other in this order. The regression exercises a shared first
reply of a Nat run, a first missing key at the changed store, and a retained
one-state replay.
[Mixed finite and infinite refutations][ssa-ub-open-guarded-mixed-support]

The guarded runner has a finite typed derivation or an actual infinite
feedback path at every typed start. This gives the finite-model property
for independently exact-readback native endpoints and the exhaustive
shared caller domain. `Table.finite_model_property` equates refinement
over every deterministic store type in any chosen Lean universe with
`some true` from every finite-carrier check. A finite checker counterexample
can be lifted from `Fin n` into that universe using `ULift`. The observation
map preserves ordered returns, stores, primitive and infinite divergence,
and fresh top. Its injectivity reflects the order.

`Table.finite_refutation_iff` gives the existential version. A refuting
caller and initial store yield a positive carrier size, with the existing
query-count bound from the finite derivations on each side. The pointwise
check rejects at that caller and the shared check returns a rejection.
The bound depends on the witnessed derivations and supplies no fixed
cutoff. The Boolean projection returns `none` for unsupported readback,
including at size zero or for an empty caller inventory. Those cases are
vacuously positive after admission when there is no caller or no initial
store. A regression proves arbitrary-store validity for two genuine
request-guarded cycles with different entry labels by checking a closed
product certificate on every finite carrier.
[Finite-model property][ssa-ub-open-guarded-finite-model]

The guarded subclass with at least one ranked entry has a single executable
cutoff. `Table.checkRankedEntries?` checks both native readbacks and requires
an entry-rank certificate on either side. It compares on `Fin (rank + 1)`,
using the smaller rank when both are available. Neither ranked entry or a
failed readback produces `none`.

Under a shared deterministic interpreter, equal exposed queries have the
same answer. Shared faults and primitive divergence agree. Successful
replies move both runners and decrease the rank on the ranked side. The
proof follows an arbitrary-store refutation through these shared replies.
At a differing head, one store suffices for the terminal test, including
when a pending request has no successful reply. Divergence separates a
pending request from an ordinary exit, and a fault versus divergence can
separate different pending queries. A selected target exit is greatest, so
that case cannot refute the order. A selected source exit is fresh top and
can fail against ordinary divergence.

Prepending a shared reply reserves a fresh store and embeds the existing
suffix interpreter into the remaining stores. This preserves complete
native observations, with no finite-run premise on the cyclic side.
The resulting finite countermodel proves that acceptance at the computed
size implies arbitrary-store deterministic refinement. The converse
follows from the finite-model property. Regressions compare a genuine
cycle with a ranked selected exit in both orders, reject a cycle against
an ordinary return, and return `none` for two unranked entries. The
earlier two-ranked fixture still needs both stores at its cutoff.
[Ranked carrier cutoff][ssa-ub-open-guarded-ranked-cutoff]

For exact guarded tables with exhaustive finite typed configuration and reply
inventories, neither entry needs a rank. At a fixed shared caller, the product
visits exactly the reachable pairs of typed configurations. It advances only
on equal opcodes and evaluated arguments followed by a shared successful
reply. A closed certificate proves refinement on arbitrary deterministic
stores. Shared faults agree at their final store. If the two runners keep
taking matched successful replies forever, both observe ordinary divergence.

A reachable local mismatch has a terminal test. An ordinary exit differs
from another ordered exit or from a pending request forced to diverge. For
distinct queries, a fault at one key and divergence at the other suffice.
A selected source exit can fail against an ordinary outcome. A selected
target exit is greatest. Prepending each shared reply uses a fresh store
and embeds the suffix interpreter, preserving the order of its full
observations. This needs no finite derivation for either original runner.
A shortest path to a mismatch visits distinct configuration pairs, even
when the product has backedges.

`Table.checkReachableEntries?` uses the maximum distinct reachable-pair
count over the exhaustive caller inventory as a single carrier size. It
includes the terminal pair, so a path of length `k` needs only `k + 1`
stores. A supported verdict decides arbitrary-store deterministic
refinement. Failed exact readback yields `none`. The regressions accept
two relabelled productive loops and reject two unranked peers whose first
mismatch requires a packet-changing reply. A longer path to the same
mismatch takes an avoidable self-edge.
[Reachable-product cutoff][ssa-ub-open-guarded-reachable-cutoff]

`OrderedLiveOut.compareReachable?` applies the same cutoff to two checked
named packet-local RTL endpoints with an agreed constructor-bit caller.
The ordered result codec retains the original exit and both Bit fields.
Product edges still depend only on shared typed requests and replies.
The terminal test compares the full return packet at ordinary exits.
Selected exits still produce fresh top, which hides the packet. State
embedding carries the store of each return or fault, and genuine infinite
replay produces ordinary divergence.

Both native readbacks are checked before a verdict. The inventories come
from the recognized profile. At the supplied caller, the two verdicts are
equivalent to refinement or a counterexample over deterministic stores
of type `Type` at the original named observations. The cyclic regressions
use a state-changing shared handler for matched infinite replay and a
handler that returns after one backedge. On the latter run the exit, final
state and first field agree, and the second field separates the endpoints.
[Named ordered live-out cutoff][ssa-ub-named-ordered-liveout-reachable]

The native silent-head profile adds unconditional exact-typed constructor
jumps to guarded rows. Constructor substitution composes the carried
payload into the next request operand while keeping the caller binding.
The label scan stops within the number of written labels when the silent
prefix reaches an existing request or ordered exit. The request itself
still uses the interpreter at the store left by the preceding reply.
The exact native readback check precedes normalization.

`Silent.Table.head_correct` certifies an exposed head at a typed invocation
by actual native transfers. Exhausting the scan certifies ordinary
divergence in the original native evaluator. The proof builds an infinite
silent path at the unchanged store, and an exhaustive typed packet
inventory supplies a repeated configuration on it. A selected exit
remains fresh top only when reached. The cycle regression separates its
ordinary divergence from an ordinary exit and checks the directed order
against a selected exit.

`Silent.Table.checkEntries?` specializes the existing reachable-product
checker to the normalized heads. The cutoff counts synchronized label
and packet pairs after silent normalization. Silent transfers contribute
no interpreter query or extra prefix store. Productive infinite replay
expands into nonempty native segments.

A certified exhausted scan is an ordinary-divergence terminal in the
product. It matches another divergent terminal or a selected target exit.
A pending request differs from a divergent terminal in either direction
because a primitive fault can separate them. The normalized emitter
implements the terminal with a silent unit self-loop. Its native
observation is exactly the divergence singleton. Shortest mismatch paths
still use one store per shared reply and one store for the terminal test.

The finite comparison is exact for the original decorated packed CFGs at
the computed cutoff, and acceptance there is equivalent to arbitrary-store
deterministic refinement. Exhaustion at a written label, including an
unreachable label, needs no further admission gate. Failed exact readback
still returns `none`. Regressions cover two native silent cycles and a
shared state-changing request that reaches a silent cycle on one side and
an ordered return on the other.
[Silent head normalization][ssa-ub-open-guarded-silent]

`OrderedLiveOut.Silent.compare?` connects the silent terminal to the
original packet-local named RTL runner. Either of the two non-request
rows may be an ordinary ordered return or an identity self-transfer.
A successful versioned readback checks the leading decoder, self label,
and unchanged packet variable. The named iterator consumes that
self-transfer forever. The native readback represents it by the
certified silent terminal, with no request or store update.

The check uses the existing payload-aware reachable cutoff. The supplied
typed caller must agree with the seed in both named stores. Failed
recognition, caller agreement, or exact native readback yields unknown.
The observations retain the two ordered fields and final state on
ordinary returns and preserve the selected UB order. The regression
takes a state-changing shared reply to a silent loop on one side and a
return on the other. An extra request would fault under the witness
handler. The actual loop produces ordinary divergence.
[Named silent terminal transport][ssa-ub-named-ordered-liveout-silent]

`OrderedLiveOut.Identity.admit?` accepts a supplied finite layout with a
Bit entry and Bit or unit internal packets. Each row uses the existing
guarded request shape, projected return, or a checked identity packet
jump to a declared internal label of the same type. The original named
compiler checks the supplied argument types and the recognizer
reconstructs the exact numbered syntax and bindings.

The native typed resolver from the silent-terminal checker normalizes
control. Its label scan also identifies the row whose live-out
expression supplies a finite return. Packet equality transports that
expression back to the incoming typed packet. The original named
iterator follows the same prefix, and an exhausted scan yields a
genuine silent orbit. The reachable cutoff applies at the common
typed caller and the exact normalized readbacks. A rejected admission,
seed binding, or readback yields unknown. The named regressions exercise
a two-label cycle and a finite chain to an ordered return after the same
state-changing reply.
[Named identity packet transfers][ssa-ub-named-ordered-identity]

The packet-indexed profile also admits native pure sum dispatch with a
constructor jump from each arm. The selected arm binds its sum payload and
can read the incoming packet and fixed caller. The executable scan counts
full typed label/packet configurations in an exhaustive inventory.
Exhaustion gives an infinite silent path with a repeated full configuration.
Silent transfers keep the store and issue no query.

`Silent.Dispatch.Table.observe_entry` identifies the complete decorated
observation of an exact-readback original CFG with feedback over the
computed heads, including productive request replay, fault states and
selected ordered exits.
[Packet-indexed silent dispatch][ssa-ub-packet-dispatch]

The dispatcher product explores paired full typed configurations at each
fixed caller. Equal exposed requests generate a successor pair for every
typed reply payload, and terminal heads have no reply edges. A certified
closed product proves refinement over arbitrary deterministic stores.
The maximum distinct reachable-pair count over the caller inventory
suffices for a single finite-carrier comparison. A shortest mismatch path
uses a fresh state per shared reply and one state for the terminal test.
Rejection gives a caller, interpreter and initial state on this carrier
that refute the original decorated endpoints. A failed exact readback
returns unknown. Ordinary divergence remains distinct from both faults
and selected UB. The regressions exercise two original CFGs in which the
same effectful reply position reaches an ordered exit or a silent cycle
at the same label depending on the returned packet.
[Packet-indexed reachable product][ssa-ub-packet-dispatch-product]

`OrderedLiveOut.PacketDispatch.admit?` extends exact named readback to a
Bit case on the decoded block parameter. A leading typed literal assignment
supplies one Bit through the existing `rawWithLiterals` interpretation,
which emits no request for the recognized literal opcode. Each arm sends
either that Bit or the unchanged input Bit to a declared internal Bit label.
The actual packet-local versioner checks the types. The recognizer then
checks the complete numbered decoder, discriminator, branches and bindings.

`Checked.observe_normalized` relates the original mutable runner to
the full-configuration scan at the agreed caller seed. The scan retains
the packet that reached the exposed return so the ordered two-Bit
projection and final handler state are preserved. At a selected exit,
the existing decoration hides the return payload. The regression
compares a revisit with a changed Bit that returns after a state-changing
reply against a repeated full configuration that silently diverges.
An unsupported decoder or target yields unknown. The packed dispatcher
product compares unit return payloads. The named observation theorem
retains both live-out fields.
[Named Bit dispatch][ssa-ub-named-packet-dispatch]

## Coverage and gaps

| Language | Refinement and institutions in the repository | UB construction and remaining hypotheses |
|---|---|---|
| LetCase | The exact typed preorder gives `caseTheory` and ordered algebra models. The separate operational institution observes results, faults and divergence. | Instantiate the ordered monad with `casePSig` or the specification of `caseTheory`. `typedEquiv` proves both typed round trips between explicit UB and native terms generated with `op (ub A) unit`, including under binders. The interpreted order preserves and reflects on these endpoints. Arbitrary unit-typed operands can have effects, and an operational equivalence needs to preserve their evaluation and justify the sequencing and UB laws in the chosen observation model. [Ordered theory][let-theory] [Typed round trip][case] [Ordered bridge][case-refinement] [Observations][obs] |
| LetIter | `iterTheory` gives ordered refinement models. The separate quantitative `Refinement.Thms` also has categorical initiality and singleton-input completeness. Operational stuckness yields an undefined outcome, while the observational institution tracks returns, faults and divergence. | The exact literal-unit round trip and ordered quotient comparison include the iteration binder. Quantitative literal-unit UB is limited to discardable contexts and compatible effect bounds. A linear input would require a resource-consuming encoding or a different typing rule for UB. [Ordered theory][let-theory] [Ordered bridge][iter-ub-refinement] [Quantitative typing][iter-ub-quant] [Categorical initiality][quant] [Undefined outcome][iter-beh] |
| LambdaSSA | Typed terms use unary instructions and regions have separate value and label contexts. The CFG entry quotient uses `CfgEquiv`. The continuation quotients install additional equations. The observational institution has inclusion of outcomes, with an observational isomorphism to LetIter for single-exit regions. | The primitive monad supplies a unit-taking expression instruction. Every exact typing interface, including the empty-label boundary, has a countermodel to uniform greatest refinement by a native region. At a fixed model with the stated saturation assumptions the unit-fed prefix is greatest at the empty interface. The independent exact-typed overlay adds a distinct greatest element with monotone substitution and feedback, each with exact all-native CFG agreement. The overlay denotation descends through the native CFG entry quotient in all models and through native `ContinuationHom` and guarded `Paper.Hom` in shaped models over free types. [Continuation descent][ssa-ub-shaped-continuation] [Paper descent][ssa-ub-paper-descent] [CFG descent][ssa-ub-native-quotient] [Empty-label boundary][ssa-ub] [Explicit overlay][ssa-ub-overlay] [Feedback][ssa-ub-feedback] [Typing][ssa-typing] [Rewrite quotient][ssa-rewrite] [Observational isomorphism][ssa-obs] |
| LambdaRTL | The acyclic model interprets unary applications in a monad; its alphabet institution takes the observation relation as a parameter. It distinguishes lexical SSA, projected RTL and full RTL store observations. The separate machine RTL adapter reports stuckness as an undefined outcome. | A top region needs a chosen store/label observation order and a typed result and continuation interface. Its interpretation must dominate all observations for every environment at the selected boundary. An instruction relabelling or a lawful monad supplies no such law. [Syntax and model][rtl] [Institution][rtl-inst] [Machine RTL outcomes][rtl-beh] |

An effect bound of `⊤` permits all effects in the typing system. It does
not establish that any computation is greatest. The effect used for a fresh
primitive remains a parameter, and assigning the pure effect would also
invoke existing purity obligations. For a
behaviour-set model one can ask for the existing convention exemplified by
MIR's `ubClose_of_undefined`, which yields the universal outcome set.
Neither the monadic model interfaces nor weak interaction-tree equivalence
provide that UB order or its sequencing laws. [Effect system][effects]
[Empty elimination][quant-typing] [MIR UB closure][mir] [Kleisli model][kleisli]
[Weak-tree semantics][weak-tree]

## Checks

```sh
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Product.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Refinement.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Capture.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.SingleRequest.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Regression
```

[ordered]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Ordered.lean
[obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Basic.lean
[compiler]: compiles-to.md
[primitive]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Primitive/Thms.lean
[instr]: ../../Silmaril/Raw/SSA/Isotope/Institution/InstrSig.lean
[sigmap]: ../../Silmaril/Raw/SSA/Isotope/Morphism/Instructions/Signature.lean
[syntax]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Syntax/Defs.lean
[signature]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Thms.lean
[spec]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Specification/Thms.lean
[institution]: ../../Silmaril/Logic/Institution/Theory.lean
[models]: ../../Silmaril/Raw/SSA/Isotope/Logic/Metatheory/Theory/OrderedModel.lean
[case-typing]: ../../Silmaril/Raw/SSA/Isotope/LetCase/LocallyNameless/Typing.lean
[ssa-syntax]: ../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean
[case-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Thms.lean
[case-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Model/Thms.lean
[case-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Regression.lean
[case]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Thms.lean
[let-theory]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Isotope.lean
[iter-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Thms.lean
[iter-ub-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Refinement/Thms.lean
[iter-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Regression.lean
[iter-ub-quant]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Quantitative/Thms.lean
[quant-typing]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Typing.lean
[quant]: ../../Silmaril/SSA/Isotope/Refinement/Thms.lean
[iter-beh]: ../../Silmaril/Raw/SSA/Isotope/LetIter/Semantics/Behaviour.lean
[ssa-typing]: ../../Silmaril/SSA/Isotope/LambdaSSA/Typing/Defs.lean
[ssa-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Isomorphism.lean
[rtl]: ../../Silmaril/SSA/LambdaRTL/Defs.lean
[rtl-inst]: ../../Silmaril/SSA/LambdaRTL/Institution/Defs.lean
[rtl-beh]: ../../Silmaril/Raw/Machine/RTL/Behaviour.lean
[effects]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Effects.lean
[mir]: ../../Silmaril/Raw/Compiler/Mir/Semantics.lean
[kleisli]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Kleisli/Thms.lean
[weak-tree]: ../../tests/ssa/LetIterWeakTreeSoundness.lean
[ssa-observations]: ../../Silmaril/SSA/Isotope/Institution/Observational/Thms.lean
[ssa-ub-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Defs.lean
[ssa-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Thms.lean
[ssa-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Regression.lean
[ssa-ub-overlay-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Defs.lean
[ssa-ub-overlay]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Thms.lean
[ssa-ub-overlay-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Regression.lean
[ssa-ub-feedback]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Thms.lean
[ssa-ub-feedback-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Regression.lean
[ssa-ub-uniformity]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Thms.lean
[ssa-ub-uniformity-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Regression.lean
[ssa-ub-elimination]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Thms.lean
[ssa-ub-elimination-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Regression.lean
[ssa-cfg-quotient]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-paper-soundness]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/Soundness/Thms.lean
[ssa-ub-native-quotient]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Thms.lean
[ssa-ub-descent-obstruction]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Obstruction/Thms.lean
[ssa-ub-descent-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Regression.lean
[ssa-ub-shaped-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Defs.lean
[ssa-ub-shaped-laws]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Thms.lean
[ssa-ub-shaped-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Regression.lean
[ssa-native-continuation]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Category/Defs.lean
[ssa-ub-shaped-continuation]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Continuation/Thms.lean
[ssa-ub-shaped-continuation-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Continuation/Regression.lean
[ssa-ub-paper-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/Defs.lean
[ssa-ub-paper-collapse]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Thms.lean
[ssa-ub-paper-uniformity]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Uniformity/Thms.lean
[ssa-ub-paper-descent]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Descent/Thms.lean
[ssa-ub-shaped-category]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Thms.lean
[ssa-ub-paper-category]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Thms.lean
[ssa-ub-paper-category-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Regression.lean
[ssa-ub-shaped-exact-sum]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/ExactSum/Thms.lean
[ssa-ub-paper-exact-sum]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/ExactSum/Thms.lean
[ssa-ub-paper-exact-sum-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/ExactSum/Regression.lean
[ssa-ub-shaped-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Product/Thms.lean
[ssa-ub-paper-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Product/Thms.lean
[ssa-ub-paper-product-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Product/Regression.lean
[ssa-ub-paper-uniformity-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Uniformity/Regression.lean
[ssa-ub-paper-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Regression.lean
[ssa-ub-paper-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Thms.lean
[ssa-ub-paper-iteration-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Regression.lean
[ssa-ub-paper-iteration-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Refinement/Regression.lean
[ssa-ub-shaped-overlay-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Thms.lean
[ssa-ub-shaped-overlay-iteration-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Regression.lean
[ssa-ub-shaped-capture-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Capture/Thms.lean
[ssa-ub-paper-capture-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Paper/Category/Iteration/Capture/Thms.lean
[ssa-ub-shaped-capture-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Capture/Regression.lean
[ssa-ub-finite-iteration]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Thms.lean
[ssa-ub-finite-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Regression.lean
[ssa-ub-finite-syntax]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Syntax/Thms.lean
[ssa-ub-finite-syntax-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/Syntax/Regression.lean
[ssa-ub-finite-cfg]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Thms.lean
[ssa-ub-finite-cfg-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Regression.lean
[ssa-ub-dependent-cfg]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Thms.lean
[ssa-ub-dependent-cfg-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Regression.lean
[ssa-ub-native-packed-readback]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/Thms.lean
[ssa-ub-native-packed-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/Regression.lean
[ssa-ub-native-router-normalize]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/Normalize/Thms.lean
[ssa-ub-native-packed-institution]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/Institution/Thms.lean
[ssa-ub-native-exit-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/ExitUB/Thms.lean

[ssa-ub-single-request]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/SingleRequest/Thms.lean
[ssa-ub-raw-obstruction]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Obstruction/Thms.lean
[ssa-ub-common-request]: ../../Silmaril/SSA/Isotope/Bridge/Acyclic/Positional/Capture/Institution/Rewrite/Repair/Reply/Payload/Finite/CommonRequest/Thms.lean
[ssa-ub-two-request]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/TwoRequest/Thms.lean
[ssa-ub-request-tree]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/RequestTree/Thms.lean
[ssa-ub-dependent-request-tree]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Thms.lean
[ssa-ub-native-request-trees]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/Thms.lean
[ssa-ub-open-operand-extraction]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Thms.lean
[ssa-ub-open-operand-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Refinement/Thms.lean
[ssa-ub-open-operand-checker]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Refinement/Checker/Thms.lean
[ssa-ub-open-caller-interface]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Refinement/Checker/Interface/Thms.lean
[ssa-ub-open-guarded-step]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Thms.lean
[ssa-ub-open-guarded-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Product/Thms.lean
[ssa-ub-open-guarded-search]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Product/Search/Thms.lean
[ssa-ub-open-guarded-replay]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Product/Search/Replay/Thms.lean
[ssa-ub-open-guarded-schedule]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Product/Search/Replay/Schedule/Thms.lean
[ssa-ub-open-guarded-fixed-carrier]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FixedCarrier/Thms.lean
[ssa-ub-open-guarded-entries]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FixedCarrier/Entry/Thms.lean
[ssa-ub-open-guarded-carrier-embedding]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FixedCarrier/Entry/State/Thms.lean
[ssa-ub-open-guarded-finite-support]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FiniteSupport/Thms.lean
[ssa-ub-open-guarded-mixed-support]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FiniteSupport/Infinite/Thms.lean
[ssa-ub-open-guarded-finite-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FiniteSupport/Model/Thms.lean
[ssa-ub-open-guarded-ranked-cutoff]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FiniteSupport/Model/Ranked/Thms.lean
[ssa-ub-open-guarded-reachable-cutoff]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FiniteSupport/Model/Reachable/Thms.lean
[ssa-ub-named-ordered-liveout-reachable]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Reachable/Thms.lean
[ssa-ub-named-ordered-liveout-silent]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Silent/Thms.lean
[ssa-ub-named-ordered-identity]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Silent/Identity/Thms.lean
[ssa-ub-open-guarded-silent]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Silent/Thms.lean
[ssa-ub-named-packet-dispatch]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Silent/Dispatch/Thms.lean
[ssa-ub-packet-dispatch]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Silent/Dispatch/Thms.lean
[ssa-ub-packet-dispatch-product]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/Silent/Dispatch/Product/Thms.lean
[ssa-ub-open-ranks]: ../../Silmaril/SSA/Isotope/Bridge/Acyclic/Positional/Rank/Thms.lean
[ssa-ub-cyclic-native-checker]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Category/Iteration/Finite/CFG/Dependent/Native/Thms.lean

[ssa-ub-open-guarded-payload]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Shape/Separation/DependentRequestTree/Native/OpenOperands/Step/FixedCarrier/Payload/Thms.lean
[ssa-ub-ranked-ordered-liveout]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Ranked/Thms.lean
[ssa-ub-ordered-liveout]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Ordered/Thms.lean
[ssa-ub-recognized-liveout]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Recognize/Thms.lean
[ssa-ub-named-guarded-payload]: ../../Silmaril/SSA/Isotope/Bridge/NamedFlat/ITree/Entry/LiveOut/PacketLocal/Guarded/FixedCarrier/Payload/Thms.lean

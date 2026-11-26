# RVSDG φ linking and finite recursive calls

The φ implementation follows Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers*,
arXiv:1912.05036v2, §4.2.3 and Definitions 7–8 for φ, and §4.3 for θ. The versioned PDF has
SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The ω linker reads typed imports and produces the ordered export tuple.
It links λ closures and δ initializers as before. At φ, it reads the
outer context once and packages the static member table with the context.
Each output contains that group environment and a typed member index.
The stored environment does not contain its own member references.
Invocation reconstructs the region's recursion arguments and its
in-scope earlier physical λ outputs as references to the same group.
It then reads the selected λ's captures and enters the body with the
ordinary argument tuple. Module linking traverses the same typed graph
or term interfaces used for λ, δ, φ and ω. `link_toGraph` proves exact
agreement on exports, including member references and numbered global
identities.
[Runtime definitions](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Defs.lean) ·
[Recursive linker](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Defs.lean)

The inductive `Returns` judgment has explicit premises for entering a
callable, running its body, applying a callable, entering the chosen γ
arm, and completing θ iterations. A stopping body publishes the carried
tuple. A continuing body feeds that tuple to a fresh activation with
an empty local prefix. Both body execution and recursive calls use the
same judgment. Its rules are independent of the bounded evaluator.
`call_iff` proves that a call returns an exact typed value/state tuple
iff some pair of call-depth and per-θ bounds returns it.
`returns_eventually` supplies sufficient bounds valid at every larger
pair. During a single θ invocation the remaining iteration count
decreases, while its body and callees still receive the full per-θ
budget. Exhaustion at a particular bound leaves divergence undecided.
The linker takes a supplied import tuple. External import cycles and
linking by symbol name are outside this slice.
[Public theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Thms.lean)

The first fixture links two mutually recursive members. The first
captures the second through a recursion argument, and the second
captures the first through its earlier physical λ output. Both capture
an imported value, pass a decreasing state through alternating calls,
and return the captured value and final state at zero. A second linked
φ member enters θ and calls itself inside the selected γ arm of the
body. The fixture checks exhaustion independently at each bound and
the exact returned tuple when both bounds suffice.
[Fixtures](../../../../tests/ssa/RVSDGPhiCalls.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPhiCalls.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```

## Typed continuations for non-tail calls

The continuation machine steps the existing runtime jobs and the actual
body of each resolved closure or φ member. At a binding, the stack saves
the typed remainder of the region, its entry tuple, and its current
locals. The node reads its operands in that scope. An application opens
the callee with fresh locals, and γ enters only its selected child. When
the result arrives, the machine appends the entire typed tuple to the
saved locals before running the remainder. The caller's earlier wires
and the callee's returned ports can both feed later nodes. A θ loop
frame keeps this enclosing continuation. Each body starts with empty
locals and takes the carried tuple as its input. Selector `1` feeds
back the carried ports to a fresh body activation. Selector `0` returns
those ports to the enclosing binding, which resumes the saved suffix.
[Machine definitions](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Defs.lean)

At each step the proof invariant interprets the active job and each
pending frame with the independent `Returns` judgment. Induction on
`Returns` constructs a completed trace, using both the stopping and
continuing θ rules. The theorem `completes_iff_returns` gives both
directions for all existing jobs, including θ. The real bounded
evaluator agrees on the same full tuple through `Recursive.call_iff`.
The theorem concerns finite returns.
[Adequacy API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Thms.lean)

The linked φ regression descends twice before a base call. An exact
intermediate configuration contains both non-tail application frames,
including the saved state before each callee runs. The prefixes append
`1` to state, the base appends `2`, and each suffix appends `3` and the
length of its own saved prefix state. The final tuple is data `12` and
state `[1, 1, 2, 3, 2, 3, 1]`. Both the stack machine and the existing
bounded evaluator return it.

A second module links a λ that captures the φ member and calls it from
inside θ. The fixture checks that the second body starts with empty
locals and the fed-back tuple. It then checks that exit returns the
carried tuple to the same parent continuation. The final state
`[1, 4, 2, 5, 4, 2, 6, 3, 1]` records the parent prefix, both body and
callee activations, feedback, exit, and the resumed suffix. The
bounded evaluator agrees and exhausts with only one allowed iteration.
[Continuation fixture](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveContinuations.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms'
```

## Partial primitive actions

The partial continuation machine adds a store `σ` to the existing
typed control state. Primitive meanings are `StateT σ Part` actions on
typed tuples. A successful action supplies the next tuple and store.
The explicit RVSDG state ports remain part of those tuples. Structural
steps preserve the ambient store and use the existing control, stack,
closure resolution, γ selection and θ restart rules. Linking still
uses the existing total linker, including its δ initializers. The
partial actions apply during invocation.
[Shared state model](../../../../Silmaril/SSA/RVSDG/NestedTheta/OrderedState/Defs.lean)

A selected primitive with an undefined result has its own
`Config.Blocked` observation. It retains the attempted primitive,
typed input, current store and pending stack. The blocked state
has neither a successor nor a returned result. Determinism also
rules out an infinite control run from any configuration that
takes a finite path to that blocked state. This is a statement
about an observed selection on a finite path. The primitive
action's `Part.none` by itself expresses undefinedness.

The independent finite `Eval` judgment and finite machine paths agree
in both directions from a fresh entry, including an invocation of a
linked export. A return has the same full typed tuple and store. A
blocking derivation reconstructs the selected primitive, its typed
input and store, and every live frame at the endpoint. Because there
is no transition out of a block, a path to that endpoint cannot have
passed an earlier block. The canonical total lift recovers the
original control steps and finite `Returns` exactly, with a constant
extra store.
[Public theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Thms.lean)

The linked λ/φ fixture calls a selected γ arm from an active θ body.
A preceding primitive updates the explicit state from `7` to `8`
and the store from `20` to `21`. Tag `0` skips the undefined arm and
returns the updated tuple. Tag `1` blocks at that arm's primitive
with both updates visible and all five pending frames intact.
The regression computes both finite paths directly from machine steps
and reflects them into the independent judgment.
[Linked fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Regression'
```

### Productive feedback with partial actions

The [partial feedback judgment](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Feedback/Defs.lean)
pairs the carried tuple with the ambient store. Each iteration starts
with fresh locals, derives a successful finite evaluation of the actual
θ body, and selects feedback. Replay takes a nonempty segment to the next
restart with the same parent frame and the exact new tuple and store.

A finite route to the selected θ uses the syntax-directed reaching
rules for completed bindings, selected γ arms, opened calls, and
nested θ bodies. Completed work uses successful partial evaluation.
Each active binding or enclosing loop saves its typed pending frame.
A route followed by an infinite sequence of successful feedback
iterations yields a productive microstep trace from the linked
entry. The certificate covers one live θ with infinitely many
returning body activations. Nonreturning bodies and general infinite
call descent are separate cases.

In the linked fixture, one interpretation permits every selected action
and both the state wire and store increase on each restart. Setting a
cutoff of `23` leaves two completed feedback iterations and blocks in
the third body at state wire `10`, store `23`, with all five frames
live. Finite reflection recovers the exact blocked observation, and
determinism excludes an infinite trace from that blocked run's entry.
[Replay theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Feedback/Thms.lean)

### Nested call descent with partial actions

A [partial call prefix](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/CallDescent/Defs.lean)
starts in an opened caller and stops at its selected application.
Earlier bindings, including returning calls, use successful
`Partial.Eval` derivations and thread the ambient store. A prefix may
follow a selected γ arm or enter a live θ body after finitely many
successful feedback iterations. The selected call receives the full
typed argument tuple and current store. Its caller's saved suffix,
entry tuple, and local tuples stay in the ordered pending stack.

An independent infinite descent specifies these prefixes at successive
call entries. Replay produces one actual microstep stream with strictly
increasing positions for the entries and strictly growing live stacks.
Each position matches the exact callable, arguments, store, and stack
from the certificate. The linked regression completes a helper call in
each activation before making a non-tail recursive call. Its second
recursive checkpoint has state wire `9`, store `22`, and two distinct
pending state-changing suffix frames.
[Replay theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/CallDescent/Thms.lean)

The finite interval theorem also recovers a prefix from observed
microsteps using only steps within that finite interval. The caller
must stay live through the interval, and every call entered between
the opened caller and the selected deeper entry
must return to its own frame before that endpoint. First returns are
reflected with their exact tuples and stores. The recovered prefix
selects the observed callable and arguments and reconstructs the
entire live stack. The linked regression computes 15 machine steps.
The helper enters at step 6 and returns at step 12. At step 15 the
recursive call is still poised to open, with state wire `8`, store
`21`, and the caller's state-changing suffix pending.

On a supplied infinite partial-machine stream, the
[first-child theorem](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/CallDescent/Extraction/Thms.lean)
selects the least later call whose frame stays live, when one exists
inside a live caller. Its earlier calls have first returns to their own
frames strictly before the selected entry. An earlier job that popped
after that entry would have to pass the selected live stack first.
The finite interval theorem then gives the exact independent prefix.
The linked fixture extracts the child at step 15 from an infinite
stream. A return to its saved frame would run the remaining suffix to
a terminal return, which contradicts the observed infinite steps.

The [complementary local theorem](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/CallDescent/Extraction/Theta/Thms.lean)
starts in a caller whose frame stays live and whose later calls all
return. It locates one live θ on the same stream and recovers its
successive completed feedback iterations. The first returns of the
θ bodies give the exact tuples and stores through partial finite
reflection. The linked regression gives an actual six-step cycle
per iteration, with one increment of the state wire and store on
each cycle.

### Divergence from a linked export

[The root equivalence](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Divergence/Thms.lean)
starts at an actual selected export with an empty stack and a specified
ambient store. An infinite machine stream keeps that initial call live
because a return to the empty stack cannot take another step. Iterated
first-child extraction either gives infinitely many independent call
prefixes or reaches a live caller whose later calls return. In the
second case the θ extraction also supplies an independent finite
route to the observed loop, retaining the same pending frames.

The resulting certificate uses typed call prefixes, successful partial
evaluations, and θ iterations. Its definition contains no machine
stream. Replay gives an infinite run of actual partial steps. A finite
path to a selected undefined primitive excludes such a certificate
from the same export entry. The linked fixtures check infinite φ
descent, a nested λ call whose θ feeds back indefinitely, and the
selected undefined arm. These results use the existing total linker
and δ initialization, with partial actions during invocation.

### Classifying partial invocation outcomes

[Progress and trichotomy](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Partial/Classification/Thms.lean)
classify the outcomes of a totally linked export with partial primitive
actions during invocation. Every intrinsically typed configuration
either returns to the empty stack, is blocked at a selected undefined
primitive, or takes another step. The typed control and total closure
resolver suffice for progress at every reachable state.

Exactly one independent outcome holds: a finite return with its tuple
and store, a finite block with its site and pending frames, or a
divergence certificate. Finite reflection recovers either terminal
derivation. If neither finite outcome exists, every reachable
configuration has a successor and an infinite trace supplies the
divergence certificate. Determinism separates the three outcomes.
This is a classical proposition about an invocation.

The same linked λ export exercises all three cases. Tag `0` returns.
Tag `1` blocks with the original partial primitive interpretation and
feeds back indefinitely with the interpretation that permits the
selected action. Linking and δ initialization retain their total
semantics throughout.

## Productive θ feedback

A feedback iteration consists of a finite `Returns` derivation for
the actual body and a selector requesting feedback. The derivation
starts with the full carried tuple and empty locals and supplies the
entire next carried tuple. A productive feedback run repeats these
completed iterations indefinitely.

`returns_iff_delimited` relates a finite job derivation to continuation
microsteps up to its first return to the supplied frame. The proof
attaches or removes the same outer stack on both sides of each local
step, so nested calls and loops keep their ordinary transitions.
`iteration_iff_segment` then matches one feedback iteration to
the actual body followed by its feedback edge.
[Definitions and finite correspondence](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Feedback/Thms.lean)

The stream theorem places every supplied carried tuple at a
successive restart of one actual continuation trace, with the same
saved parent. In reverse, supplied restart and body-return positions
and the first-return guard recover each finite body derivation. This
statement is about completed feedback iterations. A body that supplies
no finite return, whether it runs indefinitely or stops without
returning, supplies no feedback segment. The typed continuation
machine already rules out incomplete terminal states.

The linked regression adds an always-feedback variant of the θ body.
Each activation calls the linked φ member to completion and adds
`[4, 2, 5]` to state. Microsteps `6`, `30`, and `54` check the initial
iteration and the next two restarts with distinct full carried tuples
and the original parent frame. The fixture gives a finite derivation
for every iteration and exercises both directions of the stream proof.
[Linked fixture](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms'
```

## Infinite execution within a θ activation

`stays_iff_decomposes` takes an actual infinite continuation trace
starting at a θ restart. `body_decomposes` also accepts a stream
already at the freshly entered body. It prepends the actual entry
microstep so both statements use the same checkpoint convention.
The scope guard requires selector `1` at every return to the specific
saved loop frame. A finite exit followed by infinite parent execution
fails this guard. Nested frames still take their ordinary steps.

The extraction searches for the first return after each restart.
Determinism fixes the following restart and its entire carried
tuple. The result gives either unbounded first-return checkpoints
on the supplied trace or a finite sequence of such intervals ending
in a delimited infinite body suffix. The alternatives are disjoint.
Each completed interval recovers the independent finite body
derivation via `Interval.iteration`. Conversely, either decomposition
ensures that every return to the saved frame takes feedback.
`trace_of_iterations_then_body` also builds a scoped machine stream
from any finite sequence of feedback derivations and an infinite
delimited body stream. Both branches require a genuine microstep
at every index.
[Theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Feedback/Divergence/Thms.lean)

The regression keeps the linked productive feedback example and
extracts its checkpoints from the microsteps. A second linked driver
enters a body whose φ member calls itself with a pending non-tail
suffix. At step 24 the machine has two such suffixes waiting and
the argument state is `[1, 4, 1, 1]`. The proof uses typed machine
progress and finite adequacy to construct an infinite body stream
with zero completed feedback iterations.
[Linked fixtures](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms'
```

## Productive descent through non-tail calls

`Descent.Prefix` is an independent judgment over the real opened body
of a call. It uses finite `Returns` derivations for completed bindings,
follows the selected γ arm, and stops at a designated application with
its full callable and argument tuple. The saved suffixes retain their
entry arguments and the preceding local tuples. The callee's result
interface may differ from the caller's.

`Run.checkpoints` realizes a sequence of these prefixes as successive
entry checkpoints in one actual continuation stream. Each checkpoint
keeps the exact stack obtained by pushing the newly pending bindings on
the previous stack. `Run.stack_grows` proves that each opened caller
contributes at least one saved frame. Earlier completed jobs can use
calls and θ. The selected path can go through ordinary bindings,
selected γ arms, and θ bodies that are still active.

Under θ, the prefix records a finite sequence of completed feedback
iterations, including the empty sequence. Each iteration uses a
finite `Returns` derivation and its feedback selector. The full
carried tuple feeds the next fresh body. The selected call leaves
the θ frame in its original position among the pending bindings.

`entry_of_theta_interval` recovers a prefix and its exact saved stack
from two entries on an actual continuation stream. The caller must
remain live and each intervening call must return to its own stack
before the selected entry. The proof uses the first return of each
completed binding or θ body to recover its independent derivation and
the observed feedback. A θ activation may still be open at the selected
call. The existing `entry_of_interval` statement keeps its stronger
premise that intervening θ activations have also returned. These
results concern unbounded call nesting after finite feedback in each
prefix. Infinite sequences of completed θ feedback use the separate
feedback theorems.
[Definitions](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Defs.lean) ·
[Proof statements](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Thms.lean)

The ω fixture links a φ group with a returning helper and two mutually
recursive members. Each prefix calls the helper to completion, updates
the helper's value and state, then calls the other member before running
a nonempty suffix. At microstep 28 the active callable is the first
member again, with data `32`, state `[1, 10, 1, 20]`, and both distinct
suffixes pending with their own saved locals.

A second linked φ fixture starts each activation with a θ body that
feeds back once, appending `7` to the state. The restarted body adds
`8` before it enters a non-tail recursive call in the selected γ arm.
The regression checks fresh locals after restart and the ordered
stack at step 42. It contains both θ frames and six saved binding
frames, with argument state `[7, 8, 7, 8]`. The fixture also checks
the empty feedback prefix and reflects the first active-θ call interval.
[Linked fixture](../../../../tests/ssa/RVSDGRecursiveDescent.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveDescent.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms'
```

## Extracting the first live child or productive feedback

`split_live` starts at a real call on a supplied infinite continuation
stream. The call's saved frame must remain live, meaning that the stream
never reaches a return to that exact frame. The theorem derives the
checkpoints from the stream using a classical split on liveness.
It applies to linked φ members and to
ordinary linked closures. For a call started at the empty stack,
`split_start` derives root liveness from the infinite steps.

When a later call never returns to its own stack, the first such
entry is selected. A typed stack delimiter shows that each earlier
returning call must finish before the selected entry. Guarded reflection
then yields the independent prefix, with its exact typed arguments and
saved frames. The prefix includes any finite θ feedback on the way
to the selected application. The selected stack has strictly more
frames, and its liveness and actual entry position permit another
application of the theorem on the same stream.

If every later call returns, induction on finite region syntax uses
the actual node returns and selected γ arms to locate a live θ. A
live θ either yields unbounded completed feedback or reaches a
particular body activation that stays live. In the latter case the
proof continues inside that finite body syntax. The feedback result
gives actual restart positions and finite body derivations on the
original stream's suffix.

The proof uses the current deterministic machine. Each primitive is
a total typed tuple transformation that returns in one microstep,
with state threaded through its ports. γ takes a single selected child,
and linked calls resolve through the total typed resolver. Infinite
streams must take an actual step at every index. Primitive failure,
nondeterministic scheduling and finite stuck execution are outside
this classification.
[Public theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Completeness/Thms.lean)

The linked regressions supply raw streams with no call or restart
checkpoints. One invokes a φ export that repeatedly makes a non-tail
recursive call with a pending suffix. The other invokes a φ export
with an always-feedback θ and no deeper call.
[Linked fixtures](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveContinuations.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms'
```

## Classification from a linked root

`classify_linked` starts with the typed callable at an ω export, its
arguments, the empty stack, and the actual infinite microsteps. A
return to the empty stack has no following transition, so the trace
itself gives the initial live delimiter. The assumptions on total
single-step primitives and deterministic transitions are the same as
for `split_live`.

Each nested child continues at the least live call found by
`first_child`. It retains the independent finite prefix, including
finite θ feedback, and the exact typed stack at that position. A
nonempty finite chain strictly increases both the microstep index
and the saved stack depth. The global proof classically splits on
whether a finite such chain ends at productive feedback. When it
does, the final call and θ restart indices are on the supplied
stream. Otherwise coinduction chooses an endless chain of successive
least-child witnesses. `chain_checkpoints` chooses the independent
prefix witnesses to recover a single `Descent.Run` at those same
positions.

`calls_sound` runs the independent infinite-call certificate through
the existing simulation. The finite-call branch observes the route
from its final call to θ on the supplied trace. The independent
reaching judgment below reflects that route and replays it.
[Root theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Completeness/Global/Thms.lean)

The linked fixture starts at an exported λ that calls a φ member
and leaves its suffix pending. The classifier extracts a nonempty
finite chain ending at the φ call at microstep 3 and finds
productive θ feedback inside it. The trace supplies no chain
or restart checkpoints.
[Linked fixture](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Thms'
```

## Independent certificates for productive feedback

`ThetaReach.Reaches` describes a finite route to a selected θ restart
without a machine trace. A completed binding uses independent
`Returns`, including when the binding evaluates an application. A
selected γ arm receives its actual typed input. Entering a live θ body
after finite feedback records the exact carried tuple, fresh locals
and saved loop frame. The route can also choose a later restart of
the same θ. The pending bindings and loop frames preserve their
original order and port types.

`reaches_of_interval` recovers the route to the exact observed restart
and stack. It delimits the first return of every completed binding and
θ body. In the finite branch of the rooted classifier, all intermediate
calls return before the selected restart, because that restart's parent
frame stays live. `feedback_of_observation` then projects a finite chain
of the existing call prefixes followed by the independent θ route and
productive feedback.

`linked_iff` relates actual infinite continuation execution at a typed
ω export to either of two independent certificates. One is the
existing infinite call descent. The other uses the finite chain and
θ route to replay up to a selected restart, then stitches the
productive feedback steps. Completeness uses the classical rooted
classifier. The equivalence applies to the deterministic machine
with total single-step primitives and explicit state ports.
[Public theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/ThetaReach/Thms.lean)

The linked relay fixture constructs its certificate from the syntax
and finite return rules. The exported λ calls the φ member, which
completes one feedback body before the selected restart. The fixture
runs the certificate through the forward implication and uses the
original raw relay execution to exercise the reverse implication.
A second finite route checks a carried state of `[1, 4, 2, 5]`
after a completed feedback iteration with a linked return.
[Linked fixture](../../../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms'
```

## Demand through a static linked application

`StaticDemand.Code` is the compositional admission. It supports finite
primitive bindings, γ arms, and statically resolved applications, including
calls in callees and arms. Each application references a callee body and maps
its live entry ports through typed argument and capture wires. A single callee
can be used at multiple sites with different demands. The executable
`Code.liveIn` computes the corresponding shared `GenKill` least may solution.
[Compositional API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Thms.lean)

The application witness takes its callable from a typed entry port and
identifies the closure's captures with typed origins in the caller's entry.
`Code.Resolved` checks that identification against the actual closure. It
governs the callable slot, which the erased term still passes to `apply`. For
nested calls it requires the callee's own static targets to be resolved for
every formal argument tuple. The admission erases to the runtime's normal
numbered term. A γ checks the static targets of its arms for the capture
tuples wired from preceding locals. The default member index admits acyclic
calls. The singleton extension below admits one checked self-edge.

`Code.linked_runs_agree` starts from actual successful linkage at a common
store and relates the runner's demanded returns and exact stores, or its exact
typed blocked attempts and stores. The proof constructs matching transitions
from the checked code and produces a common settling budget. After a block,
the saved stacks can take a shared hypothetical result and store and continue
with the same guarantee, including at a later block.

The linked γ uses the native demand transfer. It applies the γ binding's
exit demand to each arm, joins their live captures through the typed wires,
and retains the selector. The runtime enters the selected arm with fresh
locals and a saved γ suffix. The proof relates the suffixes using the arm's
demanded results, including when a blocked callee is supplied a common
hypothetical result and store.

The γ fixture pins different capture demands for its calling and fallback
arms. At a block in the callee it observes three saved frames. After supplying
the same value and store to both invocations, the γ suffix returns demanded
value `60` and exact store `55`, even though the second exit differs.
[Linked γ regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/GammaRegression.lean)

The fixture applies one two-binding λ twice. The first call's computed result
feeds the second, which demands a different output port. The second probe
can block even though its computed data result is dead. The fixture also
resumes a saved stack from a first-call block and checks the later call.
[Compositional regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Regression.lean)

### θ feedback through static calls

Enable θ with the `loops` index of `StaticDemand.Code`. The native
feedback solver computes the least carried mask for the body summary. It
seeds the exit demand and continuation decision, and closes the mask through
the body's typed feedback result wires. At every restart, the proof relates
the carried values at those live ports. The resolution check may rely on
entry values that the body forwards directly through the same carried port,
including its linked callable and capture witnesses.

`Code.linked_prefixes_agree` compares actual runner observations at every
finite fuel. A return preserves demanded ports and the exact store. A block
preserves the exact typed attempt and store, and admits any desired observation
depth after supplying a common hypothetical result and store to the saved
stacks. Those stacks can continue through a restart or through the enclosing
suffix. Both runs are suspended at the same budgets, including when neither
has a finite endpoint. The `finite_return` and `finite_block` theorems
transport finite partial evaluation derivations through the same prefix
certificate using the runner's adequacy lemmas.

The θ fixture uses a seed that becomes live only through feedback. The first
probe advances the store to `22`, then the seed feeds a new request that blocks
after restart. Resuming at store `40` exits through an effectful suffix and
returns demanded value `50` and store `45`. Resuming at store `50` restarts
and reaches the same typed block at that store.
[Linked θ regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/ThetaRegression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Regression
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.GammaRegression
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.ThetaRegression
```

### Singleton recursive φ

`MemberSummary.live` supplies monotone demand summaries for a single
member's captures and formals. A `Code.memberCall` passes the demand from
its result users to that summary and maps live ports through its typed
argument and capture wires. `Singleton.closed` checks that the supplied
summary covers the body's shared `GenKill` liveness at every demand.
The self reference is admitted as a static call target.
[Singleton API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Singleton/Thms.lean)

`Singleton.Ready` checks the member's actual λ capture wiring and requires
every recursive call to resolve to the group's member with the witnessed
captures. The proof uses a real dispatch step before reusing the summary at
a smaller observation depth. `Singleton.calls_prefix` works at every depth
and feeds the existing finite return and blocked derivation theorems.
`linked_prefixes_agree` compares the actual linked runner at any fuel and
arbitrary observation depth after resumption. It preserves typed attempts,
exact stores, demanded results, and absence of a finite endpoint.
Mutual recursion, dynamic target selection, and synthesis of a joint least
summary are outside this admission.

The fixture passes a demanded payload only through the recursive edge and
varies a dead argument. It checks an effectful non-tail return, a probe
blocked after descent at store `22`, and resumption through the saved
frames to store `60`. A separate input repeatedly descends through the same
linked member. The regression proves productive execution for that input
using actual runner transitions.
[Singleton regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Singleton/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Regression
```

### Finite recursive groups

`StaticDemand.Family` takes a finite typed `MemberSummaries` table and
builds a linked φ group with an export for any chosen member.
`Family.closed` checks every body's shared transfer at every output demand.
A `Code.familyCall` names a member index and maps its summary through the
typed capture and argument wires. The suffix's reads of actual result
ports determine the callee's demand. `Family.Ready` checks that each
recursive target and its capture witnesses agree with the resolver's
actual member and λ capture wires. The family reference prefix is
reserved for static dispatch.
[Family API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Thms.lean)

`Family.calls_prefix` proves agreement at every finite observation depth
by consuming an actual resolver step before applying the induction
hypothesis to any member in the group. `Family.linked_prefixes_agree`
replays the linked runner. The shared prefix theorems give demanded
returns with exact store, exact typed primitive attempts and attempt stores
at a block, and observational agreement of pending suffixes under common
resumption. Suspension at every finite budget transfers in both directions.
Summaries are supplied. Joint synthesis and dynamic recursive targets
remain outside the admission.

The two-member fixture passes demand from the first result of A to the
second result of B and back to the first result of A. The unrelated result
varies while the payload and store agree. A zero capture blocks after both
call edges, and resumption runs both saved non-tail suffixes. A separate
input productively alternates between the same two linked members.
[Family regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Regression
```

### Synthesizing recursive summaries

`Family.Template` keeps the typed bodies and link wires before closure
is certified. `MemberSummaries.signaturesOnly` supplies the member order
and signatures for writing those bodies. The solver starts with an
empty table. Each round evaluates the existing shared GenKill plan,
including γ capture selection and the native θ feedback iteration.
Static calls use their witnessed capture and argument wires to
translate the callee row selected by the suffix's result demand.

The table uses a finite set of bits indexed by member, an output mask,
and a position in the member's captures and formal arguments. Lookup
joins subdemands during iteration so that even a candidate with
nonmonotone rows induces a monotone callable summary. At the fixed
point the rows themselves are monotone and lookup equals the exact
selected row. Only signature positions need finite enumeration and
decidable equality. Runtime values and primitive meanings need
neither. The solver materializes each round and stops at the first
stable table. The height bound counts the available bits, which grows
exponentially with output arity.

`Template.synthesize_isLeast` gives closure and leastness in the
finite table order. `Template.synthesize_le_supplied` also compares
the inferred reads with any supplied monotone transfer closed on
the finite rows. `Template.admit` checks that the full output demand
leaves the recursive reference prefix dead as data. The existing
`Ready` premise still checks the actual static targets and typed
capture witnesses. `Template.linked_prefixes_agree` uses the inferred
summary with the same partial runner and saved-suffix agreement.
Dynamic target selection remains outside this admission.
[Synthesis API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Synthesis/Thms.lean)

A variant of the two-member fixture seeds demand at A's second result
in round one. Round two carries it to B's second result and round
three carries it back to A's first result. The spare input stays dead
even at full output demand. The linked runner returns payload `41`
at store `46`, blocks on the zero capture at store `24`, and returns
at store `70` after both saved suffix effects run on resumption.
[Linked fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Linked λ consumers of a φ family

`Family.Wrapper` builds a linked λ over an earlier φ binding.
The leading λ capture is a typed output wire of that binding. Additional
captures use the same linker scope. At a checked application, the
ordinary reads flow through the actual capture and argument witnesses
at the demand induced by the suffix's result wires. The wrapper uses
`Code.liveness` and has no supplied λ summary. The fixture uses the
synthesized φ summaries from `Template.admit`.
[Linked λ/φ precedent](https://github.com/hiloopai/silmaril-lean/pull/3512)

The callable's link edge is a dispatch dependency. `Wrapper.Ready`
checks each target against its actual linked member and matches its
capture witnesses to that member's real captures. A dispatch-only
callable need not be equal across the compared executions. Uses of a
callable as data still create ordinary live origins. The admission
covers static targets in one checked group.

`Wrapper.linked_prefixes_agree` applies the actual partial runner to the
two-binding graph. It preserves demanded return values, exact stores,
and the typed attempted primitive and store at a block. The saved
suffixes agree observationally after a common primitive result and
resumption store. `Family.lambda_calls_prefix` also accepts an actual
closure body and captures at the post-link store for other link layouts.
[Wrapper API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Wrapper/Thms.lean)

In the linked fixture, requesting the λ's result makes a formal payload
live through the earlier φ call. Empty demand removes the payload read,
while the selector input and the potentially blocking capture stay live.
Varying the spare formal preserves the result `41` and store `56`.
A zero capture blocks at store `24`, and resumption runs the two φ
suffixes and the λ suffix to store `80`.
[Linked fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Ordered static λ bindings

`Ordered.CheckedPrefix.seed` gives the slots of a checked φ family their
existing summaries and transport proof. `addLambda` checks the new λ's actual
capture wires against the shared table of typed linker positions. It computes the
new summary with the shared GenKill plan and checks static dispatch through
the supplied `Binding.resolved` proofs. The λ's table-indexed calls can
name only earlier slots. Its new logical slot and physical linker position are
recorded separately. Callable captures used for dispatch may be absent
from the ordinary live-input set. [Ordered link admission](https://github.com/hiloopai/silmaril-lean/pull/3585)

`Binding.link_step` matches one actual linker step. The demand certificate
for the new entry accepts an arbitrary related saved suffix and calls
the earlier transport proof for earlier slots. Once the actual export
and common post-link store are identified, `Dispatch.linked_prefixes_agree`
compares demanded returns, exact stores, typed blocked attempts, and the
suffix observations after common resumption. This admission uses a
φ seed and ordered λ additions. It takes static resolution proofs and
successful-link evidence from the caller. Dynamic targets and automatic
discovery of the ordered prefix are outside this admission.
[Ordered demand API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Thms.lean)

The linked λ→λ→φ fixture uses a synthesized seed and two uses of
`addLambda`. The later λ reads both the earlier λ's linker position and
the earlier φ member as a capture witness. Result demand flows across
both applications and leaves the spare formal dead. The actual export
returns `41` at store `66`, blocks at store `24`, and resumes through
both λ suffixes and both φ suffixes to store `90`.
[Linked fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Checking a whole linked demand prefix

`Ordered.Prefix.Plan` follows the typed module tail after a checked φ
seed. It admits selected λ bindings with `addLambda` and leaves skipped
positions empty in the existing typed linker table. Each checked binding
can supply a local body-resolution proof or request the direct-call
check. The fold constructs the intermediate
membership tables, attaches the computed summaries, and uses the existing
linker equations to identify both successful link results and the final
export's captures. `Export.linked_prefixes_agree` consumes that result
directly.
[Whole-prefix API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Thms.lean)

This slice compares two links of the same φ/λ module with a common
initial store and exports the last checked λ. The
λ→λ→φ regression uses the direct-call check for both checked bindings and retains
its demand, return, block, and resumption checks. A second plan links
a same-signature copy of the first λ at a skipped position and
redirects the last λ's capture there. The runner can call that copy,
while admission rejects the unchecked position. It also rejects a site
that takes its callable from a formal input.
[Linked fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Running backward demand on a numbered λ export

`Plan.analyzeNumbered` takes a typed numbered `Omega` and a demand plan
for its exact recovered source. The layout starts with a checked φ
family and ends at the final checked λ. `Plan.phi` admits another
independently checked family in link order. Both runs use the same numbered
module and initial store. The caller supplies the source correspondence
and readiness for each family's actual captures. The prefix checks can
reject a plan when callable membership or local resolution fails.

Each added family contributes disjoint demand slots and reuses its own
closed summaries and saved-suffix transport. The step checks the group's
actual outer wires against the existing typed membership table. Later λ
bodies can call members from either group with supplied static resolution.
The extra φ step starts a fresh set of inference routes for subsequent λ
bindings. A use of a callable defined before that step therefore needs
supplied resolution. Use `Plan.phiWithEarlier` when the later group's
own bodies also call earlier checked slots. The later family supplies
summaries closed under its body transfer using both the earlier summaries
and its own recursive slots. The readiness proofs resolve actual member
operands and capture witnesses for all formals. The finite-prefix proof
uses the earlier dispatch certificate for earlier calls and its
smaller-depth induction for calls within the new family. This admits
static calls within each group and backward across link order.

Use `Family.CallTransfer.withEarlier` to synthesize the later group's
summaries. Each round holds the already checked earlier summaries fixed
and updates the later family's rows for every output mask. The existing
finite solver proves the least pre-fixed table for this combined GenKill
transfer. The height bound counts only the later group's input bits,
though the number of masks still grows exponentially with output arity.
`Template.admitWithEarlier` installs the computed table and its closure
proof. `Plan.phiWithEarlier` still checks the actual linked capture
positions and uses supplied typed resolution.
[Ordered synthesis API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Groups/Synthesis/Thms.lean)

To compute each group in link order, write it as a
`Scope.GroupTemplate` and use `Scope.synthesizeGroup`. The template
gets the earlier table from the current scope. Each admitted group
extends that scope with its computed summaries and typed member
positions. Use `Plan.analyzeNumberedFromOrdinary` to start at ordinary
imports with an empty dispatch and admit λ and φ bindings using the
existing plan. This entry point covers the plan's λ/φ fragment.
[Ordered template API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Synthesis/Defs.lean)

For a numbered module with one leading δ, use `DeltaPrefix.check` to
run both initializations and obtain the exact typed result row on each
side and a common post-link store. `Plan.analyzeNumberedAfterDelta`
runs the same source-indexed λ/φ walk from that store and certifies its
results against the original numbered link. A blocked initializer or
unequal post-link stores fail prefix admission. The initializer adds
no callable summaries. The existing typed capture check recognizes
ordinary initialized globals by type and checks callable positions as
before. This entry point analyzes the exported invocation after
initialization. Interleaved δ bindings remain outside it.
[Leading δ API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Delta/Thms.lean)

The δ→φ→λ fixture uses a synthesized φ summary for the member that
reads the initialized global. The export calls the actual member and
passes the same global as its capture witness. The probe keeps that
global live under empty demand. Varying the dead formal preserves
exact return, the typed block and resumption through the λ's saved
suffix. A same-payload global from another vertex fails the witness
equality.
[Leading δ fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Delta/Regression.lean)

For repeated initializers, `LinkedRemainder.start` indexes the actual
numbered link by the remaining source. `checkDelta` runs the next δ
against the current typed locals and store on both sides. On success
it appends the initialized rows and carries the callable dispatch
unchanged. The returned scope is available for the next step, including
group synthesis. `addGroup` reuses the checked group admission and
`analyze` runs the existing demand plan on the remaining λ/φ suffix.
Each δ must succeed at a common post-step store. The δ initialization
itself is outside the invocation liveness guarantee.
[Composable prefix API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Remainder/Thms.lean)

The interleaved δ→φ→δ→λ regression reads the first initialized
global in the second initializer and reuses the φ dispatch after
the second δ. It checks both initialized captures are live under
empty result demand, exact return and resumption, and rejection
when the received stores diverge at the second initializer.
[Interleaved δ fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Delta/Regression.lean)

The cross-group fixture starts with a λ and synthesizes both groups'
summaries in order. The exported λ calls the second group and then
uses the leading λ for its saved suffix. The second group takes a
member of the first from a typed capture, recurses once, then calls
that member. GenKill makes the payload formal live only when the
export result is requested. The blocking capture and recursion counter
stay live even with empty result demand. Varying an unrelated dead
formal preserves the exact return, the first group's block, and the
resumed return through both non-tail suffixes.
[Cross-group fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Groups/EarlierRegression.lean)

`GraphPlan` and `admitGraph` certify paired numbered runtime behavior.
That certificate has no demand-indexed summaries, so the analysis uses
the per-family demand certificates directly. The two-group regression
uses both public entry points on the same numbered module and checks one
live data capture per group, a dead formal, and exact return, block and
resumption through the λ suffix.
[Two-group fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Groups/Regression.lean)

The successful result exposes the existing `GenKill` problem through
`problem`. Its executable `liveIn` list agrees with the least `mayOut 0`
solution. Use `liveCapture` and `liveFormal` to query typed inputs and
`ExportAnalysis.linked_prefixes_agree` to consume these facts in the
actual runner. Callable dispatch evidence stays in the checked link.
The numbered θ/γ fixture consumes the formal facts, varies a dead input,
and checks exact return, block, and resumption. The swapped θ backedge
fails the same public admission.
[Numbered demand API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Thms.lean)

`ExportAnalysis.substituteDeadFormals` consumes these facts to prepare
invocation arguments. It chooses the original value at each live port
and the proposed replacement at each dead port of the same typed tuple.
`linked_substituteDeadFormals` preserves the runner's observations at the
chosen demand when the live captures agree. The θ/γ fixture proposes new
values for all three formals, substitutes only the spare, and exercises
the transformed invocation through return, block, and resumption.

### Analyzing a numbered client with a checked provider

`analyzeAllocatingClient` takes a checked numbered provider and an
`Export` demand receipt for those same provider links. It checks the
client's head import against the actual closure, seeds static dispatch
from the receipt, and starts the client initializer at the provider's
common post-link store. The client is one unshifted δ→λ in a distinct
unit. `Scope.Checked.addInitialized` appends the two initialized rows
when both runs reach the same post-initialization store. The client λ
supplies typed static body resolution for those rows.
[Provider composition API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Provider/Thms.lean)

The fixture uses a provider λ that probes its initialized capture and a
client λ that probes its own global after the provider call. The public
analysis keeps both probe inputs live even at empty result demand.
Substituting the client's dead formal preserves the exact return, the
typed provider block, and resumption through the client suffix. A
same-signature import with a stale capture fails admission.
[Provider composition fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Provider/Regression.lean)

### Looking up demand indices in a checked provider assembly

`CheckedProviderAssembly.lookup name ty` returns a `LookupReceipt` indexed by
the assembly, name and requested port type. Its `values` projection supplies
the exact left and right closure with membership in the accumulated dispatch
families. `LookupReceipt.values_left` and `values_right` identify these
values with the original exports at the requested type.
`LookupReceipt.checkImports` can certify equality when a client already
has materialized imports.

`LookupReceipt.entry.provider` retains the original
`CheckedProviderReceipt`, including its typed `port`, full `outcomeL` and
`outcomeR`, and `chain.checked.linkedL` and `linkedR`.
`CheckedProviderReceipt.selectedL` and `selectedR` are singleton outcomes
at that provider's own post-link stores. With a summary for `provider.fn`,
use them as the indices of `Export actions summary` for the selected
closure. The lookup supplies the indices and exact import values. The demand
certificate still supplies the summary, static dispatch and common-store
evidence. These projections read stored link results.

`matchNamedExport` checks that an existing demand receipt belongs to
the selected closure and its original store on each side. Use those
equalities to reindex the receipt as a `NamedDemand`. `NamedImports`
combines the checked dispatches in typed import order and checks the
materialized tuple with each name's `checkImports`. The allocating
entry point takes a successful client initializer receipt at the
assembly's common final store and returns the usual `ExportAnalysis`.
Client resolution can be supplied explicitly or inferred from the checked
named imports with `NamedImports.analyzeLayoutsDirect`.
[Named provider demand API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Provider/Named/Thms.lean)

`NamedImports.analyzeLayouts` accepts independent typed initializer and
capture layouts for the same λ body. It checks each import against its
actual named export, reads the captures from the corresponding successful
initializer row, and computes one GenKill summary. The two rows share a
post-link store. This entry point takes static resolution for each side.
Pass the resulting receipt for both sides of
`ExportAnalysis.relocated_substituted_starts` with the existing related-link
and dispatch certificates. The two-provider fixture moves the second
provider and client allocations to vertex 1 on the right, checks exact
return, typed block and non-tail resumption, and rejects the stale provider
closure with the same payload from vertex 0.

`NamedImports.analyzeLayoutsDirect` follows the typed call target and
witness wires in each layout through the existing direct provenance
checker. The call's static slot must correspond to the exact named import
position selected by its target wire. The projected witnesses must match
the capture values of that provider's checked dispatch receipt. The supplied
exact-value checker must cover both the imported closures and the witness
value types. The same provenance check handles supported forwarding.
Computed or untracked targets and mismatched witnesses are rejected.
The same two-provider regression uses inferred resolution, and also
rejects a call wired to the other same-signature import with both named
imports correctly loaded. The common store and single client allocation
requirements still apply.

`LookupReceipt.entry.traceL` and `traceR` are
`AllocationHistory.Segment` witnesses with exact entry and exit stores.
Use `AllocationHistory.Segment.reassemble` with the provider's own
`chain.historyL` or `historyR` to recover the full trace. The witnesses
cover certified links in disjoint allocation histories. Opaque allocations
and shared ancestors are outside this interface.
[Typed provider lookup](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/Isomorphism/RecursiveCall/Numbered/Admission/Prefix/Graph/Import/Allocation/Thms.lean)

### Analyzing relocated allocating layouts

`AllocationPlan.analyze` also accepts the allocating layout with an empty
φ before δ. It rebuilds the typed demand scope from the actual linked δ
row. `AllocationPlan.analyzeImported` checks each head import against a
provider demand receipt for its own numbered links. The outer capture
wires may move while the exported λ uses the same demand summary.

Use `ExportAnalysis.relocated_substituted_starts` with two such receipts,
the existing related-link evidence, and `admitAllocatingClient`'s dispatch
certificate. Related original and replacement arguments yield related
substituted starts. The linked family transports returns and blocks at
exact stores. `relocated_resume` reuses the reached related frames with
typed, related, admitted response packets at a common store. The fixture
moves both allocations from vertex 0 to 1 and checks exact success, block
and resumption in both layouts. The right client rejects a same-payload
provider closure that still captures vertex 0.
[Relocated allocation API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Analysis/Provider/Relocation/Thms.lean)

### Synthesizing direct call resolution

`Plan.lambdaDirect` and `Plan.finishDirect` construct the existing local
`ResolvedWith` proofs for direct captured calls. The checker projects the
typed call operand and capture witnesses through the λ's capture wiring
and composes that partial map through nested γ boundaries.
It compares their linker addresses with the stored sources for the
specified slot and checks callable membership at the actual position
in both runs. Matching typed addresses imply equality of the wires.
At each γ, the checker follows the actual argument wires and certifies
every arm and the suffix. The number of arms is the `Code` layer's
`extra + 2`. The certificate covers every prior local tuple. Untracked
child ports can still carry ordinary inputs and results.

The φ seed can describe member capture witnesses that project directly
through its outer context. The checker rejects missing source descriptions,
formal callees, and computed origins for callees or capture witnesses.
Inline closure descriptions use the explicit plan constructors with
supplied resolution proofs. Invocation uses the same linked runner.
[Direct resolution API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Direct/Thms.lean)

`synthesize_complete` proves success for a direct forwarding derivation
whose call sites match the supplied slot sources and paired checked
membership. The whole-prefix fold also checks each binding's admission.
[Completeness theorem](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Direct/Completeness/Thms.lean)

The linked fixture reorders captures through a ternary γ and then through
a binary γ in its first arm. The runner checks every branch choice,
including typed probes and resumption through both nested suffixes. The
spare formal stays dead. Substituting a same-signature φ target from the
wrong linker position rejects admission even when the affected inner arm
would be unselected.
[Linked γ fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Tracking captured calls through θ feedback

At θ entry, the checker follows the actual input wires and keeps a
carried origin only if the corresponding body result is wired straight
back from that same port. `feedback_return_reads` proves that every
returned body packet preserves those reads by `Code.Forwards`. The
linked runtime theorem carries those equalities through each restart,
including after resumption. Untracked ordinary state may change, and
inference checks the suffix under its enclosing boundary.

The linked θ fixture changes a counter on the first iteration and calls
a captured φ member on the second. With the spare input dead, the runner
returns, blocks on a typed probe, and resumes through both effectful
suffixes at exact stores. Swapping two same-signature callables on the
backedge rejects admission, even with the right target on initial entry.
θ bodies that need computed or permuted origins for call operands still
use supplied resolution proofs.
[Feedback and checker API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Direct/Thms.lean)
[Linked θ fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Tracking callable results at a γ join

`Code.callAt` accepts typed local result wires as well as entry
arguments. At a γ, the checker tracks an output only when every arm's
return wire projects through the boundary to the same typed linker
origin. It checks the slot and each capture witness separately. Different
same-signature slots and computed callable results fail inference.

The linked proof uses `Code.Forwards` from the selected arm to supply
the suffix's resolution at the actual returned values. This includes
the arm's returned values after resuming a blocked primitive. The
fixture forwards the same target and witness through distinct arm ports,
calls through the joined results, and keeps an ordinary argument dead.
It checks exact returns and resumption after blocks in both the arm and
the suffix. Changing the target in an unselected arm rejects admission.
[Join checker](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Ordered/Prefix/Direct/Thms.lean)
[Linked join fixture](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/StaticDemand/Family/Regression.lean)

### Single-call admission

`DirectCall` admits a two-λ module by construction. Its exported caller
captures the linked callee and invokes it at an actual application node. The
callee executes one primitive before returning through wired results. The
caller forwards selected results and may also return its own arguments.
The admission uses only λ vertices and this single static application.
Dynamic targets, recursive calls and partial initializers are outside it.
[API](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/Demand/Thms.lean)

The requested caller results select the callee result demand. The shared
least may solution identifies the live entry ports of that callee. The
analysis maps them through the actual capture and argument wires, and keeps
the caller arguments read directly by a demanded result.

Agreement on those imports and arguments, with the same initial store,
preserves demanded returns and exact store after ten invocation microsteps.
A block retains the exact typed primitive site, operands, and attempt store.
The saved stacks are related by what their two return suffixes do when
supplied a common hypothetical primitive result and store. Those stacks can
contain different dead values. The regression resumes a suspended invocation
and checks a block with two saved frames. Changing the live capture at that
same call makes the primitive return and change the store.
[Regression](../../../../Silmaril/Proofs/SSA/RVSDG/Interprocedural/Runtime/Recursive/PartialLink/Demand/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Regression
```

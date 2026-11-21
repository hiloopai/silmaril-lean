# Relational determinism and checked fuel

`Silmaril.Semantics.Operational.Determinism` adds policies to `WithUB` without
changing `HasOpSem`, or making an executable selection the source of truth.

## Default: unfuelled relations

Use `step`, `Reach`, `May`, and (for infinite primitive paths) `Diverges` on
`OpSem`. At a program entry use `HasOpSem.May` and `HasOpSem.UBReachable`; neither
takes fuel. These are existential relations, not a choice of strategy. Fix the
actual host and numeric profile when choosing a Core model; determinism and
extra UB policies are opt-in properties or transformations.

## Optional budgets and policies

- [`Determinism.Fuel.Thms`](../../Silmaril/Semantics/Operational/Determinism/Fuel/Thms.lean)
  is the optional import for bounds. `StepsN.reach_iff_exists` and
  `OpSem.may_iff_exists_stepsN` say that unfuelled finite reachability and
  outcomes are exactly those with a finite primitive-step count. The count
  witnesses any at-most budget greater than or equal to it. This requires no
  determinism, oracle, or safety premise. Counting primitive relation steps
  is not the same as counting instructions in a normalized or typed evaluator.
- `StepDetAt` is immediate successor uniqueness; `DetFrom` additionally requires
  immediate observation uniqueness at every reachable state. Neither says that
  any successor or observation exists. `ResultDetAt` compares complete finite
  outcomes. `NonTrapDetAt` means at most one non-trap payload, not “either every
  path traps or every path returns”; a trap can coexist with a unique payload.
  For Core, a non-trap payload also includes uncaught exceptions, not just
  successful returns. A different `ViewDetAt` can retain traps or compare only
  successful values. `Labelled.TraceDetAt` compares complete finite visible
  logs *and* outcomes, not all prefixes or infinite streams.
- `requireLocalDet` blocks primitive ambiguity at the offending state; it can
  reach UB after a nonempty prefix. `requirePrefix` tests every original prefix
  at the source and may instead report immediate UB. They give the same safety
  verdict for a common local test, not necessarily the same retained prefixes.
  `requireViewDet` rejects disagreement in the selected finite observation
  view. Those guards are policy, not properties of the Wasm standard. The policy
  relation only removes ordinary edges/observations and recovers all of them
  on its safe starts. The mixed `Permits` order admits more ordinary behavior
  and less immediate UB; unlike uniform relation inclusion, its join takes the
  union of ordinary behavior but the intersection of UB. Neither is the
  guarded `SafeRefines` preorder.
- `Oracle` is a sound certificate-backed choice, which may leave alternatives
  in the relation. `guard` needs a supplied `DecidablePred`; it does not infer
  an ambiguity decision from incomplete search. `run_sound` returns bounded
  relational evidence, even on exhaustion. Exhaustion means a known next step
  at the budget boundary, not UB or divergence. Unknown is not certified stuck.
  `Oracle.may_iff_run` connects an outcome to some sufficient executable fuel
  under reachable determinism, terminal observations, safety, and an oracle
  that does not return unknown on the relevant reachable states. Without those
  hypotheses a finite trap path, for example, can be missed at every fuel by
  a selector which always takes the return branch.

## Actual Core boundary

`Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms` proves finite result
uniqueness at the actual `SingleThreaded.Det.profile oracle` with `noHost`;
the existing normalization theorem gives a stronger final-state equality.
Raw trap propagation may take distinct primitive paths. On a `ConfigFree`
start, every host-free Core path transfers between **any two** `Numerics.Profile`
values, so its finite result is unique even at a spec profile. This hypothesis
excludes numeric-profile-sensitive operations and includes stored functions as
well as current code. It is not a claim that every `Profile.spec` is
deterministic. The regression exhibits two distinct admissible f32 NaN return
bit patterns at `Profile.spec nd` for either `nd`.

`normalOracle` uses the landed intrinsic numeric/local machine and
`State.raw_may_iff_bounded` connects finite observations in actual policy-gated
Core to a finite execution at some intrinsic fuel. The budgets are not raw
primitive-step counts. `driverOracle` takes an explicit soundness premise on
the actual Core driver; it reports unknown if neither the driver's step nor
its outcome classifier succeeds. It does not assert raw primitive uniqueness
or classify host callouts as UB.

The definitions are independent of the version tags and ISA feature tables.
Applying them to a SpecTec interpretation needs a verified relation/observation
transfer for that dialect; a tag alone supplies no such theorem. A host/game
adapter must specify the log alphabet, what inputs are fixed, and how callouts,
answers, host divergence, and pending requests are observed. No trace or
determinism claim about those open systems follows from `noHost`.

## Closed Strict invocations with immutable structs

[`ClosedFunctional.Thms`](../../Silmaril/Wasm/Execution/Core/Entry/ClosedFunctional/Thms.lean)
proves a sufficient criterion at an actual ready Core invocation, not a new
syntax admission test. `Bodies` certifies that each allocated function is a
Wasm body with an erasure in the existing `FunctionalISA.Raw .immutable`
grammar. This covers `call_ref` callees as well as the initial function, and
permits integer operations, locals, structured control, and immutable struct
construction and reads. Raw and intrinsically typed syntax both give `IFree`
evidence; Core `ConfigOk` is a separate premise for policy safety and the
interpreter correspondence. The certificate does not constrain unrelated store
data.

At `noHost`, `finishes_unique` compares two finite Core executions from the
same `invoke` at **any two Core numeric profiles**, including both standard
`Profile.spec` choices. It proves equality of the complete final configuration
and of the result, including traps. This is stronger than uniqueness of just
non-trap results, and does not assert uniqueness of primitive steps or traces.
`finishes_iff_run` matches these executions to successful runs of the existing
Core interpreter for some finite fuel. `export_may_iff_run` uses actual named
export lookup and retains the final store in its witness. Neither theorem
classifies runs without a finite result as divergent or UB.

The [regression](../../tests/wasm/closed-functional/Regression.lean) checks
admission, validation, and instantiation of a closed Strict module that
allocates and reads an immutable struct, then either returns 42 through
`br_if` or traps on division by zero, depending on a typed argument. Both
paths retain the allocation; the trap is not UB. Conversely, the broader
closed Strict admission checker accepts a well-typed NaN program with two
different **non-trap** returned bit patterns for each standard spec profile.
For a wider GC fragment, the missing criterion is that all admitted bodies
(including callees in the allocated store) satisfy `IFree`, or a more general
step-transport invariant. The checked struct example requires no new GC rule.

Strict as a language can allow imports. This result is only for the **closed
Strict fragment** and does not extend by absence of memory or mutable GC. For
a fixed host, a determinism extension needs a fixed initial environment and
unique answers to each reachable call (including next environment, store and
result, and whether divergence is an alternative). Typing preservation is
needed for safety, and preservation of profile-free code for cross-profile
transfer. For an open labelled semantics, specify a fixed incoming response
schedule or a projection of the visible log before formulating a uniqueness
claim; allowing all input choices is not a deterministic handler.

These theorems compare numeric profiles within the same Core reduction
relation. Applying them to a native version or SpecTec interpretation requires
the exact state and observation transport for that route (see the
[version theorem guide](https://github.com/hiloopai/silmaril-lean/pull/1370));
a checked syntax injection alone proves neither behavioral equality nor
linking closure. Fixed memory remains the existing one-page profile: changing
the page count needs a generalized valid memory instance witness and a proof
that replacement of bytes preserves its length and typing.

Run `make check CHECK_TARGETS=+Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional.Thms`
for the scoped checks.

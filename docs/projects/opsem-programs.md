# Operational program comparisons

`HasOpSem Program State Obs` is the only entry-bearing model. Its `initial`
relation describes entry in context, and its `WithUB` describes actual states.
It does not require total or unique entry. Use `Outcome (Except Error Result)`
when a language exposes both values and errors: `.returned (.ok value)`,
`.returned (.error err)`, and `.trap` are three different observations. A
missing entry is `NoEntry`; `WithUB.Stuck` is an unclassified, non-UB state
with neither a move nor an observation. Neither implies an infinite path.
Open host requests need their own observable interface rather than being
interpreted as UB or an error by default.

Start with `model.May program outcome` and `model.UBReachable program`. At a
particular state use `step`, `Reach`, `May`, or `Diverges` on the model's
`OpSem`. No fuel is needed to state these judgments, compare programs, or
validate an entry. Use the separate [fuel API](opsem-determinism.md) only to
measure a finite witness or execute a checked selector.

[`Program.Thms`](../../Silmaril/Semantics/Operational/Program/Thms.lean) adds:

| Operation | What it means |
| --- | --- |
| `precompose` / `restrictPrograms` | Change the input syntax (e.g. erase a proof-carrying term) or select admitted programs. No change to execution policy. |
| `restrictStates` | Select a subtype of states; can drop crossing steps. Backwards readback needs closure; use the existing `WithUB.restrict_readback`. |
| `.semantics.toOpSem` | Forget UB, leaving all ordinary steps and observations, even from unsafe starts. |
| `safeFragment` | Select states that cannot reach UB. This subtype is closed and its finite outcomes are exactly those from the original safe entries. |
| `mapObservations` | Interpret returned values and explicit errors in a common alphabet; keeps traps and UB. Compatible with `precompose` and preserves `Refines` under a shared map. |
| `SameFinite` | Equality of finite observation sets, not trace or step equality. |
| `UBRefines` / `Refines` | No new reachable UB, and (for `Refines`) unconditional inclusion of finite outcomes. |
| `Equivalent` | Mutual `Refines`, exactly `SameFinite` plus equivalent reachability of UB. |

For erasure between machines, pass their state relation to the existing
`OpSim` and match **every** implementation entry with a specification entry.
`refines_of_sim` transfers finite outcomes and possible UB forward. A reverse
simulation needs its own step, observation, UB, and initialization evidence.
Stuttering simulations need not reflect divergence; finite equivalence need
not reflect missing entry or stuckness. Observer projection is a proved
compatibility rule, not contextual congruence under linking. `OpSim.id` and
`OpSim.trans` already provide identity and composition with relational state
composition; no new category or institution is implied here.

Primitive meet/join use [`WithUB.Included`](../../Silmaril/Semantics/Operational/Policy/Thms.lean).
Mixed policy approximation and guarded safe refinement have distinct meanings;
see [determinism and fuel](opsem-determinism.md). `DetFrom` is primitive
uniqueness on reachable states, and `NonTrapDetAt` is uniqueness of non-trap
payloads (including explicitly observed errors); possible traps do not violate
the latter. Use `Oracle.run_sound` and the finite completeness theorem with its
reachability, terminal, determinism and coverage premises. Fuel exhaustion or
an unknown choice is not evidence of UB, stuckness or divergence.

Run `make check CHECK_TARGETS=+Silmaril.Semantics.Operational.Program.Thms`
for the regression and axiom audit.

## Coverage at Wasm entries

| Boundary | Checked statement | Outside the statement |
| --- | --- | --- |
| Core module vs. checked raw module | `checkedModule` restricts the syntax domain at `ModuleOk`, `StoreOk` and typed import addresses. `checkedModule_erasure` commutes with erasure before execution. | Binary encodability, feature admission, import name resolution, and success of initialization. |
| Intrinsic Core module vs. checked/raw | `typedModule_erase` and `typedModule_readback` use the state relation `typed.val = raw`; `typedModule_equivalent_raw` matches initialization in both directions and checks `HostOk` for readback. It uses actual Core preservation, with no host-determinism or fuel premise. | An independent typed evaluator for arbitrary segments or start; publication of a ready instance still needs `ReadyAfter`. |
| Resolved Core integer/local export | `ResolvedExport.equivalent args` compares unfuelled outcomes and reachable UB of the intrinsic body and actual named raw `invoke` at `profile oracle` with `noHost`. There is no UB on either side. Its proof supplies the structural budget; `equivalent_of_runFor` is the auxiliary theorem for clients with their own finite typed witness. | Other body languages, open imports, arbitrary profiles, and path equality. `invoke_finishes_iff` is the stronger readback that also retains frame and store. |
| V1 scalar syntax → Core entry | `wasm1Scalar_core_entry` says native V1 erasure then injection and direct intrinsic emission select the **same** actual Core initialization and policy for a supplied store with no import arguments. | This is not a statement about the source’s native operational semantics or a feature-lattice map. |
| Native Lime | The existing [`lime1_core_beh`](../../Silmaril/Wasm/Models/Lime1Core/Thms.lean) maps observations of native invocations **into** Core at `Profile.spec`. It needs `StoreWF`, `HostPreserves`, `HostKeepsL`, and an allocated address. The atlas embedding uses direction `.sub`. | No backwards reflection, UB transfer, or equality of features: Core's rewritten table/element syntax can fall outside `ValidIn lime1`. |
| Ready scalar leaf / component | The existing [`session_finishes_iff`](../../Silmaril/Wasm/Execution/Core/Entry/Thms.lean) covers the observed store-retaining, import-free, matched activation. The [registered game bridge](wasm-intrinsic-denotation.md) separately interprets linked intrinsic Core exports, including open import moves under its stated environment and store hypotheses. | No whole-component execution equivalence. It needs a relation on the actual deployed stores, preservation after each round (including traps), and matching requests, responses, pending prefixes and divergence. A type-checked wiring or deployment certificate alone does not supply that proof. |

[`Entry.Program.Thms`](../../Silmaril/Wasm/Execution/Core/Entry/Program/Thms.lean)
imports the established entry and validation proofs. The separate
[`Entry.Program.Versions.Thms`](../../Silmaril/Wasm/Execution/Core/Entry/Program/Versions/Thms.lean)
uses the landed V1 intrinsic syntax and `ClosedModule.toCore_eq`; it requires
no dependency on the [version guide PR](https://github.com/hiloopai/silmaril-lean/pull/1370).
Keep version injection, Core feature inclusion, and runtime policy distinct.
If the model behind an institution changes, reuse its actual state and
observation transfer and specify which judgments are reflected or preserved;
the Core entry triangle proves no new institution morphism. The existing
`Pure.postEquivalent_iff` covers a specific linked numeric suffix test, not all
Core contexts or linked components.

The [Core regression](../../tests/wasm/module-entry/Regression.lean) checks
validated, initialized `divide` as checked raw and lifted intrinsic module
syntax, then compares typed and raw ready entry for every divisor. It checks
the relational return, trap, and failed lookup first, and separately checks
insufficient fuel using `runFor`. The
[version regression](../../tests/wasm/operational-program/Version.lean) observes
successful instantiation via both syntax paths under the triangle.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Execution.Core.Entry.Program.Thms +Silmaril.Wasm.Execution.Core.Entry.Program.Versions.Thms'
```

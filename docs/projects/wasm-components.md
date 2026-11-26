# Wasm components: wasm-tools components, jco, WAC, WIT and the generator API

The second part of the Wasm tooling. It adds the WebAssembly component model to the Lean
`wasm-tools`, Lean versions of jco (`wasm-jco`) and WAC (`wasm-wac`), a WIT tool, the
command-line specification API, and the program generator API. The core `wasm-tools` and the
Binaryen tooling are described in [wasm-binaryen-tooling.md](wasm-binaryen-tooling.md) and
[wasm-tools-trust.md](wasm-tools-trust.md).

## Checked Declaration Wiring

`Silmaril.Wasm.Component.IntrinsicWiring` is an indexed builder for a flat
fragment of the reference component AST. Each step advances the actual
`DefState`. Core payloads supply the named module interface; instantiation,
aliasing, function type, canonical ABI, and re-export commands use the existing
reference checker. `Program.then` composes only fragments whose intermediate
scope agrees. `erase_nil` and `erase_then` give identity and composition in
the reference syntax; `erase_map` and `map_then` let a payload transformation
commute with erasure and composition when it preserves the accepted named
Core interface. `Program.sound` proves the actual `ValidComponent` judgment.

The regression links a typed provider exporting `get` to a typed consumer
importing `env.get`, then canonically lifts and exposes the consumer's `run`.
The erased program passes the reference Core 3.0 component checker. A missing
argument name and an out-of-scope provider instance are rejected. This is
scope-indexed **declaration** composition, not WAC composition of separately
closed components. Reference validation, not a new engine, supplies the
typing premises. The builder does not cover nested binders or resource declarations.

### Exact lift and typed exports

`IntrinsicWiring.Lift` seals a finished program as `Closed` at the reference
`ComponentType`. `Exposure` identifies an entry in that checked export table
by position, name, and actual entity type. `Closed.lift?` reconstructs the
indexed steps from reference syntax; its success certificate erases to the
input exactly. `Program.lift_erase` and `Closed.lift_erase` give the other
direction. This is a retraction on the supported declaration fragment, not
completeness for the full reference checker. In particular neither nested
components nor export ascriptions are silently stripped. `Closed.erase_map`
commutes with raw `Syntax.Component.map` for a payload map preserving the
same named module interfaces under one component profile.

### Interaction trees for ready, closed simple components

Import `Silmaril.Wasm.Component.SyncITree.Thms` to observe a
`Reference.Simple` component through an interaction tree. `Ready.ofAdequate`
uses the existing instance witness and its initial Core store. The fragment
has one import-free Core instance, direct canonical lifts, float-free
interfaces and flat ABI arities. The recursive scalar, record and variant
types in `ValTy` exclude stream and future types by construction. The ready
instance excludes a Core start function. Component startup is outside the
tree, and the reference observation starts with successful instantiation.

`Question` checks the export index and argument types. Each normal reply is
checked against that export's result types. `exportSig` uses these as
dependent game questions and answers. `body` uses the existing abstract
Wasm `BodyM` and `BodyTrace.toAFun` observer. The definition reads terminal
Core/ABI judgements at a fixed deterministic Core profile without a fuel
parameter. A trap answers the current call and keeps its final store.
This follows the existing resumable reference-session extension, which
clears the reference machine's lockdown for the next call.

`completes_iff_reference` and `completes_iff_game` prove both directions for
completed typed rounds against the independent reference machine and the
component IR game. `pending_iff_game` also covers the finite play that
ends at the next typed export question. `quiet_iff_reference` identifies a
session followed by actual silent divergence. `noOutcome` distinguishes
absence of both a terminal judgement and an infinite internal run, and
never answers an export in the session observer. Productive infinite
sessions are outside this bridge.

The [downstream regression](../../Silmaril/Wasm/Component/SyncITree/Examples.lean)
observes `poke` trapping during its canonical lift after writing a global,
then `peek` returning the written value. It rules out the same observation
for the component that omits the write.

An open synchronous adapter needs to preserve typed import requests, host
replies and pending activations. When the concrete protocol permits callbacks,
the game position must retain the suspended invocation during reentry.
Supporting nondeterministic Core profiles also requires a component-side
choice model. This bridge has no import moves and fixes a deterministic
Core profile.

### Observation boundary

`Closed.terminal_iff` relates the stock reference-machine outcomes at an
exposed function to `IRObs` of the existing component game. It requires
exact erasure to a `Simple.toRef`, `Simple.Adequate` (goodness, float freedom,
instantiation with the intended instance, flat arities), typed arguments and
a terminating outcome. It uses the stock no-import reference host. The
regression projects the same typed `add` declaration from an intrinsically
typed Core body and from a native Lime1 payload. For the Core projection of
the Lime1 payload, an actual game answer `x + y` transfers to the reference
machine. This is not an execution theorem about the native Lime1 engine.

`Syntax.Component Lime1.Module` and `checkLime1?` already exist: this is
shared reference component syntax with native Lime1 payloads and the Lime1
extern interface, not a separate Lime component calculus. That checker
checks wiring and the structural module interface, not Lime1 module bodies.
`Syntax.Component.map Lime1.Module.toCore` instead targets Core payloads:
the example rechecks at the Core 3.0 profile, whose extern types and module
validation are different. It does not coerce a native checked interface into
the Core index. Removing the adder's result-producing body leaves the native
interface check successful but is rejected by the Core-projected checker.

The [institution guide](wasm-institutions-guide.md#scope-core-modules-and-components)
describes the existing `componentToGInst` on component IR. A syntax map alone
does not give the reduct for native reference observations or the
satisfaction condition. The ready-instance Core `Entry` API begins after
registration. For actual linked components, `Linked2.sessObs_eq` needs the
adequate wire and the corresponding importer/exporter instances, discharged
within `Linked2.sessAdequacy_full` for that class;
`HLinked2.sessAdequacy_full` also requires typed host handling and retains
the host run. Those linked results do not apply to the flat Core-module
wiring: its consumer imports a Core instance directly, not via the nested
components and canonical trampolines of `Linked2.toRef`.

The [flat wiring regression](../../tests/wasm/inductive-component/Regression.lean)
checks one runtime witness independently of `Simple`: reference instantiation
resolves `env.get` to the provider at Core address 0 and lifts `run` at address
1. The entire ready Core store agrees with sequential checked Core
instantiation from the empty store. The reference call of `run` returns
`u32 42` with the Core store of the unique deterministic terminal Core
configuration (`i32 42`). The same call is a complete Core scalar-game
activation; translating the store's host-code type preserves all its fields
and rejects host functions. A Core import resolved to a Wasm function is not
a game host move.

`DirectLift.terminalReadback` goes beyond this witness: it inverts any stock
terminal `Calls` trace from the existing one-owner `readyCfg` frame, not just
an interpreter trace. It needs a fresh call id, a reusable thread slot, a
name lookup in the supplied export table and a direct lift at the scalar
question's resolved Core address. The game instance must be well formed at
the shared store and have no host imports. The ABI is synchronous and
float-free, with default options, specification limits, at most 16 flat
inputs and one flat result, and no ABI memory or resource operations. Core
steps themselves are not required to preserve the store.

Readback gives `Entry.Finishes` and a store-bearing scalar-game `Activation`.
The final Core stores agree after renaming the host-code type. A reference trap
can reflect a Core trap, a Core throw, or a normal Core result rejected by the
ABI (for example, a surrogate returned as `char`). The typed Core game answer
retains that distinction. No registration or proof that arbitrary component
instantiation establishes `readyCfg` is inferred; nor does the result cover
resumption after lockdown, other owners, host moves or arbitrary prefixes.
The stock `Simple.adequacy` identifies only trap-last plays; observing the
retained store after a trap would distinguish its existing witnesses.

For the start-free two-module direct wire, `DirectWire.instantiates_iff`
derives the ready configuration from the stock preparation and resolution
checks. `DirectWire.terminalForwardOfInstantiation` follows a given finite
Core `Entry.Finishes` from the resolved address and constructs a stock
reference `Calls` derivation at the named lift, without fuel or a Core
determinism hypothesis. It keeps the mapped final Core store even when the
ABI rejects a normal Core result. Together with readback,
`DirectWire.terminalObservationIff` equates the reachable pairs of reported
ABI outcome and mapped final Core store on this boundary. It does not equate
Core results with component values or identify complete traces; host imports,
divergence, and nested component links are outside this theorem.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms +Silmaril.Wasm.Component.Reference.DirectLift.Thms'
```

## Ready components with synchronous imports

`Silmaril.Wasm.Component.SyncImportITree.Thms` exposes the flat, float-free
`Reference.SimpleI` fragment as abstract Wasm bodies. A `Question` carries
checked arguments for one particular function. Its `Answer` is either checked
results of that function's type or a trap. The tree is built one Core game
move at a time. A visible import holds the paused thread and its store in
the continuation. `request_resumes` relates each reply to the canonical ABI's
`ImpRel`, the existing game transition, and one actual Core reduction.

`body_sees_iff` gives both directions for the `BodyTrace` observations
from a supplied ready store. After any finite sequence of legal import
exchanges, a branch can return, trap, expose its next unanswered import,
or witness an infinite host-free Core run. A reply retains the reached
Core store, including on a trap. The caller can pass it to another body
under the Core game's resumable-session convention. Waiting at a visible
request is a finite prefix and imposes no host progress obligation.
`productive_iff` characterizes infinite import exchanges by their finite
pending prefixes.
The correspondence is exact at a fixed deterministic Core profile.
Different host replies give different branches, and the theorem supplies
no must-termination or fairness property. The step into the body starts
after Core instantiation and permits only one active export. The interface
has no streams, futures, or callback reentry.

The scalar game's `ScalarInstance.Trans` is the operational source used by
`impSem` through `core3Sem`. The finite `Wasi.Body` handler interpreter
in [`Wasi.Comp`](../../Silmaril/Wasi/Comp/Defs.lean) also has named import
waiting and reply states. It describes a program already written in the
handler language. [PR #1267](https://github.com/hiloopai/silmaril-lean/pull/1267)
relates its model runner to that language and to linked host plays.
The [downstream regression](../../Silmaril/Wasm/Component/SyncImportITree/Examples.lean)
instead starts from the stock `fwdS` Core 3.0 instance used by the
reference component litmus. It sees the same suspended call resume with
two different legal replies and distinguishes host wait from a trap.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Component.SyncImportITree.Examples'
```

### Stock reference dispatcher at a typed import

The cut API uses the stock `Machine.Steps` and dispatcher at `core3P (profile o)`.
`ReferenceCut.request` takes a focused Core activation and a prefix of
`.core` steps ending at a recognized optionless lower of import `i` in
instance zero. The cut gives the flat parameter types and their successful
lift to a typed question. The theorem renames the reference store's Core
host code by `trampIdx`, derives the game's typed import transition and
the tree's request via `tree_request`, and gives the stock `coreCallout`
step with that same thread and continuation in `Seg.core`.
[`Reference.SyncImportCut.Thms`](../../Silmaril/Wasm/Component/Reference/SyncImportCut/Thms.lean)

`ReferenceCut.answer` applies when the store is unlocked, the owner passes
`calloutEntry`, the instance may leave, and function `i` is the host binding
for import `i`. Given one typed answer from `answerHostS`, the stock
dispatcher runs through `on_start` and `on_resolve` to a flat return. The
`popCore` step restores the saved continuation with the same Core store
and thread as the tree's residual cursor, and with the host's new state.
The downstream example uses the `fwdS` signature and the stock counter
host at a local cut. [Lean example](../../Silmaril/Wasm/Component/Reference/SyncImportCut/Examples.lean)

The tree is visibly pending at this cut. Silent divergence requires an
infinite host-free Core run. The reference synchronous loop can trap
with `cannotBlockSync` when a parked caller leaves the instance with no
ready thread (`HLinked2.silent_cannotBlock`). The `answerHostS` policy
traps if its answering function returns `none`.
`ReferenceCut.refuses` reaches that machine trap, whose `trapCfg` locks
the component store and clears the active control chain. Supplying
`none` as an ITree reply resumes the game cursor with a Core trap and
retains its Core store.

### Successful single-export runs

`sees_of_reference_return` starts from a stock `Instantiates` run for
`SimpleI.toRef` and a stock `Calls` run resolving the selected export with
values. The component must be start-free, wired as `SimpleI.Inst` specifies,
and in the flat, float-free fragment described by `Ready`. The host is
`answerHostS` with `SimpleI.HostOkS`. Successful import rounds supply their
actual typed replies, with the host state threaded through `HostReplies`.
The theorem reads each answered dispatcher callout in order, for any finite
number of such callouts. Its ITree path starts at the instantiated store,
returns the observed typed values, and carries the reference run's final Core
store with trampoline host code renamed to import indices.
[`Reference.SyncImportRun.Thms`](../../Silmaril/Wasm/Component/Reference/SyncImportRun/Thms.lean)

The downstream check instantiates `fwdS` and calls `f(3)` in the stock
dispatcher. The counter host starts at `10`, the export returns `13`, and
the host ends at `11`. The matching ITree path has one answered import and
carries the final mapped Core store.
[Lean example](../../Silmaril/Wasm/Component/Reference/SyncImportRun/Examples.lean)

`reference_return_of_sees` replays an independently supplied successful ITree
path from the corresponding fresh stock instance. `HostReplies` checks each
typed exchange against the fixed answering function in the host state left
by the preceding exchange. The replay constructs a stock `Calls` witness with
the path's result values, final host state and projected Core store.
`reference_return_iff_sees` bundles both directions at that observation level.
The replay example uses the tree's explicit reply of `13` to `f(3)`, admitted
by the counter host in state `10`.
[Lean example](../../Silmaril/Wasm/Component/SyncImportITree/Examples.lean)

The observer projects away internal steps, the component arena and scheduler
labels. The equivalence covers successful returns with finitely many answered
imports. Relating whole-export observations of failed ABI lifts, host refusal
and lockdown, `cannotBlockSync`, pending requests and silent Core divergence
remains open.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Component.SyncImportITree.Examples +Silmaril.Wasm.Component.Reference.SyncImportCut.Examples +Silmaril.Wasm.Component.Reference.SyncImportRun.Examples'
```

## What ships

| Part | Modules | What it is |
| --- | --- | --- |
| Component model | `Silmaril.Wasm.Component` | the component binary codec behind one facade (`Codec`: `mvp`, `strict`, `async` and `lax` variants, with `mvp ⊆ lax` and `strict ⊆ lax` proved), the validator (proved sound), the canonical ABI, a reference component machine, resources, streams and futures |
| WIT | `Silmaril.Wasm.Wit` | WIT text and binary packages: parser, printer, elaboration and the custom-section encoding |
| jco | `Silmaril.Wasm.Jco`, `Silmaril.Wasm.JcoTool` | the transpilation of components to core modules and JavaScript glue, with the stream stack |
| WAC | `Silmaril.Wasm.Wac` | the WAC composition language: text, resolution and composition of components |
| Perf | `Silmaril.Wasm.Perf` | fast paths (validator, decoder, encoder, printer) used through `@[csimp]`; each states its equation with the verified version in `Thms` |
| Versions | `Silmaril.Wasm.Versions` | Wasm 1.0, 2.0 and Lime1 models with translations to Core 3.0 |
| CLI spec | `Silmaril.Cli.Spec.WasmTools`, `.Jco`, `.Wac`, `Silmaril.Cli.Clap` | the command lines as values, with derived help and usage errors |
| Generators | `Silmaril.Wasm.Tools.Gen` | `Gen.API` (core-only interface), per-model kits, the generators, mutators and shrinkers of `smith`, `mutate`, `shrink` and `wit-smith` |
| SpecTec | `Silmaril.Wasm.SpecTec` | the SpecTec headers that need the modules above: institution chains between 2.0 and 3.0, the remaining Sim10/Sim20 halves, `BinaryAgree`, the Lime1 grammar and simulations |

## Tools

| Executable | Source | What it does |
| --- | --- | --- |
| `wasm-tools` | `tools/wasm-tools` | the full build: the core subcommands plus `component new/wit/embed/targets/unbundle/semver-check`, `compose`, `smith`, `mutate`, `shrink`, `wit-smith`; every command line is read through `Silmaril.Cli.Spec.WasmTools.tool` |
| `wasm-tools-gen` | `tools/wasm-tools` | the generator subcommands alone |
| `wasm-tools-gen-check` | `tools/wasm-tools-gen-check` | measures how often each checked generator or mutator falls back |
| `wasm-jco` | `tools/wasm-jco` | a jco 1.39.0 work-alike (`transpile`, `new`, `wit`, `embed`, …) |
| `wasm-wac` | `tools/wasm-wac` | a WAC 0.12.0 work-alike (`compose`, `plug`, `parse`, `resolve`) |
| `wasm-wit` | `tools/wasm-wit` | WIT text and package tools |
| `wasm-perf` | `tools/wasm-perf` | runs the fast paths on inputs, for benchmarks |
| `cli-spec`, `cli-harness`, `cli-demo` | `tools/cli-*` | print and test the CLI specifications; a small demo program |

Build them with Lake:

```sh
lake build wasm-tools wasm-tools-gen wasm-tools-gen-check wasm-jco wasm-wac wasm-wit wasm-perf cli-spec cli-harness cli-demo
.lake/build/bin/wasm-tools component wit some-component.wasm
.lake/build/bin/wasm-jco transpile some-component.wasm -o out
```

## The `wasm-tools` command line, specified

The command line of `wasm-tools` 1.262.0 is a value: an argument grammar in the clap dialect
(`Silmaril.Cli.Spec.WasmTools.tool`) with every subcommand, option, positional argument, value
check and `requires`/`conflicts_with` rule of upstream. The executable reads every command line
with it before anything else.

- **Reading.** The clap pre-pass, then the argument parser proved sound and complete for the
  grammar, then the value checks and rules. When the pre-pass passes, the clap reading is proved
  to agree with the generic front end (`read_agrees`). The program reads as the spec
  (`WasmTools.toolAt_read`).
- **Help and errors are derived.** The `-h` and `--help` texts of every command path and every
  usage error are rendered from the grammar in clap 4.6's layout, byte-identical to upstream's
  on all 29 command paths at 100 and 80 columns and on 1096 of 1098 tested command lines (the 2
  others differ in the order in which upstream checks values).
- **Layout facts, proved.** Wrapping only inserts line breaks and indentation and drops trailing
  white space (`wrap_erase`); help and the version go to stdout and every usage error to stderr
  (`Tool.text_channel`); an error text starts with `error: `.

Where the layout puts its line breaks, and clap's wording, are tested against the pinned
binary, not proved.

## Program generators, mutators and shrinkers

`smith`, `mutate`, `shrink`, `wit-smith` and `wasm-tools-gen-check` are instances of one small
interface, `Silmaril.Wasm.Tools.Gen.API`, which needs only Lean's core library.

| Object | Meaning |
|---|---|
| `Rng`, `Rand` | SplitMix64, a splittable 64-bit generator, and seeded computations over it |
| `Lang`, `DecLang` | syntax with a validity predicate; a language with a Boolean checker proved equivalent to validity |
| `Generator L` | from a seed and a size, a program; every output is valid |
| `Mutator L` | a seeded rewrite that preserves validity |
| `SemMutator L Eqv` | a mutator whose output is `Eqv`-equivalent to its valid input |
| `Shrinker S` | a size and a candidate list; `Shrinker.shrink p x` greedily takes the first strictly smaller candidate satisfying `p`, and terminates |
| `ByteGen L`, `PMutator L` | the byte-seeded shapes of `wasm-tools smith` and `wasm-tools mutate` |

`Generator.guarded`, `Mutator.guarded` and `SemMutator.guarded` turn an unverified generator or
rewrite into a verified one: an output is kept when the checker accepts it, and replaced by a
valid default otherwise. The laws (`Gen.API.Thms`): checked shrinking keeps the predicate and
validity, never grows the input and ends in a local minimum.

`Silmaril.Wasm.Tools.Gen.Model` has a kit (checker, generator, mutator, shrinker) per model:
`kit10`, `kit20`, `kit30`, `kitLime1`, `kitFX`, and `coreKitT`/`kitFXT` whose generators are
valid by construction. `Gen.Comp` generates components and `Gen.Wit` WIT packages.

Trust boundary: the raw generators and mutators are unverified; validity comes from the checker
(a fast Core validator proved equal to the verified one) or from typing by construction. The
component validator is proved sound, not complete, so a checked component generator may fall
back where upstream would accept.

## Known limitations

- **Frozen statements.** Some results are stated as `def Task.x : Prop` and used only as
  hypotheses. Nothing unconditional depends on them. For the components and WIT:
  `Task.check_complete` (`Proofs/Wasm/Wit/Tool/Complete`), `Task.refToSpecFXE`,
  `Task.coreFraming_of_decode`; for the asyncify link to Core 3.0 (`FX/Asyncify/Tool`):
  `Task.machine_core`, `Task.fits`. For the CLI:
  `WasmTools.SpecThms.Task.*_agree` and `Wast.Spec.Task.*_agree` (the older core readers agree
  with the specification; tested on records with 0 differences). The SpecTec modules add
  `Task.composite*`, `Task.swapStep*`, `Task.unstripStep*` and a few others, described in
  [the SpecTec guide](spectec/README.md).
- **Raw modules.** About 200 modules under `Silmaril/Raw/Wasm/{Component,Versions,…}` hold
  valid but unrefined proofs, about 1,350 theorems of the component model among them. Headers
  re-export the parts other topics use.
- **Partial definitions.** `Tools/Component/Layout`, `Tools/Component/Typed`, `Wac/Text/Json`,
  `Wit/Binary/Print` and `wasm-tools-gen-check` still contain `partial def`s.
- **Upstream parity is tested, not proved.** The suites under `tools/wasm-tools/tests/
  {component,compval,gen}`, `tools/wasm-jco/tests`, `tools/cli-spec/tests` and
  `tools/cli-harness/tests` compare against pinned upstream binaries (wasm-tools 1.262.0,
  jco 1.39.0, wac 0.12.0, wasmtime 50.0.0) and skip when those are not installed; CI does not
  run them. Some read component fixtures that are not part of this repository yet. Last full
  run before release: jco suite 442 passed and 0 failed; the component validator agreed with
  upstream on 1896 of 1919 corpus components (13 valid ones rejected, 10 invalid ones
  accepted); `component new` agreed on 78 cases, both refused 15 and 22 differed; the CLI texts
  1096/1098.
- **Not implemented:** `wit-dylib` and `component link` report `not implemented in this build`.

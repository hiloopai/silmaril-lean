module

public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Defs
public import Silmaril.Wasm.Component.Reference.Instantiate.Root.Defs

/-!
# The embedding API: lifting, lowering, invoking, ticking, cancelling, instantiating

The REF Embedding API (`Store.invoke`, `Store.lift`, `Store.lower`, `Store.tick`, L524-563 of
`definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF"), plus root instantiation (`Instantiate/Root.lean`), on top of the component machine
(`Machine/Exec.lean`, `Machine/Step.lean`) with the dispatcher `Canon.dispatch`
(`Canon/Dispatch.lean`):

| Lean | REF / meaning |
| --- | --- |
| `storeLift core ft opts inst` | `Store.lift` (L539-543): a `CFuncInst.lifted` function value |
| `storeHostFunc ft fn` | a host function value (`CFuncInst.host`, run_tests `mk_host_func`) |
| `storeLower f opts inst` | `Store.lower` (L545-548): a core host function `CanonHost.lowered` |
| `invokeTop c f args` | `Store.invoke` (L524-536) as the host event `HostEvent.invoke` |
| `tickTop` | `Store.tick` (L555-563), `HostEvent.tick` |
| `cancelTop c` | the `on_cancel` returned by `Store.invoke` (L530-534), `HostEvent.cancel` |
| `instantiateTop c args` | root instantiation (`instantiateRootCall`), `HostEvent.run` |
| `componentMachine E X lim q hr host σ0` | an embedder and its initial machine configuration |
| `Calls`, `CallDiverges` | the relational outcome of a top-level call (over `Machine.Steps`) |
| `Instantiates`, `InstantiateTraps`, `InstantiateDiverges` | the same for instantiation |
| `Embedder.runTop`, `callTop`, `instantiateRun` | executable drivers, with soundness |

**Instantiation results.** A host frame discards its program's result (`Machine.runProg`), so
`instantiateProg` reports the root instance and its *function* exports (the part of the export
map the host can invoke) by one observation `instantiatedObs inst es`
(`HostObs.note instantiatedTag ...`, names as utf8 strings, ids as `u32`), decoded exactly by
`decodeInstantiated?` (`decodeInstantiated?_instantiatedObs`). `Instantiates` reads the first
such observation of the trace. Host functions running during instantiation (start
functions) must not emit notes with the tag `instantiatedTag` (not checked).

**Instantiation is a host entry.** `instantiateProg` brackets root instantiation with
`nesting_depth += 1` / `-= 1` like `Store.invoke`, so start functions (`Store.lift`'s
`func_inst`) and the host imports they call (`Store.lower`) run at `nesting_depth > 0`, the
precondition REF asserts (L540, L549; D-f).

## Proved

* `Embedder.runTop_sound`: the trace of `runTop` is a `Machine.Steps` trace
  (`Machine.runTop_sound`).
* `Embedder.callTop_sound`: an executable top-level call with a classified outcome
  (`callOutcome?`: resolved with its result, a trap other than an `internal` fault, or deadlock
  of the call) is a `Calls` fact
  (its trace issues only ticks after the invoke: `runTopCall_ticks`).
* `Embedder.instantiateRun_sound`: an executable instantiation that finished (host in control,
  not locked down) with a decoded result is an `Instantiates` fact (`Machine.run` issues no
  host event: `run_noHost`).
* `step?_not_host`, `runLoop_noHost`, `runTopLoop_ticks`, `hostStep?_label`: the label shapes
  of the executable drivers.
* `decodeInstantiated?_instantiatedObs` (the observation encoding round-trips).

## Tests (Mock engine, kernel-checked by `decide +kernel`)

* the empty component instantiates in a fresh root instance `0` with no exports
  (`empty_instantiates`, and the relational `empty_instantiates_rel`);
* a component whose core module exports `f() = 42` (no imports, no memory), lifted at
  `func() -> u32` and exported as `"f"`, instantiates with the export `("f", func 0)`
  (`const_instantiates`), and invoking the export resolves the top-level call with `[42]`
  (`const_call`); no choice is made and the nesting depth is restored (`const_call_shape`).
  `const_calls` states both relationally, end to end from `smokeMachine.config`
  (`Instantiates` to `m₁`, then `Calls` from `m₁`).

## Design notes and non-claims

* `componentMachine E X lim q hr host σ0` also takes the host readiness `hr` and the host
  record `host : Canon.HostImpl E σ` (instead of `hostFns`, see `Canon/Dispatch.lean`); it
  returns a `ComponentMachine` (the `Embedder` and the initial `Config`), since `Config` does not
  hold the dispatcher.
* Nested instantiation is a late-bound call (`Call.instantiate`, dispatched by
  `Canon.dispatch` to `Instantiate.instantiateClosure`), so the embedding API has no nesting
  bound: arbitrary nesting depth is bounded only by the machine's fuel (the `fuel` of the
  executable drivers). The embedder, the drivers and the relations that mention
  `Embedder.dispatch` take the instance `[∀ a b, Decidable (E.ExternSub a b)]`.
* `Calls` names the top-level call id `c` explicitly; after the invoke its trace may contain
  only the host events `tick` and `cancel c` (`CallHostEvent`), so no other host program can
  forge `HostObs.resolved c` or cause the outcome. Its outcome `resolved r` requires the
  host in control, no lockdown and `result? c = some r` (other top-level calls may be
  unresolved); `deadlock` is `Machine.Deadlocked` with `c` unresolved; `trap` is a machine
  trap (global, as in REF: it may come from another thread already present in `m`) whose trace
  has no `TrapReason.internal` label, so a model fault cannot satisfy a trap-expected fact.
  `Instantiates` / `InstantiateTraps` allow no host event after the instantiation event, and
  `InstantiateTraps` also excludes `internal` faults.
  Host functions (`HostImpl`) are trusted: one that emits `HostObs.resolved c` itself is not
  excluded. `CallDiverges` and
  `InstantiateDiverges` are guest divergence (`Machine.Diverges`, internal steps only) after the
  host event.
* `instantiateRun` drives internal steps only (`Machine.run`, no ticks): instantiation is
  synchronous (start functions run under `canon_lift`'s synchronous loop).
* Not claimed: completeness of the drivers, termination, fairness, typing of instantiation
  (not modelled; only the run-time import check `Instantiate.importTypeCheck` is performed),
  or anything about host behaviour beyond the given programs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
  _root_.Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type}

/-! ## `Store.lift` / `Store.lower` -/

/-- REF `Store.lift(f, ft, opts, inst)` (L539-543): the function value `f` lifted at `ft`
with `opts` in `inst` (its `func_inst` is `canon_lift`, dispatched from `Call.funcInst`). -/
def storeLift (core : E.FuncAddr) (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E)
    (inst : InstId) : P E σ FuncId :=
  allocObj ArenaField.funcs (.lifted core ft opts inst)

/-- A host function value of type `ft` running host program `fn` (run_tests
`mk_host_func`; dispatched to `HostImpl.funcs fn`). -/
def storeHostFunc (ft : WIT.FuncType Empty RtId) (fn : HostFuncId) : P E σ FuncId :=
  allocObj ArenaField.funcs (.host ft fn)

/-- REF `Store.lower(f, ft, opts, inst)` (L545-548): a core host function of flat type
`flatten_functype(opts, ft, 'lower')` whose calls run `canon_lower` (`CanonHost.lowered`). -/
def storeLower (f : FuncId) (opts : CanonOpts E) (inst : InstId) : P E σ E.FuncAddr := do
  let fi ← getObj ArenaField.funcs f
  Instantiate.allocCoreHost (.lowered f fi.ft opts inst)

/-- `Store.lift` on a store (outside the machine). -/
def storeLiftSt (s : CStore E) (core : E.FuncAddr) (ft : WIT.FuncType Empty RtId)
    (opts : CanonOpts E) (inst : InstId) : CStore E × FuncId :=
  ArenaField.funcs.alloc s (.lifted core ft opts inst)

/-! ## Instantiation results as an observation -/

/-- The tag of the instantiation observation. -/
def instantiatedTag : String := "component.instantiated"

/-- A name as a (utf8, i32-sourced) string value. -/
def nameVal (n : String) : Val := .string ⟨⟨n, .utf8, n.utf8ByteSize⟩, .i32⟩

/-- One function export as a value. -/
def encodeExport (p : String × FuncId) : Val := .record [nameVal p.1, .u32 p.2.idx]

/-- The observation reporting root instance `inst` and function exports `es`. -/
def instantiatedObs (inst : InstId) (es : List (String × FuncId)) : HostObs :=
  .note instantiatedTag (.u32 inst.idx :: es.map encodeExport)

/-- Decode `encodeExport`. -/
def decodeExport? : Val → Option (String × FuncId)
  | .record [.string s, .int .u32 n] => some (s.v.str, ⟨n.toNat⟩)
  | _ => none

/-- Decode `instantiatedObs`. -/
def decodeInstantiated? : HostObs → Option (InstId × List (String × FuncId))
  | .note tag (.int .u32 i :: vs) =>
    if tag = instantiatedTag then (vs.mapM decodeExport?).map fun es => (⟨i.toNat⟩, es)
    else none
  | _ => none

/-- The function exports of an export map. -/
def funcExports (es : Instantiate.Exports E) : List (String × FuncId) :=
  es.filterMap fun
    | (n, .func f) => some (n, f)
    | _ => none

/-! ## Host events -/

/-- REF `Store.invoke(f, on_start, on_resolve)` of function value `f` on `args` as top-level
call `c` (the caller record's `on_start` returns `args`; `on_resolve` records the result). -/
abbrev invokeTop (c : CallId) (f : FuncId) (args : List Val) : HostEvent E σ :=
  .invoke c f args

/-- REF `Store.tick()`. -/
abbrev tickTop : HostEvent E σ := .tick

/-- The `on_cancel` returned by the `Store.invoke` of top-level call `c`. -/
abbrev cancelTop (c : CallId) : HostEvent E σ := .cancel c

section Instantiation

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- The instantiation program: a host entry like `Store.invoke` (`nesting_depth += 1`), root
instantiation of `c` with arguments `args` (`Instantiate.instantiateRootCall`: nested
instantiations are late-bound `Call.instantiate`s), `nesting_depth -= 1`, then the observation
of the root instance and its function exports. The bracket makes start functions
(`Store.lift`'s `func_inst`) and the host imports they call (`Store.lower`) run at
`nesting_depth > 0`, as REF asserts (L540, L549; D-f preconditions). -/
def instantiateProg (c : Syntax.Component E.Module) (args : Instantiate.Exports E) :
    P E σ (Ret E) := do
  modifyStore DispatchSt.incNestingSt
  let (inst, es) ← Instantiate.instantiateRootCall c args
  modifyStore DispatchSt.decNestingSt
  emit (instantiatedObs inst (funcExports es))
  pure .unit

/-- Root instantiation as a host event. -/
abbrev instantiateTop (c : Syntax.Component E.Module) (args : Instantiate.Exports E) :
    HostEvent E σ :=
  .run (instantiateProg c args)

end Instantiation

/-! ## Embedders and the initial machine -/

/-- An embedder: the executable core stepper, limits, quirks (`Quirks.none` is the
specification), the host readiness and the host behaviour. -/
structure Embedder (E : CoreEngine) (σ : Type) where
  X : E.Exec
  lim : Limits := Limits.spec
  q : Quirks := Quirks.none
  hr : HostReady σ
  host : HostImpl E σ

/-- The dispatcher of an embedder. -/
abbrev Embedder.dispatch [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) :
    Call E → P E σ (Ret E) :=
  Canon.dispatch emb.lim emb.q emb.hr emb.host

/-- An embedder together with a machine configuration. -/
structure ComponentMachine (E : CoreEngine) (σ : Type) where
  emb : Embedder E σ
  config : Config E σ

/-- The component machine of engine `E` with stepper `X`, limits `lim`, quirks `q`, host
readiness `hr` and host behaviour `host`, in its initial state: the empty store (REF
`Store()`), host state `σ0`, the host in control. -/
def componentMachine (E : CoreEngine) (X : E.Exec) (lim : Limits) (q : Quirks)
    (hr : HostReady σ) (host : HostImpl E σ) (σ0 : σ) : ComponentMachine E σ :=
  { emb := { X, lim, q, hr, host }, config := Config.init CStore.empty σ0 }

/-! ## Relations -/

/-- The outcome of a top-level call. -/
inductive CallOutcome where
  /-- The call resolved (`none`: cancelled). -/
  | resolved (r : Option (List Val))
  /-- The machine trapped with a specification trap (`Calls` excludes `TrapReason.internal`
  faults from the trace). -/
  | trap
  /-- The call is unresolved and no thread can make progress. -/
  | deadlock

/-- What an outcome says about the final configuration `m` of top-level call `c`. -/
def CallOutcome.Holds (hr : HostReady σ) (c : CallId) (m : Config E σ) : CallOutcome → Prop
  | .resolved r => m.ctl = [] ∧ m.store.lockdown = false ∧ m.result? c = some r
  | .trap => Trapped m
  | .deadlock => Deadlocked hr m ∧ m.result? c = none

section Relations

variable (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))

/-- The host events allowed after the invoke of top-level call `c` in `Calls`: `Store.tick`
and the `on_cancel` of `c` itself (no other invokes, cancels or host programs, which could
emit a forged `HostObs.resolved c` or trap independently of `c`). -/
def CallHostEvent (c : CallId) (ev : HostEvent E σ) : Prop :=
  ev = .tick ∨ ev = .cancel c

/-- Top-level call `c` of `f` on `args` from `m` ends in `m'` with outcome `out`: a machine
trace starting with the invoke whose later host events are only ticks and cancellations of
`c` (`CallHostEvent c`). Internal steps may still run other threads already present in `m`
(a `trap` of the machine is global, as in REF). A `trap` outcome must not come from an
`internal` fault (a model bug or an unmodelled feature, not proved unreachable). -/
def Calls (m : Config E σ) (c : CallId) (f : FuncId) (args : List Val) (m' : Config E σ)
    (out : CallOutcome) : Prop :=
  ∃ tr, Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) m' ∧
    (∀ ev, Label.host ev ∈ tr → CallHostEvent c ev) ∧
    (out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr) ∧ out.Holds hr c m'

/-- Top-level call `c` of `f` on `args` from `m` diverges (guest divergence after the invoke). -/
def CallDiverges (m : Config E σ) (c : CallId) (f : FuncId) (args : List Val) : Prop :=
  ∃ m₁, Step prof hr dispatch m (.host (invokeTop c f args)) m₁ ∧
    Diverges prof hr dispatch m₁

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- Instantiating `c` with `args` from `m` ends in `m'` (host in control, no lockdown) with
root instance `inst` and function exports `exports`: after the host event, only internal steps
(no host event), so `m'` is the configuration at the end of the instantiation. -/
def Instantiates (m : Config E σ) (c : Syntax.Component E.Module)
    (args : Instantiate.Exports E) (m' : Config E σ) (inst : InstId)
    (exports : List (String × FuncId)) : Prop :=
  ∃ tr, Steps prof hr dispatch m (.host (instantiateTop c args) :: tr) m' ∧
    (∀ ev, Label.host ev ∉ tr) ∧ m'.ctl = [] ∧ m'.store.lockdown = false ∧
    (traceObs tr).findSome? decodeInstantiated? = some (inst, exports)

/-- Instantiating `c` with `args` from `m` traps (internal steps only after the host event)
with a specification trap: the trace has no `internal` fault.

Deviation from wasmtime: a missing or ill-typed root argument (`hostTrap "missing import"`,
`hostTrap "import type mismatch: ..."`, see `Instantiate/Root.lean`) is modelled as a trap, so
it also locks the store down (`Trapped m'`) and no later host event is possible from `m'`.
wasmtime instead reports a link error (`Linker::instantiate` / `instantiate_pre` return `Err`)
before any side effect and leaves the store usable. -/
def InstantiateTraps (m : Config E σ) (c : Syntax.Component E.Module)
    (args : Instantiate.Exports E) (m' : Config E σ) : Prop :=
  ∃ tr, Steps prof hr dispatch m (.host (instantiateTop c args) :: tr) m' ∧
    (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap (.internal msg) ∉ tr) ∧ Trapped m'

/-- Instantiating `c` with `args` from `m` diverges. -/
def InstantiateDiverges (m : Config E σ) (c : Syntax.Component E.Module)
    (args : Instantiate.Exports E) : Prop :=
  ∃ m₁, Step prof hr dispatch m (.host (instantiateTop c args)) m₁ ∧
    Diverges prof hr dispatch m₁

end Relations

/-! ## Executable drivers and their soundness -/

namespace Embedder

variable [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) (o : Oracle E)

/-- Internal steps and host ticks from `m`, at most `fuel` steps (`Machine.runTop`). -/
def runTop (fuel : Nat) (m : Config E σ) : RunResult E σ o.State :=
  Machine.runTop emb.hr emb.dispatch emb.X o fuel m

/-- Issue top-level call `c` of `f` on `args`, then `runTop` (`Machine.runTopCall`). -/
def callTop (fuel : Nat) (c : CallId) (f : FuncId) (args : List Val) (m : Config E σ) :
    Option (RunResult E σ o.State) :=
  runTopCall emb.hr emb.dispatch emb.X o fuel c f args m

/-- Instantiate `c` with `args` (the host event `instantiateTop c args`), then run
internal steps (at most `fuel`); `some (r, inst, exports)` when the event was enabled, the
instantiation finished (host in control, no lockdown) and reported its result. The labels of
`r` start with the host event. -/
def instantiateRun (fuel : Nat) (c : Syntax.Component E.Module)
    (args : Instantiate.Exports E) (m : Config E σ) :
    Option (RunResult E σ o.State × InstId × List (String × FuncId)) :=
  match hostStep? emb.hr (instantiateTop c args) m with
  | none => none
  | some (l, m₁) =>
    let r := Machine.run emb.hr emb.dispatch emb.X o fuel m₁
    if r.config.ctl = [] ∧ r.config.store.lockdown = false then
      match (traceObs r.labels).findSome? decodeInstantiated? with
      | some (inst, es) => some ({ r with labels := l :: r.labels }, inst, es)
      | none => none
    else none

end Embedder

/-- Classify a run of top-level call `c`: resolved (with its result), trapped with a
specification trap, or deadlocked with `c` unresolved; `none` otherwise (out of fuel, running,
an `internal` fault, or a deadlock of another call). -/
def callOutcome? {S : Type} (c : CallId) (r : RunResult E σ S) : Option CallOutcome :=
  match r.outcome with
  | .resolved => (r.config.result? c).map .resolved
  | .trap => if r.labels.any Label.isInternalTrap then none else some .trap
  | .deadlock => if (r.config.result? c).isNone then some .deadlock else none
  | _ => none

section Labels

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end Labels

namespace Embedder

variable [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) (o : Oracle E)

end Embedder

/-! ## Smoke tests (Mock engine) -/

namespace EmbeddingTests

open Engine.Mock (mock mockExec)

/-- No host ready predicate holds. -/
def noReady : HostReady Unit := fun _ _ => false

/-- The specification embedder over the Mock engine without host functions. -/
def smokeMachine : ComponentMachine mock Unit :=
  componentMachine mock mockExec Limits.spec Quirks.none noReady HostImpl.none ()

/-- The embedder of `smokeMachine`. -/
def smokeEmb : Embedder mock Unit := smokeMachine.emb

/-- The deterministic first-alternative oracle. -/
abbrev first : Oracle mock := Oracle.first

/-- Instantiate the empty component. -/
def emptyRun : Option (RunResult mock Unit Unit × InstId × List (String × FuncId)) :=
  smokeEmb.instantiateRun first 50 [] [] smokeMachine.config

/-- A core module exporting `f() = 42` (no imports, no memory). -/
def constModule : Mock.Module where
  funcs := [⟨⟨[], [.int .i32]⟩, [.const 0 (i32Flat 42), .ret [0]]⟩]
  exports := [("f", .func 0)]

/-- A component lifting the core function `f` at `func() -> u32` and exporting it as `"f"`. -/
def constComponent : Syntax.Component mock.Module :=
  [.coreModule constModule, .coreInstance (.instantiate 0 []), .alias (.coreExport 0 "f" .func),
    .type (.func { params := [], result := some (.prim .u32) }), .canon (.lift 0 [] 0),
    .export_ { name := "f" } ⟨.func, 0⟩ none]

/-- Instantiate `constComponent`. -/
def constRun : Option (RunResult mock Unit Unit × InstId × List (String × FuncId)) :=
  smokeEmb.instantiateRun first 200 constComponent [] smokeMachine.config

/-- Invoke the export `"f"` of `constComponent` as top-level call `0` and run. -/
def constCall : Option (RunResult mock Unit Unit) :=
  constRun.bind fun (r, _, es) =>
    (es.lookup "f").bind fun f => smokeEmb.callTop first 400 ⟨0⟩ f [] r.config

end EmbeddingTests

end Silmaril.Wasm.Component

module

public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-!
# The relational machine semantics

The labelled small-step relation `Machine.Step` of the component machine: it interprets the
operations `Canon.Op E σ` of the specification programs `Canon.P E σ` (the REF functions of
`definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF") over the configurations `Machine.Config E σ` of `Machine/Config.lean`.
It is the relational counterpart of the executable `step?`; `Machine/Soundness.lean` proves `step?`
sound and `Machine/Completeness.lean` complete against it.

`Step prof hr dispatch m l m'` is parametric in
* the profile `prof`, gating every oracle answer by `Canon.Allowed prof`;
* the host readiness function `hr : HostReady σ` (the ONE function used both by the thread
  programs of `Runtime/Thread.lean` and by the candidate set `CStore.candidates (hr m.host)`
  of `HostEvent.tick`);
* the non-recursive dispatcher `dispatch : Call E → P E σ (Ret E)` of late-bound calls.

Core code steps with the engine's relation `E.Internal` (NOT an executable stepper).

## Rules (one constructor per case of `step?`)

Programs (head activation `⟨th, .prog p, segs⟩ :: rest` of `m.ctl`):

| constructor | focus | effect | label |
| --- | --- | --- | --- |
| `popProg` | `pure r`, top seg `.prog k` | focus `k r` | `tau` |
| `popCore` | `pure (.flat vs)`, top seg `.core t k` | resume `t` with `vs` (`E.resume`) | `tau` |
| `threadExit` | `pure r`, no segs, thread `some t` | `t` exited; pop the activation | `tau` |
| `hostDone` | `pure r`, no segs, host frame | `hostFinish`: pop, record `on_cancel` | `tau` |
| `call` | `call c` | push seg `.prog k`, focus `dispatch c` | `tau` |
| `callCore` | `callCore f args` | focus core `E.invoke f args` | `tau` |
| `get` / `modify` | store access | `k s` / apply `f` | `tau` |
| `trap` | `trap r` | lockdown, discard `ctl` | `trap r` |
| `choose` | `choose k` | any `r` with `Allowed prof k r` | `choice k r` |
| `currentThread` | | `k th` | `tau` |
| `newThread` | `newThread b` | allocate thread, save `dispatch (.threadBody b)` | `tau` |
| `block` | `block none` | save activation, `t` blocked, pop to the resumer | `tau` |
| `blockSwitch` | `block (some o)` | save, `t` blocked, run `o`'s saved activation | `tau` |
| `resumeThread` | `resumeThread t` | push `t`'s saved activation above | `tau` |
| `hostGet` / `hostSet` | host state | | `tau` |
| `emit` | `emit o` | `HostObs.resolved c r` records the resolution | `obs o` |

Core activations (`⟨th, .core ct k, segs⟩`): `coreInternal` (an `E.Internal` step, label
`core`, only while the status is `running` or `stuck`, i.e. neither returned nor parked on a
callout, the `_` branch of `coreStep`, so non-lawful engines agree with `step?` too),
`coreReturned` (status `returned (.values vs)`: focus `k vs`), `coreTrap` (status
`returned .trap`: machine trap `coreTrap`), `coreCallout` (status `callout h args`: push seg
`.core ct k`, focus `dispatch (.hostCallout h args)`; with the specification dispatcher this is
`Canon.hostCalloutProg`, whose entry check `Canon.calloutEntry` on the current thread enforces
REF `Store.lower`'s `assert(inst is current_instance())` (L548) and the `may_leave` traps of
`canon_lower` (L2171) and of the built-ins, and confines embedder imports while the current
instance may not leave; the rule itself checks nothing, so the guarantee holds for
`Canon.dispatch` and for dispatchers that keep the check, as the test overlays do with
`Canon.withCalloutEntry`). A core activation whose status is
`running` or `stuck` and that has no `E.Internal` step takes no step (the machine is stuck;
`step?` returns `none`).

Faults (`Fault m msg`, rule `fault`, label `trap (.internal msg)`): violated machine invariants
that the executable machine reports as internal traps (with the same messages), expected to be
unreachable for validated components (not proved here): `block` on a host frame, a `switch_to` /
`resumeThread` target without a saved activation, a callout program returning a non-`flat` result.

Host events (label `host ev`), all requiring `m.ctl = []`, `¬ lockdown` and
`nestingDepth = 0` (deviation D-f: side conditions). REF asserts `not lockdown` in
`Store.invoke`, `on_cancel` and `Store.tick` (L525, L530, L556), but `nesting_depth == 0` only
in `Store.tick` (L557). For a top-level `invoke` or `on_cancel`, with no host code running
(`ctl = []`), the condition is expected to hold anyway, but that is not proved here (no lemma
relates `nestingDepth` to `ctl = []` along runs), so it stays a side condition; invokes and
cancels issued by running host code are the calls `Call.hostInvoke` and `Call.hostCancel`,
which have no such condition:
* `hostInvoke c f args` (`c` fresh): appends `(c, f, args)` to `pending` and runs
  `invokeProg c f args` on a host frame (REF `Store.invoke`, L524-536: allocate the host caller
  record `Caller.host c args 0`, `nesting_depth += 1; f(on_start, on_resolve);
  nesting_depth -= 1`);
* `hostTick`: runs `tickProg hr` (REF `Store.tick`, L555-563): the pick among the ready
  candidates is the choice C2 `choose (.tickPick n)` inside the program, so a tick can resume
  ANY ready candidate (`tickPick` is admissible for every answer in every profile) and the
  choice appears in the trace for replay;
* `hostCancel c`: requires a recorded `on_cancel` (`m.cancel? c = some r`) of a call that has
  not resolved (`m.result? c = none`), consumes it (`dropCancel c`, so each call is cancelled at
  most once) and runs `cancelProg r` (REF `on_cancel`, L530-534). The two side conditions are
  REF `request_cancellation`'s assert that the task is `INITIAL` or `STARTED` (D-f);
* `hostRun p`: runs the instantiation program `p` (supplied by the embedding) on a host frame
  (`runProg p`, its result discarded).

## Traces

`Steps prof hr dispatch m tr m'` is the reflexive-transitive closure with the trace of
labels; `Steps.trans`, `Steps.single`, `Steps.toReflTransGen`/`Steps.of_reflTransGen`, and the
label projections `traceChoices`, `traceHostEvents`, `traceObs` (also available as `Steps.choices`,
`Steps.hostEvents`, `Steps.obs`).

`Diverges` is an infinite run of INTERNAL steps (`InternalStep`: any step whose label is not a
host event), i.e. guest divergence with the host passive (what `run_tests.py` and wasmtime
observe as a hang). Host events are always enabled when the host is in control, and e.g.
`hostRun (pure .unit)` followed by `hostDone` returns to the same configuration, so an infinite
run of `AnyStep` exists from every host-ready configuration; that host-inclusive notion is kept
as `DivergesWithHost` and says nothing about termination.

Terminal predicates `Resolved`, `Trapped`, `Deadlocked` describe host-in-control states
(`ctl = []`): such a state has no internal step (`Step.host_of_ctl_nil`), but host events stay
enabled in `Resolved` and `Deadlocked` states (a `Deadlocked` tick only does nothing).

## Design decisions and deviations

* The configuration type is `Machine.Config E σ` (see `Machine/Config.lean`).
* Thread status transitions (REF `Thread.cont`: running / exited / blocked) are performed by
  the machine (`threadStatusSt`) on `block`, `resumeThread` and thread exit, and on the switch
  target of `block (some o)`. `resumeThread` and `block (some o)` require a saved activation of
  the target; they do not re-check the target's `status` (the REF asserts `t` blocked, a
  precondition of the calling programs, deviation D-f).
* `hostDone`: host frames are pushed only by host events, which need `ctl = []`, so a host
  frame at the bottom of the chain belongs to the latest host event; when it returns
  `Ret.cancel r`, `r` is the `on_cancel` of the latest entry of `pending` (`hostFinish`; the
  `tick`, `cancel` and `run` frames return `Ret.unit`).
* `emit (.resolved c r)` records `r` into `results` (`observe`); this is how the host caller's
  `on_resolve` reaches the machine.
* The rules follow the executable `step?`/`hostStep?` of `Machine/Exec.lean` case by
  case, including the fault messages; the host-frame programs and named store updates of
  `StepDefs` have the same bodies as their `Machine/Exec.lean` counterparts (`invokeProg`,
  `tickProg`, `cancelProg`, `runProg`, `CStoreOps.*`), written here because the two files are
  developed in parallel (`Machine/Soundness.lean` relates them).
* The oracle's `failed` flag is an executable concern: the relation quantifies over all
  admissible answers.

Not modelled or claimed here: any property of the relation (soundness and completeness of
`step?` are `Machine/Soundness.lean` and `Machine/Completeness.lean`, invariants
`Machine/Invariant.lean`), fairness, or the choice of `dispatch`. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Named updates and host-frame programs -/

namespace StepDefs

/-- Set the REF `Thread.cont` state of thread `t` (no-op if dangling). -/
def threadStatusSt (t : ThreadId) (st : ThreadStatus) (s : CStore E) : CStore E :=
  ArenaField.threads.modify s t fun th => { th with status := st }

/-- REF `Store.lock_down`. -/
def lockdownSt (s : CStore E) : CStore E := { s with lockdown := true }

/-- REF `self.nesting_depth += 1` of `Store.invoke`, `Store.tick` and `on_cancel`. -/
def enterHostSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth + 1 }

/-- REF `self.nesting_depth -= 1` of `Store.invoke`, `Store.tick` and `on_cancel`. -/
def leaveHostSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth - 1 }

/-- A machine trap: the store is locked down and every activation is discarded (saved
continuations are left as they are). -/
def trapCfg (m : Config E σ) : Config E σ := { m with store := lockdownSt m.store, ctl := [] }

/-- The host-frame program of REF `Store.invoke` (L524-536) of function value `f` as top-level
call `c`: allocate the host caller record, then `nesting_depth += 1`, `f(on_start,
on_resolve)`, `nesting_depth -= 1`; returns the `on_cancel` (`Ret.cancel`) of `f`. -/
def invokeProg (c : CallId) (f : FuncId) (args : List Val) : P E σ (Ret E) := do
  let caller ← allocObj ArenaField.callers (Caller.host c args 0)
  modifyStore enterHostSt
  let r ← callRet (.funcInst f caller)
  modifyStore leaveHostSt
  pure r

/-- The host-frame program of REF `Store.tick` (L555-563): among the ready waiting threads
pick one (choice C2) and resume it (`Thread.resume`, `Runtime/Thread.lean`). -/
def tickProg (hr : HostReady σ) : P E σ (Ret E) := do
  modifyStore enterHostSt
  let s ← getStore
  let h ← hostGet
  match s.candidates (hr h) with
  | [] => pure ()
  | c :: cs => do
    let t ← pickTick c cs
    Thread.resume t
  modifyStore leaveHostSt
  pure .unit

/-- The host-frame program of the `on_cancel` returned by REF `Store.invoke` (L530-534). -/
def cancelProg (r : CancelRef) : P E σ (Ret E) := do
  modifyStore enterHostSt
  let _ ← callRet (.onCancel r)
  modifyStore leaveHostSt
  pure .unit

/-- The host-frame program of `HostEvent.run p`: run `p`, discard its result. -/
def runProg (p : P E σ (Ret E)) : P E σ (Ret E) := do
  let _ ← p
  pure .unit

/-- The latest top-level call issued by the host. -/
def lastCall? (m : Config E σ) : Option CallId := m.pending.getLast?.map (·.1)

/-- A host frame finished with result `r`, leaving the chain `rest`: pop it; at the bottom of
the chain a returned `Ret.cancel cr` is the `on_cancel` of the latest top-level call. -/
def hostFinish (r : Ret E) (rest : List (Activation E σ)) (m : Config E σ) : Config E σ :=
  match rest, r, lastCall? m with
  | [], .cancel cr, some c => { m with ctl := rest }.setCancel c cr
  | _, _, _ => { m with ctl := rest }

/-- The machine effect of a host-visible observation: a resolution is recorded. -/
def observe (m : Config E σ) : HostObs → Config E σ
  | .resolved c r => m.resolve c r
  | _ => m

/-- The activation saved by a thread executing `block` with continuation `k`. -/
def blockedAct (t : ThreadId) (k : Unit → P E σ (Ret E)) (segs : List (Seg E σ)) :
    Activation E σ :=
  ⟨some t, .prog (k ()), segs⟩

/-- The saved activation of a thread created by `newThread b`. -/
def threadAct (dispatch : Call E → P E σ (Ret E)) (t : ThreadId) (b : ThreadBody E) :
    Activation E σ :=
  .ofProg (some t) (dispatch (.threadBody b))

/-- The host may act: the control chain is empty, the store is not locked down and no host
call is in progress (REF asserts `not lockdown` in `Store.invoke`, `on_cancel` and `Store.tick`,
and `nesting_depth == 0` only in `Store.tick`, L557). -/
def HostReadyCfg (m : Config E σ) : Prop :=
  m.ctl = [] ∧ m.store.lockdown = false ∧ m.store.nestingDepth = 0

instance (m : Config E σ) : Decidable (HostReadyCfg m) := by
  unfold HostReadyCfg; infer_instance

end StepDefs

open StepDefs

/-! ## Faults -/

/-- Violated machine invariants, reported as internal traps (see the module docstring). -/
inductive Fault : Config E σ → String → Prop where
  /-- `block` on a host frame (no REF thread). -/
  | blockNoThread {m : Config E σ} {sw : Option ThreadId} {k : Unit → P E σ (Ret E)}
      {segs rest} :
      m.ctl = ⟨none, .prog (.op (S := Eff E σ) (.block sw) k), segs⟩ :: rest →
      Fault m "block on a host frame"
  /-- The `switch_to` target of `block (some o)` has no saved activation. -/
  | switchMissing {m : Config E σ} {t o : ThreadId} {k : Unit → P E σ (Ret E)} {segs rest} :
      m.ctl = ⟨some t, .prog (.op (S := Eff E σ) (.block (some o)) k), segs⟩ :: rest →
      (m.setCont t (some (blockedAct t k segs))).cont? o = none →
      Fault m "switch to a thread without a saved continuation"
  /-- The target of `resumeThread` has no saved activation. -/
  | resumeMissing {m : Config E σ} {th} {t : ThreadId} {k : Unit → P E σ (Ret E)} {segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.resumeThread t) k), segs⟩ :: rest →
      m.cont? t = none → Fault m "resume of a thread without a saved continuation"
  /-- A callout program returned a result that is not `Ret.flat`. -/
  | calloutBadRet {m : Config E σ} {th} {r : Ret E} {ct} {k : List FlatValue → P E σ (Ret E)}
      {segs rest} :
      m.ctl = ⟨th, .prog (.pure r), .core ct k :: segs⟩ :: rest →
      (∀ vs, r ≠ .flat vs) → Fault m "host callout returned a non-flat result"

/-! ## The step relation -/

/-- One labelled machine transition (see the module docstring for the rule table). -/
inductive Step (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) :
    Config E σ → Label E σ → Config E σ → Prop where
  /-- A program returned to a waiting program continuation. -/
  | popProg {m : Config E σ} {th r k segs rest} :
      m.ctl = ⟨th, .prog (.pure r), .prog k :: segs⟩ :: rest →
      Step prof hr dispatch m .tau { m with ctl := ⟨th, .prog (k r), segs⟩ :: rest }
  /-- A callout program returned flat values: the parked core activation resumes. -/
  | popCore {m : Config E σ} {th vs ct k segs rest} :
      m.ctl = ⟨th, .prog (.pure (.flat vs)), .core ct k :: segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with ctl := ⟨th, .core (E.resume m.store.core ct (.values vs)) k, segs⟩ :: rest }
  /-- The body of thread `t` returned: `t` exits and its resumer continues. -/
  | threadExit {m : Config E σ} {t : ThreadId} {r rest} :
      m.ctl = ⟨some t, .prog (.pure r), []⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with store := threadStatusSt t .exited m.store, ctl := rest }
  /-- A host frame finished; a returned `on_cancel` is recorded for the last invoke. -/
  | hostDone {m : Config E σ} {r rest} :
      m.ctl = ⟨none, .prog (.pure r), []⟩ :: rest →
      Step prof hr dispatch m .tau (hostFinish r rest m)
  /-- A late-bound call: push the continuation, run the dispatched program. -/
  | call {m : Config E σ} {th c k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.call c) k), segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with ctl := ⟨th, .prog (dispatch c), .prog k :: segs⟩ :: rest }
  /-- A core call: start a core activation. -/
  | callCore {m : Config E σ} {th f args k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.callCore f args) k), segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with ctl := ⟨th, .core (E.invoke f args) k, segs⟩ :: rest }
  /-- An internal (host-free) step of the running core activation. -/
  | coreInternal {m : Config E σ} {th ct k segs rest c' ct'} :
      m.ctl = ⟨th, .core ct k, segs⟩ :: rest →
      (E.status m.store.core ct = .running ∨ E.status m.store.core ct = .stuck) →
      E.Internal (m.store.core, ct) (c', ct') →
      Step prof hr dispatch m .core
        { m with store := { m.store with core := c' }, ctl := ⟨th, .core ct' k, segs⟩ :: rest }
  /-- The core activation returned values. -/
  | coreReturned {m : Config E σ} {th ct k segs rest vs} :
      m.ctl = ⟨th, .core ct k, segs⟩ :: rest →
      E.status m.store.core ct = .returned (.values vs) →
      Step prof hr dispatch m .tau { m with ctl := ⟨th, .prog (k vs), segs⟩ :: rest }
  /-- The core activation trapped (or threw): the machine traps. -/
  | coreTrap {m : Config E σ} {th ct k segs rest} :
      m.ctl = ⟨th, .core ct k, segs⟩ :: rest →
      E.status m.store.core ct = .returned .trap →
      Step prof hr dispatch m (.trap .coreTrap) (trapCfg m)
  /-- The core activation called a canon host function: run its callout program (with
  `Canon.dispatch`, `Canon.hostCalloutProg`, which checks the current thread first). -/
  | coreCallout {m : Config E σ} {th ct k segs rest h args} :
      m.ctl = ⟨th, .core ct k, segs⟩ :: rest →
      E.status m.store.core ct = .callout h args →
      Step prof hr dispatch m .tau
        { m with ctl := ⟨th, .prog (dispatch (.hostCallout h args)), .core ct k :: segs⟩ ::
          rest }
  /-- Read the component store. -/
  | get {m : Config E σ} {th k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) .get k), segs⟩ :: rest →
      Step prof hr dispatch m .tau { m with ctl := ⟨th, .prog (k m.store), segs⟩ :: rest }
  /-- Apply a named store update. -/
  | modify {m : Config E σ} {th f k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.modify f) k), segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with store := f m.store, ctl := ⟨th, .prog (k ()), segs⟩ :: rest }
  /-- REF `trap()`: lock the store down and discard every activation. -/
  | trap {m : Config E σ} {th r k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.trap r) k), segs⟩ :: rest →
      Step prof hr dispatch m (.trap r) (trapCfg m)
  /-- A choice: any admissible answer. -/
  | choose {m : Config E σ} {th ck k segs rest} (r : ChoiceKind.Resp ck) :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.choose ck) k), segs⟩ :: rest →
      Allowed prof ck r →
      Step prof hr dispatch m (.choice ck r) { m with ctl := ⟨th, .prog (k r), segs⟩ :: rest }
  /-- REF `current_thread()`: the thread of the running activation. -/
  | currentThread {m : Config E σ} {th k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) .currentThread k), segs⟩ :: rest →
      Step prof hr dispatch m .tau { m with ctl := ⟨th, .prog (k th), segs⟩ :: rest }
  /-- REF `Thread(task, thread_func)`: a new blocked, suspended thread whose saved activation
  runs `dispatch (.threadBody b)`. -/
  | newThread {m : Config E σ} {th b k segs rest s' t} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.newThread b) k), segs⟩ :: rest →
      ArenaField.threads.alloc m.store { task := b.task } = (s', t) →
      Step prof hr dispatch m .tau
        { (m.setCont t (some (threadAct dispatch t b))) with
          store := s', ctl := ⟨th, .prog (k t), segs⟩ :: rest }
  /-- REF `block()`: save the activation, mark the thread blocked, return to the resumer (or
  to the host if there is none). -/
  | block {m : Config E σ} {t : ThreadId} {k segs rest} :
      m.ctl = ⟨some t, .prog (.op (S := Eff E σ) (.block none) k), segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { (m.setCont t (some (blockedAct t k segs))) with
          store := threadStatusSt t .blocked m.store, ctl := rest }
  /-- REF `block(switch_to = o)` (resume site R4): save the activation, mark the thread
  blocked, and run `o`'s saved activation in the same resumer frame. -/
  | blockSwitch {m : Config E σ} {t o : ThreadId} {k segs rest b} :
      m.ctl = ⟨some t, .prog (.op (S := Eff E σ) (.block (some o)) k), segs⟩ :: rest →
      (m.setCont t (some (blockedAct t k segs))).cont? o = some b →
      Step prof hr dispatch m .tau
        { (m.setCont t (some (blockedAct t k segs))).setCont o none with
          store := threadStatusSt o .running (threadStatusSt t .blocked m.store),
          ctl := b :: rest }
  /-- REF `Thread.resume` (resume sites R1-R3): run `t`'s saved activation above the current
  one, which waits for `t` to block or exit. -/
  | resumeThread {m : Config E σ} {th} {t : ThreadId} {k segs rest b} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.resumeThread t) k), segs⟩ :: rest →
      m.cont? t = some b →
      Step prof hr dispatch m .tau
        { (m.setCont t none) with
          store := threadStatusSt t .running m.store,
          ctl := b :: ⟨th, .prog (k ()), segs⟩ :: rest }
  /-- Read the host state. -/
  | hostGet {m : Config E σ} {th k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) .hostGet k), segs⟩ :: rest →
      Step prof hr dispatch m .tau { m with ctl := ⟨th, .prog (k m.host), segs⟩ :: rest }
  /-- Replace the host state. -/
  | hostSet {m : Config E σ} {th s k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.hostSet s) k), segs⟩ :: rest →
      Step prof hr dispatch m .tau
        { m with host := s, ctl := ⟨th, .prog (k ()), segs⟩ :: rest }
  /-- A host-visible observation. -/
  | emit {m : Config E σ} {th o k segs rest} :
      m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.emit o) k), segs⟩ :: rest →
      Step prof hr dispatch m (.obs o)
        { observe m o with ctl := ⟨th, .prog (k ()), segs⟩ :: rest }
  /-- A violated machine invariant: internal trap. -/
  | fault {m : Config E σ} {msg : String} :
      Fault m msg → Step prof hr dispatch m (.trap (.internal msg)) (trapCfg m)
  /-- REF `Store.invoke` (L524-536) of `f` as top-level call `c`. -/
  | hostInvoke {m : Config E σ} {c f args} :
      HostReadyCfg m → (∀ x ∈ m.pending, x.1 ≠ c) →
      Step prof hr dispatch m (.host (.invoke c f args))
        { m with
          pending := m.pending ++ [(c, f, args)]
          ctl := [.ofProg none (invokeProg c f args)] }
  /-- REF `Store.tick` (L555-563); the pick is the choice C2 inside `tickProg`. -/
  | hostTick {m : Config E σ} :
      HostReadyCfg m →
      Step prof hr dispatch m (.host .tick) { m with ctl := [.ofProg none (tickProg hr)] }
  /-- The `on_cancel` of top-level call `c` (REF `Store.invoke`, L530-534). -/
  | hostCancel {m : Config E σ} {c r} :
      HostReadyCfg m → m.cancel? c = some r → m.result? c = none →
      Step prof hr dispatch m (.host (.cancel c))
        { m.dropCancel c with ctl := [.ofProg none (cancelProg r)] }
  /-- Run an instantiation program on a host frame. -/
  | hostRun {m : Config E σ} {p} :
      HostReadyCfg m →
      Step prof hr dispatch m (.host (.run p)) { m with ctl := [.ofProg none (runProg p)] }

/-! ## Traces -/

/-- Finite runs with their label traces. -/
inductive Steps (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) :
    Config E σ → List (Label E σ) → Config E σ → Prop where
  | refl (m : Config E σ) : Steps prof hr dispatch m [] m
  | cons {m₁ m₂ m₃ : Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
      Step prof hr dispatch m₁ l m₂ → Steps prof hr dispatch m₂ tr m₃ →
      Steps prof hr dispatch m₁ (l :: tr) m₃

/-- The unlabelled step relation (host events included). -/
def AnyStep (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (m m' : Config E σ) : Prop :=
  ∃ l, Step prof hr dispatch m l m'

/-- A machine-internal step: any step whose label is not a host event. -/
def InternalStep (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (m m' : Config E σ) : Prop :=
  ∃ l, (∀ ev, l ≠ .host ev) ∧ Step prof hr dispatch m l m'

/-- Guest divergence: an infinite run of internal steps (the host stays passive). -/
def Diverges (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (m : Config E σ) : Prop :=
  InfiniteTrace (InternalStep prof hr dispatch) m

/-- An infinite run that may include host events. This holds for every host-ready
configuration (see the module docstring) and is NOT a nontermination notion. -/
def DivergesWithHost (prof : ProfileKind) (hr : HostReady σ)
    (dispatch : Call E → P E σ (Ret E)) (m : Config E σ) : Prop :=
  InfiniteTrace (AnyStep prof hr dispatch) m

namespace Steps

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

end Steps

/-! ## Label projections -/

/-- The oracle answer recorded by a label, if any. -/
def Label.choice? : Label E σ → Option ChoiceRecord
  | .choice k r => some ⟨k, r⟩
  | _ => none

/-- The host event of a label, if any. -/
def Label.hostEvent? : Label E σ → Option (HostEvent E σ)
  | .host ev => some ev
  | _ => none

/-- The observation of a label, if any. -/
def Label.obs? : Label E σ → Option HostObs
  | .obs o => some o
  | _ => none

/-- The choice log of a trace (the input of `Oracle.replay`). -/
def traceChoices (tr : List (Label E σ)) : List ChoiceRecord := tr.filterMap Label.choice?

/-- The host events of a trace. -/
def traceHostEvents (tr : List (Label E σ)) : List (HostEvent E σ) :=
  tr.filterMap Label.hostEvent?

/-- The observations of a trace. -/
def traceObs (tr : List (Label E σ)) : List HostObs := tr.filterMap Label.obs?

/-- Label projection: choice log of a trace. -/
abbrev Steps.choices (tr : List (Label E σ)) : List ChoiceRecord := traceChoices tr

/-- Label projection: host events of a trace. -/
abbrev Steps.hostEvents (tr : List (Label E σ)) : List (HostEvent E σ) := traceHostEvents tr

/-- Label projection: observations of a trace. -/
abbrev Steps.obs (tr : List (Label E σ)) : List HostObs := traceObs tr

@[simp] theorem traceChoices_append (tr₁ tr₂ : List (Label E σ)) :
    traceChoices (tr₁ ++ tr₂) = traceChoices tr₁ ++ traceChoices tr₂ := by
  simp [traceChoices]

@[simp] theorem traceHostEvents_append (tr₁ tr₂ : List (Label E σ)) :
    traceHostEvents (tr₁ ++ tr₂) = traceHostEvents tr₁ ++ traceHostEvents tr₂ := by
  simp [traceHostEvents]

@[simp] theorem traceObs_append (tr₁ tr₂ : List (Label E σ)) :
    traceObs (tr₁ ++ tr₂) = traceObs tr₁ ++ traceObs tr₂ := by
  simp [traceObs]

/-! ## Terminal predicates -/

/-- Every top-level call resolved, the host is in control and the store is not locked down. -/
def Resolved (m : Config E σ) : Prop :=
  m.ctl = [] ∧ m.store.lockdown = false ∧ m.allResolved = true

/-- The machine trapped (the store is locked down). -/
def Trapped (m : Config E σ) : Prop := m.store.lockdown = true

/-- Some top-level call is unresolved, the host is in control, and no waiting thread is ready
(a tick could only do nothing). Host events remain enabled: this is terminal for internal
steps only (`Step.host_of_ctl_nil`). -/
def Deadlocked (hr : HostReady σ) (m : Config E σ) : Prop :=
  m.ctl = [] ∧ m.store.lockdown = false ∧ (∃ c ∈ m.pending, m.result? c.1 = none) ∧
    m.store.candidates (hr m.host) = []

instance (m : Config E σ) : Decidable (Resolved m) := by unfold Resolved; infer_instance
instance (m : Config E σ) : Decidable (Trapped m) := by unfold Trapped; infer_instance
instance (hr : HostReady σ) (m : Config E σ) : Decidable (Deadlocked hr m) := by
  unfold Deadlocked; infer_instance

/-! ## Basic facts -/

section Basic

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

@[simp] theorem trapCfg_ctl (m : Config E σ) : (trapCfg m).ctl = [] := rfl
@[simp] theorem trapCfg_lockdown (m : Config E σ) : (trapCfg m).store.lockdown = true := rfl

end Basic

/-! ## Example: a top-level call resolved immediately -/

section Examples

variable (prof : ProfileKind) (hr : HostReady σ)

end Examples

end Silmaril.Wasm.Component.Machine

module

public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Wasm.Component.Engine.Laws

/-!
# The executable machine step and fuel runner

The executable half of the component machine: `step?` interprets one operation of the
specification programs `Canon.P E σ` (the REF functions of `definitions.py` at component-model
`a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF") on a configuration `Config E σ` (`Machine/Config.lean`), resolving choices with an
`Oracle` (`Machine/Oracle.lean`) and running core code with an executable engine stepper
`X : E.Exec`. `hostStep?` performs the embedder's actions (`HostEvent`), and `run` /
`runTop` / `runTopCall` are fuel-bounded drivers returning an `Outcome`, the label trace and
the choice log (for replay with `Oracle.replay`).

## Rules of `step?` (head activation `a` of the control chain, the rest `rest`)

Labels are `tau` unless stated otherwise.
* `prog (pure r)` with top segment `prog k`: pop the segment, focus `k r`.
* `prog (pure r)` with top segment `core t k`: if `r = flat vs`, focus
  `core (E.resume t (values vs)) k`; otherwise an internal trap.
* `prog (pure r)`, no segment, thread `t`: thread exit (`t` exited), pop `a`; the resumer
  below continues.
* `prog (pure r)`, no segment, host frame: pop `a`; at the bottom of the chain,
  `r = cancel c'` records the `on_cancel` of the latest top-level call.
* `get` / `modify f`: read / update the store.
* `trap r` (label `trap r`): `lockdown := true`, `ctl := []` (saved continuations are kept).
* `choose k` (label `choice k r`): ask the oracle; stop (`none`) if it failed or the answer
  is not `Allowed o.prof k`.
* `callCore f args`: focus `core (E.invoke f args) k`.
* `call c`: push segment `prog k`, focus `dispatch c`.
* `currentThread`: answer `a.thread`.
* `newThread b`: allocate a `Thread` (blocked, suspended, task `b.task`) and save the
  activation `dispatch (.threadBody b)` as its continuation.
* `block none`: `a.thread = some t` (else internal trap): save `a` in `conts[t]`, `t`
  blocked, pop.
* `block (some o)`: as `block none`, then take `conts[o]` (else internal trap), `o` running,
  push it (same resumer, REF resume site R4).
* `resumeThread t`: take `conts[t]` (else internal trap), `t` running, push it above `a`.
* `hostGet` / `hostSet s`: read / write the host state.
* `emit o` (label `obs o`): `resolved c r` also records the resolution of top-level call `c`.
* `core t k` with status `returned (values vs)`: focus `k vs`; `returned trap`: trap
  `coreTrap`; `callout h args`: push segment `core t k`, focus
  `dispatch (.hostCallout h args)` (with `Canon.dispatch`, `Canon.hostCalloutProg`: the entry
  check `Canon.calloutEntry` on the current thread, then the canon code; the step itself checks
  nothing, so another dispatcher must keep the check, `Canon.withCalloutEntry`); otherwise (label
  `core`): `X.step?` on `(store.core, t)`, whose `none` stops the machine.

`step?` is `none` when the host is in control (`ctl = []`), in particular after a trap
(`step?_lockdown`).

## Host events (`hostStep?`)

Enabled only when `ctl = [] ∧ ¬ lockdown ∧ nestingDepth = 0` (`hostStep?_enabled`); each pushes
one host frame (thread `none`) running a program:
* `invoke c f args` (REF `Store.invoke`, L524-536; `c` must be fresh): record `(c, f, args)` in
  `pending`; the frame allocates the caller `Caller.host c args 0`, then runs
  `nesting_depth += 1; call (.funcInst f caller); nesting_depth -= 1` and returns the
  `Ret.cancel` of the call, which the machine records with `setCancel c`.
* `tick` (REF `Store.tick`, L555-563): `nesting_depth += 1`; if `CStore.candidates` is nonempty,
  pick one (C2, `choose (.tickPick n)`) and run the `Thread.resume` program on it;
  `nesting_depth -= 1`.
* `cancel c` (REF `on_cancel`, L530-534): enabled when `cancel? c = some r` and `c` has not
  resolved (`result? c = none`); consumes the handle (`dropCancel c`) and runs
  `nesting_depth += 1; call (.onCancel r); nesting_depth -= 1`.
* `run p`: runs `p` (instantiation programs, `Embedding.lean`); its result is discarded.

## Drivers

`run hr dispatch X o fuel m` iterates `step?`; `runTop` additionally issues `tick` whenever the
host may act and some waiting thread is ready, also after every top-level call resolved
(run_tests.py `lift_and_run`, L54-58: `while inst.store.waiting: inst.store.tick()`, up to
ticks that would do nothing: REF keeps ticking while a waiting thread is not ready, `runTop`
stops); `runTopCall` issues `invoke c f args` and then `runTop`. `outcomeOf` classifies a
stopped configuration exactly as the terminal predicates of `Machine/Step.lean` (`Deadlocked`:
host in control, not locked down, an unresolved call, no candidate).

## Tests (kernel `rfl`, generic engine `E`, no core code)

With `toyDispatch` (a function value resolves at once through its host caller's `on_resolve`),
`runTopCall` of an invoke ends `resolved` with result `[]`, the `on_cancel` recorded and the
nesting depth restored; a trap ends `trap`; `newThread` + `resumeThread` runs a thread body to
exit; with `yieldDispatch` a thread yields (C1), blocks, and a host `tick` (C2) resumes it to
exit.

## Design notes and non-claims

* The configuration type is `Config E σ` (`Machine/Config.lean`).
* `step?` takes no host readiness; `hostStep?` and the drivers take `hr : HostReady σ` (the one
  fixed `HostReady` of Runtime/Thread.lean used for `CStore.candidates`).
* The `on_cancel` of a top-level invoke is recorded when its host frame, at the bottom of the
  control chain, returns `Ret.cancel r`; the call is the latest entry of `pending` (host frames
  are pushed only by host events, which require an empty chain, so the bottom frame belongs to
  the latest host event; the `tick`/`cancel`/`run` frames return `Ret.unit`).
* Top-level results are recorded by the `emit (.resolved c r)` rule (the dispatcher
  `Canon.dispatch` implements the host caller's `on_resolve` by that emit).
* Violated REF preconditions the machine cannot follow (block on a host frame, resuming or
  switching to a thread without a saved continuation, a non-`flat` callout result) trap with
  `TrapReason.internal` (expected to be unreachable for well-formed runs; not proved here). The
  status of the resumed / switched-to thread is not checked (REF `assert`, deviation D-f).
* A core activation for which `X.step?` returns `none` while not returned nor parked (e.g.
  `stuck`) stops the machine (`step? = none`); `run` reports `Outcome.running`.
* Nothing is proved here about agreement with the relation or invariants.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates of the machine -/

namespace CStoreOps

/-- The machine's update of REF `Thread.cont` (running / exited / blocked) of thread `t`. -/
def setThreadStatus (t : ThreadId) (st : ThreadStatus) (s : CStore E) : CStore E :=
  ArenaField.threads.modify s t fun th => { th with status := st }

/-- REF `trap()` at head: `store.lock_down()`. -/
def lockDown (s : CStore E) : CStore E := { s with lockdown := true }

/-- REF `self.nesting_depth += 1` (`Store.invoke`, `Store.tick`, `on_cancel`). -/
def incNesting (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth + 1 }

/-- REF `self.nesting_depth -= 1`. -/
def decNesting (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth - 1 }

/-- Replace the core store (a core step). -/
def setCore (c : E.Store (CanonHost E)) (s : CStore E) : CStore E := { s with core := c }

end CStoreOps

open CStoreOps

/-! ## Host-frame programs -/

/-- The host frame of `HostEvent.invoke c f args` (REF `Store.invoke`, L524-529): allocate the
host caller record, then `nesting_depth += 1`, `f(on_start, on_resolve)`, `nesting_depth -= 1`;
the result is the call's `Ret.cancel` (its `on_cancel`). -/
def invokeProg (c : CallId) (f : FuncId) (args : List Val) : P E σ (Ret E) := do
  let caller ← allocObj ArenaField.callers (Caller.host c args 0)
  modifyStore incNesting
  let r ← callRet (.funcInst f caller)
  modifyStore decNesting
  pure r

/-- The host frame of `HostEvent.tick` (REF `Store.tick`, L555-563): C2 among the ready
waiting threads, then the `Thread.resume` program. -/
def tickProg (hr : HostReady σ) : P E σ (Ret E) := do
  modifyStore incNesting
  let s ← getStore
  let h ← hostGet
  match s.candidates (hr h) with
  | [] => pure ()
  | c :: cs =>
    let t ← pickTick c cs
    Thread.resume t
  modifyStore decNesting
  pure .unit

/-- The host frame of `HostEvent.cancel` (REF `on_cancel`, L530-534). -/
def cancelProg (r : CancelRef) : P E σ (Ret E) := do
  modifyStore incNesting
  let _ ← callRet (.onCancel r)
  modifyStore decNesting
  pure .unit

/-- The host frame of `HostEvent.run p`: run `p`, discard its result. -/
def runProg (p : P E σ (Ret E)) : P E σ (Ret E) := do
  let _ ← p
  pure .unit

/-! ## Configuration helpers -/

namespace Config

/-- The machine after a trap: the store is locked down and every activation is discarded
(saved continuations are kept). -/
def trapped (m : Config E σ) : Config E σ :=
  { m with store := lockDown m.store, ctl := [] }

/-- Update the store. -/
def mapStore (m : Config E σ) (f : CStore E → CStore E) : Config E σ :=
  { m with store := f m.store }

/-- Replace the control chain. -/
def withCtl (m : Config E σ) (ctl : List (Activation E σ)) : Config E σ := { m with ctl }

/-- The latest top-level call issued by the host. -/
def lastCall? (m : Config E σ) : Option CallId := m.pending.getLast?.map (·.1)

/-- Record the resolution observed by `emit`. -/
def observe (m : Config E σ) : HostObs → Config E σ
  | .resolved c r => m.resolve c r
  | _ => m

/-- Host events are enabled: host in control, not locked down, no nested invocation. -/
def hostReady (m : Config E σ) : Bool :=
  m.ctl.isEmpty && !m.store.lockdown && m.store.nestingDepth == 0

end Config

/-- The result of one machine step: its label, the oracle's next state, the next
configuration. -/
abbrev StepResult (E : CoreEngine) (σ : Type) (S : Type) := Option (Label E σ × S × Config E σ)

section Step

variable (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- A trap transition. -/
def trapStep (m : Config E σ) (r : TrapReason) : StepResult E σ o.State :=
  some (.trap r, o.state, m.trapped)

/-- A silent transition. -/
def tauStep (m : Config E σ) : StepResult E σ o.State := some (.tau, o.state, m)

/-- The head activation `a` finished with result `r` and has no segment left. -/
def finish (m : Config E σ) (a : Activation E σ) (rest : List (Activation E σ)) (r : Ret E) :
    StepResult E σ o.State :=
  match a.thread with
  | some t => tauStep o ((m.mapStore (setThreadStatus t .exited)).withCtl rest)
  | none =>
    let m' := m.withCtl rest
    match rest, r, m.lastCall? with
    | [], .cancel cr, some c => tauStep o (m'.setCancel c cr)
    | _, _, _ => tauStep o m'

/-- The head activation `a` returns `r` to its top segment. -/
def retStep (m : Config E σ) (a : Activation E σ) (rest : List (Activation E σ)) (r : Ret E) :
    StepResult E σ o.State :=
  match a.segs with
  | .prog k :: segs => tauStep o (m.withCtl ({ a with focus := .prog (k r), segs } :: rest))
  | .core t k :: segs =>
    match r with
    | .flat vs =>
      tauStep o (m.withCtl
        ({ a with focus := .core (E.resume m.store.core t (.values vs)) k, segs } :: rest))
    | _ => trapStep o m (.internal "host callout returned a non-flat result")
  | [] => finish o m a rest r

/-- Save the head activation (continuing with `k ()`) of thread `t` and block it. -/
def blockSave (m : Config E σ) (a : Activation E σ) (t : ThreadId) (k : Unit → P E σ (Ret E)) :
    Config E σ :=
  (m.setCont t (some { a with focus := .prog (k ()) })).mapStore (setThreadStatus t .blocked)

/-- Interpret operation `op` issued by the head activation `a` with continuation `k`. -/
def opStep (m : Config E σ) (a : Activation E σ) (rest : List (Activation E σ)) :
    (op : Op E σ) → (Op.Resp op → P E σ (Ret E)) → StepResult E σ o.State
  | .get, k => tauStep o (m.withCtl ({ a with focus := .prog (k m.store) } :: rest))
  | .modify f, k =>
    tauStep o ((m.mapStore f).withCtl ({ a with focus := .prog (k ()) } :: rest))
  | .trap r, _ => trapStep o m r
  | .choose kd, k =>
    let ans := o.answer o.state m.store kd
    if o.failed ans.2 then none
    else if Allowed o.prof kd ans.1 then
      some (.choice kd ans.1, ans.2, m.withCtl ({ a with focus := .prog (k ans.1) } :: rest))
    else none
  | .callCore f args, k =>
    tauStep o (m.withCtl ({ a with focus := .core (E.invoke f args) k } :: rest))
  | .call c, k =>
    tauStep o (m.withCtl ({ a with focus := .prog (dispatch c), segs := .prog k :: a.segs } ::
      rest))
  | .currentThread, k => tauStep o (m.withCtl ({ a with focus := .prog (k a.thread) } :: rest))
  | .newThread b, k =>
    let r := ArenaField.threads.alloc m.store ({ task := b.task } : Thread)
    let t := r.2
    let m' := ({ m with store := r.1 }).setCont t
      (some (Activation.ofProg (some t) (dispatch (.threadBody b))))
    tauStep o (m'.withCtl ({ a with focus := .prog (k t) } :: rest))
  | .block sw, k =>
    match a.thread with
    | none => trapStep o m (.internal "block on a host frame")
    | some t =>
      let m₁ := blockSave m a t k
      match sw with
      | none => tauStep o (m₁.withCtl rest)
      | some u =>
        match m₁.cont? u with
        | none => trapStep o m (.internal "switch to a thread without a saved continuation")
        | some au =>
          tauStep o (((m₁.setCont u none).mapStore (setThreadStatus u .running)).withCtl
            (au :: rest))
  | .resumeThread u, k =>
    match m.cont? u with
    | none => trapStep o m (.internal "resume of a thread without a saved continuation")
    | some au =>
      tauStep o (((m.setCont u none).mapStore (setThreadStatus u .running)).withCtl
        (au :: { a with focus := .prog (k ()) } :: rest))
  | .hostGet, k => tauStep o (m.withCtl ({ a with focus := .prog (k m.host) } :: rest))
  | .hostSet s, k =>
    tauStep o ({ m with host := s }.withCtl ({ a with focus := .prog (k ()) } :: rest))
  | .emit ob, k =>
    some (.obs ob, o.state, (m.observe ob).withCtl ({ a with focus := .prog (k ()) } :: rest))

/-- One step of a core activation `t` (continuation `k`) at the head. A callout runs the
dispatched program `dispatch (.hostCallout h args)`, which (for `Canon.dispatch`) checks the
current thread before any canon code runs (`Canon.calloutEntry`). -/
def coreStep (m : Config E σ) (a : Activation E σ) (rest : List (Activation E σ))
    (t : E.Thread (CanonHost E)) (k : List FlatValue → P E σ (Ret E)) :
    StepResult E σ o.State :=
  match E.status m.store.core t with
  | .returned (.values vs) => tauStep o (m.withCtl ({ a with focus := .prog (k vs) } :: rest))
  | .returned .trap => trapStep o m .coreTrap
  | .callout h args =>
    let a' : Activation E σ :=
      { a with focus := .prog (dispatch (.hostCallout h args)), segs := .core t k :: a.segs }
    tauStep o (m.withCtl (a' :: rest))
  | _ =>
    match X.step? (m.store.core, t) with
    | some (c', t') =>
      some (.core, o.state,
        (m.mapStore (setCore c')).withCtl ({ a with focus := .core t' k } :: rest))
    | none => none

/-- One machine step (see the rule table in the module docstring); `none` when the host is in
control or the machine is stuck (failed or inadmissible oracle answer, stuck core code). -/
def step? (m : Config E σ) : StepResult E σ o.State :=
  match m.ctl with
  | [] => none
  | a :: rest =>
    match a.focus with
    | .prog (.pure r) => retStep o m a rest r
    | .prog (.op op k) => opStep dispatch o m a rest op k
    | .core t k => coreStep dispatch X o m a rest t k

end Step

/-- A host event (see the module docstring); `none` when not enabled. The oracle is not
consulted (the tick choice C2 is a `choose` of the tick program). -/
def hostStep? (hr : HostReady σ) (ev : HostEvent E σ) (m : Config E σ) :
    Option (Label E σ × Config E σ) :=
  if m.hostReady then
    match ev with
    | .invoke c f args =>
      if m.pending.any (·.1 == c) then none
      else
        let m' : Config E σ := { m with pending := m.pending ++ [(c, f, args)] }
        some (.host ev, m'.withCtl [Activation.ofProg none (invokeProg c f args)])
    | .tick => some (.host ev, m.withCtl [Activation.ofProg none (tickProg hr)])
    | .cancel c =>
      match m.cancel? c, m.result? c with
      | some r, none =>
        some (.host ev, (m.dropCancel c).withCtl [Activation.ofProg none (cancelProg r)])
      | _, _ => none
    | .run p => some (.host ev, m.withCtl [Activation.ofProg none (runProg p)])
  else none

/-! ## Basic lemmas -/

section Lemmas

variable (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- With the host in control, the machine takes no internal step. -/
@[simp] theorem step?_nil (m : Config E σ) (h : m.ctl = []) : step? dispatch X o m = none := by
  simp [step?, h]

end Lemmas

/-! ## Drivers -/

/-- The choices recorded in a label trace (for `Oracle.replay`). -/
def choiceLog : List (Label E σ) → List ChoiceRecord
  | [] => []
  | .choice k r :: ls => ⟨k, r⟩ :: choiceLog ls
  | _ :: ls => choiceLog ls

/-- The outcome of a configuration in which the machine stopped (cf. the terminal predicates of
`Machine/Step.lean`). -/
def outcomeOf (hr : HostReady σ) (m : Config E σ) : Outcome :=
  if m.store.lockdown then .trap
  else if !m.ctl.isEmpty then .running
  else if m.allResolved then .resolved
  else if (m.store.candidates (hr m.host)).isEmpty then .deadlock
  else .running

/-- The result of a bounded run. -/
structure RunResult (E : CoreEngine) (σ : Type) (S : Type) where
  /-- How the run ended. -/
  outcome : Outcome
  /-- The final configuration. -/
  config : Config E σ
  /-- The final oracle state. -/
  state : S
  /-- The labels of the run, in order. -/
  labels : List (Label E σ)

/-- The choice log of a run (replayable with `Oracle.replay`). -/
def RunResult.choices {S : Type} (r : RunResult E σ S) : List ChoiceRecord :=
  choiceLog r.labels

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- The oracle `o` restarted at state `st`. -/
def Oracle.at (o : Oracle E) (st : o.State) : Oracle E := { o with state := st }

/-- Internal steps only, labels accumulated in reverse. -/
def runLoop : Nat → o.State → Config E σ → List (Label E σ) →
    RunResult E σ o.State
  | 0, st, m, acc =>
    { outcome := if (step? dispatch X (o.at st) m).isSome then .outOfFuel else outcomeOf hr m,
      config := m, state := st, labels := acc.reverse }
  | n + 1, st, m, acc =>
    match step? dispatch X (o.at st) m with
    | some (l, st', m') => runLoop n st' m' (l :: acc)
    | none => { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }

/-- Run internal steps from `m` with at most `fuel` steps. -/
def run (fuel : Nat) (m : Config E σ) : RunResult E σ o.State :=
  runLoop hr dispatch X o fuel o.state m []

/-- The harness wants a `Store.tick`: the host may act and a waiting thread is ready
(run_tests.py `while inst.store.waiting: inst.store.tick()`, minus the no-op ticks; post-return
work of resolved calls is driven too). -/
def wantsTick (m : Config E σ) : Bool :=
  m.hostReady && !(m.store.candidates (hr m.host)).isEmpty

/-- Internal steps, and `tick` whenever `wantsTick` (run_tests.py's driving loop, without its
no-op ticks). -/
def runTopLoop : Nat → o.State → Config E σ → List (Label E σ) →
    RunResult E σ o.State
  | 0, st, m, acc =>
    { outcome := if (step? dispatch X (o.at st) m).isSome || wantsTick hr m then .outOfFuel
        else outcomeOf hr m,
      config := m, state := st, labels := acc.reverse }
  | n + 1, st, m, acc =>
    match step? dispatch X (o.at st) m with
    | some (l, st', m') => runTopLoop n st' m' (l :: acc)
    | none =>
      if wantsTick hr m then
        match hostStep? hr .tick m with
        | some (l, m') => runTopLoop n st m' (l :: acc)
        | none => { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }
      else { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }

/-- Run from `m` with ticks, at most `fuel` steps. -/
def runTop (fuel : Nat) (m : Config E σ) : RunResult E σ o.State :=
  runTopLoop hr dispatch X o fuel o.state m []

/-- Issue the top-level call `c` of `f` on `args` (`HostEvent.invoke`), then `runTop`;
`none` if the invoke is not enabled. The invoke label heads the trace. -/
def runTopCall (fuel : Nat) (c : CallId) (f : FuncId) (args : List Val) (m : Config E σ) :
    Option (RunResult E σ o.State) :=
  (hostStep? hr (.invoke c f args) m).map fun (l, m') =>
    runTopLoop hr dispatch X o fuel o.state m' [l]

end Drivers

/-! ## Tests -/

section Tests

/-- A toy dispatcher: a function value resolves immediately with no results (through the host
caller's `on_resolve`, which emits `resolved`); every other call returns `unit`. -/
def toyDispatch : Call E → P E σ (Ret E)
  | .funcInst _ caller => do
    callUnit (.onResolve caller (some []))
    pure (.cancel .none)
  | .onResolve c r => do
    match ← getObj ArenaField.callers c with
    | .host call _ _ => emit (.resolved call r)
    | _ => pure ()
    pure .unit
  | _ => pure .unit

variable (X : E.Exec)

/-- A dispatcher whose thread bodies yield once (REF `Thread.yield_`, C1 at K9) and exit. -/
def yieldDispatch : Call E → P E σ (Ret E)
  | .threadBody _ => do
    Thread.yield_
    pure .unit
  | _ => pure .unit

end Tests

end Silmaril.Wasm.Component.Machine

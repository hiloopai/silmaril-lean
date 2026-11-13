module

public import Silmaril.Wasm.Component.Reference.Machine.Exec.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs

public import Silmaril.Raw.Wasm.Component.Machine.Config
public import Silmaril.Raw.Wasm.Component.Machine.Oracle
public import Silmaril.Raw.Wasm.Component.Runtime.Thread
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

end CStoreOps

open CStoreOps

/-! ## Host-frame programs -/

/-! ## Configuration helpers -/

namespace Config

end Config

section Step

variable (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end Step

/-! ## Basic lemmas -/

section Lemmas

variable (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- After a trap (locked down, empty chain) the machine takes no step. -/
theorem step?_lockdown (m : Config E σ) (_ : m.store.lockdown = true) (h : m.ctl = []) :
    step? dispatch X o m = none := step?_nil dispatch X o m h

/-- A locked-down store admits no host event. -/
theorem hostStep?_lockdown (hr : HostReady σ) (ev : HostEvent E σ) (m : Config E σ)
    (h : m.store.lockdown = true) : hostStep? hr ev m = none := by
  cases e : hostStep? hr ev m with
  | none => rfl
  | some r => simp [(hostStep?_enabled e).2.1] at h

/-- A trap step locks the store down and empties the control chain. -/
theorem trapStep_spec (m : Config E σ) (r : TrapReason) :
    trapStep (σ := σ) o m r = some (.trap r, o.state, m.trapped) ∧ m.trapped.ctl = [] ∧
      m.trapped.store.lockdown = true := ⟨rfl, rfl, rfl⟩

end Lemmas

/-! ## Drivers -/

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end Drivers

/-! ## Tests -/

section Tests

variable (X : E.Exec)

private def noHostReady : HostReady Unit := fun _ _ => false

private def invokeRun : Option (RunResult E Unit Unit) :=
  runTopCall noHostReady toyDispatch X (Oracle.first (E := E)) 50 ⟨0⟩ ⟨0⟩ []
    (Config.init CStore.empty ())

/-- Invoke → resolved: the top-level call resolves with no results and the run ends
`resolved`. -/
example : (invokeRun X).map (·.outcome) = some .resolved := rfl

example : (invokeRun X).map (·.config.result? ⟨0⟩) = some (some (some [])) := rfl

/-- The `on_cancel` of the call is recorded, the nesting depth is restored, and the run made no
choice. -/
example : (invokeRun X).map (fun r => (r.config.cancel? ⟨0⟩, r.config.store.nestingDepth,
    r.choices.length, r.config.ctl.length)) = some (some .none, 0, 0, 0) := rfl

/-- The trace: the invoke, then only silent steps around one `resolved` observation. -/
example : (invokeRun X).map (fun r => (r.labels.length, r.labels.countP (· matches .obs _),
    r.labels.countP (· matches .host _), r.labels.countP (· matches .tau))) =
    some (12, 1, 1, 10) := rfl

/-- A second invoke of the same call id is not enabled. -/
example : ((invokeRun X).bind fun r =>
    hostStep? noHostReady (.invoke ⟨0⟩ ⟨0⟩ []) r.config).isNone = true := rfl

/-- A trap locks the store down and stops the machine. -/
example : (runTop noHostReady (toyDispatch (E := E)) X (Oracle.first (E := E)) 10
    ({ (Config.init CStore.empty ()) with
      ctl := [Activation.ofProg none (Canon.trap .deadlock)] })).outcome = .trap := rfl

/-- `newThread` then `resumeThread` from a host frame runs the thread body (`toyDispatch` of
`threadBody` returns at once), which exits (no block, no tick; see `yieldDispatch` for that). -/
example : (run noHostReady (toyDispatch (E := E)) X (Oracle.first (E := E)) 20
    ({ (Config.init ({ CStore.empty with tasks := [] } : CStore E) ()) with
      ctl := [Activation.ofProg none (do
        let t ← Canon.newThread (.host ⟨0⟩ ⟨0⟩)
        Canon.resumeThread t
        pure .unit)] })).config.store.threads.map (·.status) = [.exited] := rfl

private def yieldStart : Config E Unit :=
  { (Config.init CStore.empty ()) with
    ctl := [Activation.ofProg none (do
      let t ← Canon.newThread (.host ⟨0⟩ ⟨0⟩)
      Canon.resumeThread t
      pure .unit)] }

private def yieldAfterFrame : RunResult E Unit Unit :=
  run noHostReady (yieldDispatch (E := E)) X (Oracle.first (E := E)) 40 yieldStart

/-- The thread yields: it is blocked, waiting on `.always`, with a saved continuation; the host
frame finished; the only choice so far is C1 (answered `false`: block). -/
example : ((yieldAfterFrame X).config.store.threads.map (·.status),
    (yieldAfterFrame X).config.store.waiting, ((yieldAfterFrame X).config.cont? ⟨0⟩).isSome,
    (yieldAfterFrame X).config.ctl.length, (yieldAfterFrame X).choices.length) =
    ([.blocked], [⟨0⟩], true, 0, 1) := rfl

private def yieldAfterTick : Option (RunResult E Unit Unit) :=
  (hostStep? noHostReady .tick (yieldAfterFrame X).config).map fun (_, m) =>
    run noHostReady (yieldDispatch (E := E)) X (Oracle.first (E := E)) 40 m

/-- A `Store.tick` picks the ready thread (C2), resumes it (`stop_waiting` first), and the
thread exits; the nesting depth is restored. -/
example : (yieldAfterTick X).map (fun r => (r.config.store.threads.map (·.status),
    r.config.store.waiting, r.config.store.nestingDepth, r.config.ctl.length,
    r.choices.length)) = some ([.exited], [], 0, 0, 1) := rfl

/-- `runTop` ticks while a waiting thread is ready even when no top-level call is unresolved
(run_tests.py drives on `store.waiting`): the yielded thread is resumed and exits. -/
example : (runTop noHostReady (yieldDispatch (E := E)) X (Oracle.first (E := E)) 80
    yieldStart).config.store.threads.map (·.status) = [.exited] := rfl

end Tests

end Silmaril.Wasm.Component.Machine

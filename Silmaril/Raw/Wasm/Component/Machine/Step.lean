module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

public import Silmaril.Raw.Wasm.Component.Machine.Config
public import Silmaril.Raw.Wasm.Component.Machine.Oracle
public import Silmaril.Raw.Wasm.Component.Runtime.Thread
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

end StepDefs

open StepDefs

/-! ## Faults -/

/-! ## The step relation -/

/-! ## Traces -/

namespace Steps

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem single {m m' : Config E σ} {l : Label E σ} (h : Step prof hr dispatch m l m') :
    Steps prof hr dispatch m [l] m' :=
  .cons h (.refl _)

theorem trans {m₁ m₂ m₃ : Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : Steps prof hr dispatch m₁ tr₁ m₂)
    (h₂ : Steps prof hr dispatch m₂ tr₂ m₃) :
    Steps prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons s _ ih => exact .cons s (ih h₂)

theorem snoc {m₁ m₂ m₃ : Config E σ} {tr : List (Label E σ)} {l : Label E σ}
    (h₁ : Steps prof hr dispatch m₁ tr m₂) (h₂ : Step prof hr dispatch m₂ l m₃) :
    Steps prof hr dispatch m₁ (tr ++ [l]) m₃ :=
  h₁.trans (single h₂)

theorem nil_iff {m m' : Config E σ} : Steps prof hr dispatch m [] m' ↔ m = m' := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .refl _

theorem append_iff {m m' : Config E σ} {tr₁ tr₂ : List (Label E σ)} :
    Steps prof hr dispatch m (tr₁ ++ tr₂) m' ↔
      ∃ m₁, Steps prof hr dispatch m tr₁ m₁ ∧ Steps prof hr dispatch m₁ tr₂ m' := by
  induction tr₁ generalizing m with
  | nil => simp only [List.nil_append, nil_iff, exists_eq_left']
  | cons l tr ih =>
    simp only [List.cons_append, cons_iff, ih]
    constructor
    · rintro ⟨a, s, b, r₁, r₂⟩; exact ⟨b, ⟨a, s, r₁⟩, r₂⟩
    · rintro ⟨b, ⟨a, s, r₁⟩, r₂⟩; exact ⟨a, s, b, r₁, r₂⟩

/-- Forget the labels. -/
theorem toReflTransGen {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') :
    Relation.ReflTransGen (AnyStep prof hr dispatch) m m' := by
  induction h with
  | refl => exact .refl
  | cons s _ ih => exact Relation.ReflTransGen.head ⟨_, s⟩ ih

/-- Every unlabelled run has a label trace. -/
theorem of_reflTransGen {m m' : Config E σ}
    (h : Relation.ReflTransGen (AnyStep prof hr dispatch) m m') :
    ∃ tr, Steps prof hr dispatch m tr m' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .refl _⟩
  | head s _ ih =>
    obtain ⟨l, s⟩ := s
    obtain ⟨tr, r⟩ := ih
    exact ⟨l :: tr, .cons s r⟩

/-- A host-event-free run is a run of internal steps. -/
theorem toInternal {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') (hi : ∀ l ∈ tr, ∀ ev, l ≠ .host ev) :
    Relation.ReflTransGen (InternalStep prof hr dispatch) m m' := by
  induction h with
  | refl => exact .refl
  | cons s _ ih =>
    exact Relation.ReflTransGen.head
      ⟨_, hi _ List.mem_cons_self, s⟩ (ih fun l hl => hi l (List.mem_cons_of_mem _ hl))

/-- A divergent configuration reached by a host-event-free run makes the start divergent. -/
theorem diverges {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') (hi : ∀ l ∈ tr, ∀ ev, l ≠ .host ev)
    (d : Diverges prof hr dispatch m') : Diverges prof hr dispatch m :=
  InfiniteTrace.of_steps (h.toInternal hi) d

/-- The host-inclusive version of `diverges` (any finite prefix). -/
theorem divergesWithHost {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') (d : DivergesWithHost prof hr dispatch m') :
    DivergesWithHost prof hr dispatch m :=
  InfiniteTrace.of_steps h.toReflTransGen d

end Steps

/-! ## Label projections -/

/-! ## Terminal predicates -/

/-! ## Basic facts -/

section Basic

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

/-- Every choice step answers admissibly. -/
theorem Step.choice_allowed {m m' : Config E σ} {k : ChoiceKind} {r : k.Resp}
    (h : Step prof hr dispatch m (.choice k r) m') : Allowed prof k r := by
  cases h
  assumption

/-- A trap label locks the store down and empties the control chain. -/
theorem Step.trap_lockdown {m m' : Config E σ} {r : TrapReason}
    (h : Step prof hr dispatch m (.trap r) m') : m'.store.lockdown = true ∧ m'.ctl = [] := by
  cases h <;> exact ⟨rfl, rfl⟩

end Basic

/-! ## Example: a top-level call resolved immediately -/

section Examples

variable (prof : ProfileKind) (hr : HostReady σ)

/-- A dispatcher whose every call returns `Ret.cancel .none` at once. -/
private def immediate : Call E → P E σ (Ret E) := fun _ => pure (.cancel .none)

/-- `invoke` of a function value whose call returns at once: eight steps, back to the host,
with the `on_cancel` recorded and the nesting depth restored. -/
example (m : Config E σ) (c : CallId) (f : FuncId) (args : List Val) (hm : HostReadyCfg m)
    (hfresh : ∀ x ∈ m.pending, x.1 ≠ c) :
    ∃ m', Steps prof hr immediate m
      [.host (.invoke c f args), .tau, .tau, .tau, .tau, .tau, .tau, .tau] m' ∧
      m'.ctl = [] ∧ m'.cancel? c = some .none ∧
      m'.store.nestingDepth = 0 := by
  obtain ⟨hc, hl, hd⟩ := hm
  refine Exists.intro ?w (And.intro ?s ?r)
  case s =>
    refine .cons (.hostInvoke (f := f) ⟨hc, hl, hd⟩ hfresh) ?_
    refine .cons (.get rfl) ?_
    refine .cons (.modify rfl) ?_
    refine .cons (.modify rfl) ?_
    refine .cons (.call rfl) ?_
    refine .cons (.popProg rfl) ?_
    refine .cons (.modify rfl) ?_
    refine .cons (.hostDone rfl) ?_
    exact .refl _
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hostFinish, lastCall?, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.map_some]
  · rfl
  · exact Config.cancel?_setCancel_self _ _ _
  · simp [Config.setCancel, enterHostSt, leaveHostSt, ArenaOps.allocSt, ArenaField.alloc,
      ArenaField.callers, hd]

end Examples

end Silmaril.Wasm.Component.Machine

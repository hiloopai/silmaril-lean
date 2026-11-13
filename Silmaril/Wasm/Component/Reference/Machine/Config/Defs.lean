module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs

/-!
# Machine configurations, host events, labels and outcomes

The specification programs `Canon.P E σ` (the REF functions of `definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
are run by a machine that interprets the operations `Canon.Op E σ`. This file fixes the
machine's configuration; the executable step is `Machine/Exec.lean` and the relation
`Machine/Step.lean`.

## Configuration

* A running **activation** (`Activation`) is a `Focus` (the program or core thread executing
  now) and a stack of `Seg`ments (what to do with its result), plus the REF thread it runs on
  (`none` for host frames, e.g. a top-level host call before a thread exists).
  * `Focus.prog p`: the program `p` runs; its `Ret` result goes to the top segment.
  * `Focus.core t k`: the core activation `t` (of the engine, over canon host sites
    `CanonHost E`) runs; its returned values go to `k` (the continuation of `Op.callCore`).
  * `Seg.prog k`: a program waiting for the result of a late-bound call (`Op.call`).
  * `Seg.core t k`: a core activation `t` parked on a host callout (REF: core code calling a
    canon host function, `Store.lower`'s `core_func_inst`); the `Ret.flat` result of the callout
    program resumes `t` (`E.resume`), whose returned values then go to `k`.
  An activation with an empty segment stack whose focus returns has finished.
* **Blocked threads' continuations** live in `Config.conts`, indexed by `ThreadId`, and never
  in the component store `CStore E` (issue #477; the REF keeps them in `Thread.cont`, L279-390).
* **The control chain** `Config.ctl`: its head is the running activation. The activations below
  it are suspended *resumers*: an activation that issued `Op.resumeThread t` (REF
  `Thread.resume`, resume sites R1-R4) keeps its continuation `Focus.prog (k ())` below the
  resumed thread's activation, and runs again when that thread blocks or finishes (REF: `resume`
  returns when the resumed thread suspends). An empty chain means the host is in control.
* `Config.pending` records top-level calls issued by the host (`HostEvent.invoke`) and
  `Config.results` their resolutions (REF `on_resolve`: `none` means cancelled).
* `Config.cancels` records, per top-level call, the `CancelRef` that REF `Store.invoke`
  (L524-536) wraps into the returned `on_cancel`: when the host activation of
  `HostEvent.invoke c f args` (running `call (.funcInst f caller)`) returns `Ret.cancel r`, the
  machine records `(c, r)` with `setCancel`; `HostEvent.cancel c` then looks it up with
  `cancel?` and runs `call (.onCancel r)` bracketed by `nesting_depth += 1 / -= 1` (REF
  L530-534).
* REF `Store.nesting_depth` (reentrant host invocations) lives in `CStore.nestingDepth`, not here.

## Host events, labels, outcomes

`HostEvent` are the embedder's actions (REF `Store.invoke`, `Store.tick`, cancelling a
top-level call via its `on_cancel`, and running an instantiation program supplied by the embedding,
`Embedding.lean`). `Label` labels machine transitions; `Label.obs` reuses `Canon.HostObs`. `Outcome`
summarises a bounded run.

## Design notes

* The configuration structure is `Machine.Config E σ`, not `Machine E σ`: a structure
  `Machine` inside namespace `Machine` fails the `dupNamespace` linter.

* `Seg.resumer` is not a segment: resumers are the non-head activations of `ctl` (above).
* `Focus.core` carries the continuation `k` of the returned values, so `Seg.core` is only used
  for a core activation parked on a callout.
* `HostEvent.run p` is the instantiation event; `HostEvent.instantiate` is an alias.

Not modelled or claimed here: any transition, invariants of configurations,
or the choice of the oracle (`Machine/Oracle.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable (E : CoreEngine) (σ : Type)

/-- What an activation executes now. -/
inductive Focus where
  /-- A specification program; its result goes to the top segment. -/
  | prog (p : P E σ (Ret E))
  /-- A core activation; its returned values go to `k`. -/
  | core (t : E.Thread (CanonHost E)) (k : List FlatValue → P E σ (Ret E))

/-- A pending continuation of an activation. -/
inductive Seg where
  /-- A program waiting for the result of a late-bound call. -/
  | prog (k : Ret E → P E σ (Ret E))
  /-- A core activation `t` parked on a host callout: the callout's `Ret.flat` resumes `t`,
  whose returned values go to `k`. -/
  | core (t : E.Thread (CanonHost E)) (k : List FlatValue → P E σ (Ret E))

/-- An activation: the REF thread it runs on (`none`: a host frame), its focus and its segment
stack (head = innermost). -/
structure Activation where
  /-- The REF thread (`none` for host frames). -/
  thread : Option ThreadId
  /-- What executes now. -/
  focus : Focus E σ
  /-- Pending continuations, innermost first. -/
  segs : List (Seg E σ) := []

/-- A machine configuration (see the module docstring). -/
structure Config where
  /-- The component store (including the shared core store). -/
  store : CStore E
  /-- The host (embedder / test harness) state. -/
  host : σ
  /-- Saved activations of blocked threads, indexed by `ThreadId.idx`. -/
  conts : List (Option (Activation E σ)) := []
  /-- The control chain: head = running; the rest are suspended resumers; empty = host. -/
  ctl : List (Activation E σ) := []
  /-- Top-level calls issued by the host (REF `Store.invoke`), in issue order. -/
  pending : List (CallId × FuncId × List Val) := []
  /-- Resolutions of top-level calls (`none`: cancelled). -/
  results : List (CallId × Option (List Val)) := []
  /-- The `on_cancel` of each top-level call (REF `Store.invoke` L530-534), as the `CancelRef`
  returned (`Ret.cancel`) by the call's `funcInst` activation. Latest entry first. -/
  cancels : List (CallId × CancelRef) := []

/-- Actions of the host (embedder). -/
inductive HostEvent where
  /-- REF `Store.invoke` (L524-536) of function value `f` as top-level call `call`. -/
  | invoke (call : CallId) (f : FuncId) (args : List Val)
  /-- REF `Store.tick` (L555-563). -/
  | tick
  /-- The `on_cancel` returned by REF `Store.invoke` (L530-534) for top-level call `call`: runs
  `call (.onCancel r)` for `r = cancel? call` (see `Config.cancels`). -/
  | cancel (call : CallId)
  /-- Run an instantiation program (supplied by the embedding) on a host frame. -/
  | run (p : P E σ (Ret E))

/-- Transition labels. -/
inductive Label where
  /-- An internal step of the specification program. -/
  | tau
  /-- An oracle answer `r` to the choice `k`. -/
  | choice (k : ChoiceKind) (r : k.Resp)
  /-- A host action. -/
  | host (ev : HostEvent E σ)
  /-- A host-visible observation (`Op.emit`). -/
  | obs (o : HostObs)
  /-- A trap (the store is locked down). -/
  | trap (r : TrapReason)
  /-- An internal step of a core activation. -/
  | core

/-- The label is a trap with an `internal` reason: a model fault (an unmodelled feature or a
violated invariant), not a specification trap. -/
def Label.isInternalTrap {E : CoreEngine} {σ : Type} : Label E σ → Bool
  | .trap (.internal _) => true
  | _ => false

/-- The outcome of a bounded run. -/
inductive Outcome where
  /-- Every top-level call resolved and the host is in control. -/
  | resolved
  /-- The machine trapped. -/
  | trap
  /-- Some top-level call is unresolved and no thread can make progress. -/
  | deadlock
  /-- The fuel ran out. -/
  | outOfFuel
  /-- The run stopped (e.g. waiting for a host event) with work remaining. -/
  | running
  deriving DecidableEq, Repr

variable {E σ}

/-- The instantiation event (alias of `HostEvent.run`). -/
abbrev HostEvent.instantiate (p : P E σ (Ret E)) : HostEvent E σ := .run p

namespace Activation

/-- A fresh activation running program `p` on thread `t`. -/
def ofProg (t : Option ThreadId) (p : P E σ (Ret E)) : Activation E σ :=
  { thread := t, focus := .prog p }

/-- Push a segment. -/
def push (a : Activation E σ) (s : Seg E σ) : Activation E σ := { a with segs := s :: a.segs }

/-- Replace the focus. -/
def withFocus (a : Activation E σ) (f : Focus E σ) : Activation E σ := { a with focus := f }

@[simp] theorem push_segs (a : Activation E σ) (s : Seg E σ) : (a.push s).segs = s :: a.segs :=
  rfl
@[simp] theorem push_thread (a : Activation E σ) (s : Seg E σ) : (a.push s).thread = a.thread :=
  rfl
@[simp] theorem withFocus_thread (a : Activation E σ) (f : Focus E σ) :
    (a.withFocus f).thread = a.thread := rfl

end Activation

namespace Config

/-- The initial machine: the host is in control, nothing saved, nothing pending. -/
def init (store : CStore E) (host : σ) : Config E σ := { store, host }

/-- The saved activation of thread `t`, if any. -/
def cont? (m : Config E σ) (t : ThreadId) : Option (Activation E σ) := (m.conts[t.idx]?).join

/-- Write slot `i` of a slot list, padding with `none`. -/
def setSlot {α : Type} : List (Option α) → Nat → Option α → List (Option α)
  | [], 0, v => [v]
  | [], i + 1, v => none :: setSlot [] i v
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: setSlot xs i v

theorem getElem?_setSlot_self {α : Type} (xs : List (Option α)) (i : Nat) (v : Option α) :
    ((setSlot xs i v)[i]?).join = v := by
  induction xs generalizing i with
  | nil =>
    induction i with
    | zero => simp [setSlot]
    | succ i ih => simpa [setSlot] using ih
  | cons x xs ih =>
    cases i with
    | zero => simp [setSlot]
    | succ i => simpa [setSlot] using ih i

/-- Save (or with `none`, clear) the continuation of thread `t`. -/
def setCont (m : Config E σ) (t : ThreadId) (a : Option (Activation E σ)) : Config E σ :=
  { m with conts := setSlot m.conts t.idx a }

@[simp] theorem cont?_setCont_self (m : Config E σ) (t : ThreadId)
    (a : Option (Activation E σ)) : (m.setCont t a).cont? t = a :=
  getElem?_setSlot_self _ _ _

/-- Take the saved continuation of `t`, clearing its slot. -/
def takeCont? (m : Config E σ) (t : ThreadId) : Option (Activation E σ × Config E σ) :=
  (m.cont? t).map fun a => (a, m.setCont t none)

/-- The running activation (`none`: the host is in control). -/
def running? (m : Config E σ) : Option (Activation E σ) := m.ctl.head?

/-- The host is in control (the control chain is empty). -/
def hostInControl (m : Config E σ) : Bool := m.ctl.isEmpty

/-- Record the resolution of top-level call `c`. -/
def resolve (m : Config E σ) (c : CallId) (r : Option (List Val)) : Config E σ :=
  { m with results := m.results ++ [(c, r)] }

/-- The resolution of top-level call `c`, if it resolved (`some none`: cancelled). -/
def result? (m : Config E σ) (c : CallId) : Option (Option (List Val)) :=
  (m.results.find? (·.1 == c)).map Prod.snd

/-- Every top-level call issued so far has resolved. -/
def allResolved (m : Config E σ) : Bool := m.pending.all fun c => (m.result? c.1).isSome

/-- Record the `on_cancel` (`CancelRef`) of top-level call `c`, replacing any earlier one. -/
def setCancel (m : Config E σ) (c : CallId) (r : CancelRef) : Config E σ :=
  { m with cancels := (c, r) :: m.cancels.filter (·.1 != c) }

/-- Consume the `on_cancel` of top-level call `c`: the host cancels each call at most once
(REF `request_cancellation` asserts the task is still `INITIAL` or `STARTED`, which a second
`on_cancel` would violate; deviation D-f makes this a side condition). -/
def dropCancel (m : Config E σ) (c : CallId) : Config E σ :=
  { m with cancels := m.cancels.filter (·.1 != c) }

/-- The `on_cancel` (`CancelRef`) of top-level call `c`, if recorded. -/
def cancel? (m : Config E σ) (c : CallId) : Option CancelRef :=
  (m.cancels.find? (·.1 == c)).map Prod.snd

@[simp] theorem cancel?_setCancel_self (m : Config E σ) (c : CallId) (r : CancelRef) :
    (m.setCancel c r).cancel? c = some r := by
  simp [cancel?, setCancel]

@[simp] theorem init_cancel? (store : CStore E) (host : σ) (c : CallId) :
    (init store host).cancel? c = none := rfl

@[simp] theorem init_ctl (store : CStore E) (host : σ) : (init store host).ctl = [] := rfl
@[simp] theorem init_hostInControl (store : CStore E) (host : σ) :
    (init store host).hostInControl = true := rfl
@[simp] theorem init_cont? (store : CStore E) (host : σ) (t : ThreadId) :
    (init store host).cont? t = none := rfl

@[simp] theorem setCont_store (m : Config E σ) (t : ThreadId) (a : Option (Activation E σ)) :
    (m.setCont t a).store = m.store := rfl
@[simp] theorem setCont_ctl (m : Config E σ) (t : ThreadId) (a : Option (Activation E σ)) :
    (m.setCont t a).ctl = m.ctl := rfl

end Config

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Machine

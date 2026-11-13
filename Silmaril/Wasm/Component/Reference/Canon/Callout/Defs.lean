module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs

/-!
# The entry check of core callouts

In REF (`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF"), core code leaves its component instance only through the canon definitions of that
instance, and every such exit checks the current instance:
* `Store.lower`'s `core_func_inst` asserts `inst is current_instance()` (L548) and then calls
  `canon_lower`, which begins with `trap_if(not thread.task.inst.may_leave)` (L2170-2171);
* every built-in except `canon_resource_rep` (L2267), `canon_context_get` / `canon_context_set`
  (L2275, L2285) and `canon_backpressure_inc` / `canon_backpressure_dec` (L2295, L2302) begins
  with `trap_if(not inst.may_leave)` on `current_instance()`.

The machine runs a core callout `callout h args` (rule `Machine.Step.coreCallout`) as the
dispatched program `Canon.hostCalloutProg`, which first evaluates the entry check
`calloutEntry s th h` of this file on the current store `s` and thread `th` and traps with its
answer before any canon code runs (`withCalloutEntry`, which test dispatchers that override a
callout reuse):

| Lean | REF |
| --- | --- |
| `instOfThread? s th` | `current_instance()` of thread `th` (`current_thread().task.inst`) |
| `instMayLeave s i` | `inst.may_leave` (`true` for an unallocated id, the default of L203) |
| `threadMayLeave s th` | `current_instance().may_leave` (`true` on a host frame) |
| `ResolvedBuiltin.checksMayLeave b` | the built-in begins with `trap_if(not inst.may_leave)` |
| `CanonHost.inst? h` | the instance whose canon definition `h` is |
| `calloutEntry s th h` | the checks a callout makes before its canon code runs |
| `confine p` | an embedder import called while the current instance may not leave |

`calloutEntry s th h` is `some r` when the callout traps with `r`, in REF's order:
* `lowered callee ft opts inst`: called from a thread of `inst`, no trap here (`canon_lower`
  itself checks `inst.may_leave`, L2171). Called from a thread of another instance, or from a
  host frame (no current instance), it traps `internal`: `Store.lower`'s assert (L548) comes
  before `canon_lower`'s `may_leave` check, so REF never reads the flag in that case.
* `builtin b bi`: called from a thread of `bi`, no trap. Called from a thread of another
  instance `i`, no trap if `b` checks `may_leave` and `i.may_leave` is clear (the built-in then
  traps `cannotLeave` itself, first, as REF's `trap_if(not inst.may_leave)` on
  `current_instance()` does); otherwise `internal`. This check has no REF counterpart: REF
  built-ins carry no instance and act on `current_instance()`, and a canon built-in is only
  reachable from core code of the component instance that defined it (Explainer.md "Canonical
  Definitions"). Called from a host frame (no current instance), it traps `internal`.
* `embedder name ft`: no trap. An embedder import is a core-level import the host supplies
  (test harnesses only; REF has no such import, and `run_tests.py` writes the corresponding core
  functions in Python). While the current instance may not leave, its host program runs
  `confine`d: it may read the store, the host state and the current thread, write the host
  state, choose, emit free-form test notes (`HostObs.note`) and trap; its first other operation
  (a store update, a call, a core call, a thread operation, or an observation that the machine
  acts on: `started`, `resolved`, `received`) traps `cannotLeave`. This is a restriction of the
  test harness and is stricter than REF's Python core functions, which may update their own
  memory while `may_leave` is clear (run_tests `core_consumer_realloc` copies bytes with
  `Heap.realloc` while `assert(not consumer_inst.may_leave)` holds): such a function ported as
  an embedder import traps.

When the current instance of the calling thread is the defining instance of every lowered
function and built-in that core code calls (`calloutEntry_of_local`), the `internal` answers are
never taken. That every reachable callout of a validated component has this property is not
proved here, and it does not follow from the engine laws: a lawful engine whose core instances
export an address they did not import reaches, from the empty store and for valid components, a
callout to another instance's `canon lower` (`Theorems.Fidelity.Cex.calloutLocal_fails_validated`).
It is a property of the core engine (core instances export only their own functions and their
imports) together with instantiation.

Proved here: invariant preservation and the operation shape of `confine` (`confine_every`,
`Prog.Every.confine`), and the cases of `calloutEntry`. Machine-level consequences are in
`Theorems/MayLeave.lean` and `Theorems/Fidelity.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

variable {E : CoreEngine}

/-- The instance a canon host function was defined in (`none` for an embedder import). -/
def CanonHost.inst? : CanonHost E → Option InstId
  | .lowered _ _ _ i => some i
  | .builtin _ i => some i
  | .embedder _ _ => none

/-- The built-ins that begin with `trap_if(not inst.may_leave)`: all but `canon_resource_rep`
(L2267), `canon_context_get` / `canon_context_set` (L2275, L2285) and
`canon_backpressure_inc` / `canon_backpressure_dec` (L2295, L2302). -/
def ResolvedBuiltin.checksMayLeave : ResolvedBuiltin E → Bool
  | .resourceRep .. | .backpressureInc | .backpressureDec | .contextGet .. | .contextSet .. =>
    false
  | _ => true

end Silmaril.Wasm.Component.Runtime

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

/-- REF `current_instance()` of thread `th` in `s`: the instance of the task of `th` (`none` on
a host frame and for dangling ids). -/
def instOfThread? (s : CStore E) (th : Option ThreadId) : Option InstId := do
  let t ← th
  let thr ← ArenaField.threads.get? s t
  let tk ← ArenaField.tasks.get? s thr.task
  pure tk.inst

/-- REF `inst.may_leave` of instance `i` in `s` (`true` for an unallocated id, the default of a
fresh `ComponentInstance`, L203). -/
def instMayLeave (s : CStore E) (i : InstId) : Bool := ((s.inst? i).map (·.mayLeave)).getD true

/-- The flag of the current instance of thread `th` (`true` without one). -/
def threadMayLeave (s : CStore E) (th : Option ThreadId) : Bool :=
  match instOfThread? s th with
  | some i => instMayLeave s i
  | none => true

/-- The entry check of a core callout from thread `th` to the canon host function `h` in store
`s` (`none`: proceed; `some r`: trap with `r` before any canon code runs). See the module
docstring for the cases. -/
def calloutEntry (s : CStore E) (th : Option ThreadId) : CanonHost E → Option TrapReason
  | .lowered _ _ _ inst =>
    match instOfThread? s th with
    | some i =>
      if i = inst then none else some (.internal "Store.lower: inst is not current_instance()")
    | none => some (.internal "Store.lower: no current instance")
  | .builtin b bi =>
    match instOfThread? s th with
    | some i =>
      if i = bi ∨ (b.checksMayLeave = true ∧ instMayLeave s i = false) then none
      else some (.internal "canon built-in called from another instance")
    | none => some (.internal "canon built-in called without a current instance")
  | .embedder _ _ => none

/-- Read the current thread `th` and the store `s`, trap with the answer of the entry check
`calloutEntry s th h` of a callout to `h`, otherwise continue with `k s th`. This is the
prefix of `hostCalloutProg` (`Canon/Dispatch.lean`, `hostCalloutProg_eq`); dispatchers that
override the canon code of a callout (test overlays) use it to keep the check. -/
def withCalloutEntry {α : Type} (h : CanonHost E) (k : CStore E → Option ThreadId → P E σ α) :
    P E σ α := do
  let th ← currentThread
  let s ← getStore
  match calloutEntry s th h with
  | some r => trap r
  | none => k s th

/-- The operations confined code may issue: reads of the store, the current thread and the host
state, writes of the host state, choices, free-form test notes and traps. Store updates, calls,
core calls and thread operations would leave the instance, and the other observations are acted
on by the machine (`resolved` records the result of a top-level call, `Machine.Config.observe`;
REF code whose instance may not leave causes no `on_resolve`, L2171, L2313). -/
def Op.observes : Op E σ → Bool
  | .get | .currentThread | .hostGet | .hostSet _ | .choose _ | .trap _ => true
  | .emit o =>
    match o with
    | .note _ _ => true
    | .started _ | .resolved _ _ | .received _ _ => false
  | .modify _ | .call _ | .callCore _ _ | .newThread _ | .block _ | .resumeThread _ => false

/-- `p` confined to observation: `p` runs as long as it only `observes`, and its first other
operation traps `cannotLeave` (an embedder import called while the current instance may not
leave; see the module docstring). -/
def confine {α : Type} : P E σ α → P E σ α
  | .pure a => .pure a
  | .op o k => if Op.observes o then .op o fun r => confine (k r) else trap .cannotLeave

@[simp] theorem confine_pure {α : Type} (a : α) : confine (.pure a : P E σ α) = .pure a := rfl

/-! ## The cases of the entry check -/

@[simp] theorem calloutEntry_embedder (s : CStore E) (th : Option ThreadId) (n : String)
    (ft : V1.FuncType) : calloutEntry s th (.embedder n ft) = none := rfl

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon

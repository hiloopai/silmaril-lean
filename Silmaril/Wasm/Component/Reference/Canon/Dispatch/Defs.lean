module

public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Defs
public import Silmaril.Wasm.Component.Reference.Instantiate.Defs

/-!
# The dispatcher of late-bound calls

`Canon.dispatch lim q hr host : Call E → P E σ (Ret E)` resolves every late-bound call
`call (c : Call E)` of the specification programs (the REF functions of `definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF") to the program transcribing the corresponding Python closure or loop. It is the
`dispatch` argument of the machine (`Machine.step?`, `Machine.Step`). It is **non-recursive**:
a single `match` on the call whose arms are the (closed) programs of `Canon/Lift.lean`,
`Canon/Lower.lean` and
`Canon/Builtins`; those programs
issue further late-bound calls with `call`, which the machine resolves by calling `dispatch`
again, so only the machine's fuel loop recurses.

| `Call` | resolved to | REF |
| --- | --- | --- |
| `reallocate cx ..` | `reallocProg lim q cx ..` | `LiftLowerContext.reallocate` L625-641 |
| `funcInst f c`, `f` lifted | `canonLift lim q core ft opts inst c` | `Store.lift` L539 |
| `funcInst f c`, `f` a host function | `host.funcs fn c` | E1 (`mk_host_func`) |
| `hostFunc fn c` | `host.funcs fn c` | E1 |
| `onStart c` | by the caller record (below) | `on_start()` |
| `onResolve c r` | by the caller record (below) | `on_resolve(r)` |
| `onCancel r` | `Task.requestCancellation hr t` / `host.cancel n` / no-op | `OnCancel()` |
| `hostCallout (.lowered ..) args` | entry check `calloutEntry`, then `canonLower lim q ..` | `Store.lower` L545-552 |
| `hostCallout (.builtin b _) args` | entry check `calloutEntry`, then `builtinProg lim q hr b args` | `canon_<builtin>` |
| `hostCallout (.embedder n ft) args` | `host.embedder n ft args`, `confine`d while the current instance may not leave | an embedder import |
| `threadBody (.liftImplicit ..)` | `liftThreadBody` | `canon_lift`'s `thread_func` |
| `threadBody (.liftNoop task)` | `liftNoopThreadBody` | `thread_func` of the no-op destructor (L2257) |
| `threadBody (.newIndirect task f c)` | `callCore f [c]`, `Task.unregisterThread` | L2585-2587 |
| `threadBody (.host fn task)` | `host.threadBody fn task` | run_tests `mk_host_func` |
| `loop (.syncLiftLoop task)` | `syncLiftLoopBody hr task` | L2141-2144 |
| `loop (.callbackLoop ..)` | `callbackLoopBody` | L2108-2134 |
| `hostBuffer op` | `host.buffer op` | run_tests host buffers |
| `hostInvoke f args` | `hostInvokeProg f args` | `Store.invoke` L524-529 |
| `hostCancel r` | `hostCancelProg r` | `Store.invoke`'s `on_cancel` L530-534 |
| `instantiate c args` | `instantiateCallProg c args` | none (nested `instance (instantiate)`) |

Caller records (`Runtime.Caller`, the defunctionalized `(on_start, on_resolve)` pairs):
* `host call args depth` (a top-level host `Store.invoke`, `depth = 0`): `on_start` emits
  `HostObs.started call` (so traces show when a top-level call started) and returns `args`;
  `on_resolve r` emits `HostObs.resolved call r`, which the machine records in
  `Config.results` (`Config.observe`). A `host` record with `depth > 0` (not created by this
  development any more) returns `args` and ignores its resolution;
* `sub (.invoke args res)` (a nested `Store.invoke` of a host function, `hostInvokeProg`):
  `on_start` returns `args`; `on_resolve r` records `res := some r` in the record
  (`DispatchSt.recordInvokeResult`), which `hostInvokeProg` reads back (`invokeStatus`);
* `lower ..` (`canon_lower`): `lowerOnStart` / `lowerOnResolve` (`Canon/Lower.lean`);
* `sub ..` (realloc, destructor, start function): `onStartProg` / `onResolveProg`
  (`Canon/Lift.lean`).

The destructor call of `resource.drop` (`dtorCall` of `Builtins.resourceDrop`) is
`destructorCall lim q` of `Canon/Lift.lean`
(the synchronous lift of the destructor issues its own late-bound calls).

## Built-ins

`builtinProg lim q hr b args` is a total match over `ResolvedBuiltin E`: the flat core
arguments are decoded as unsigned numbers (`Canon.flatNat`) in the order of the REF
`canon_<builtin>` parameters (`thread.new-indirect`'s context argument `c` is passed as is;
`task.return` receives the whole flat argument list), and the flat results are returned as
`Ret.flat`. A wrong number of arguments is an `internal` trap: validation fixes the core type
of every built-in (`CanonHost.coreType`) and the core engine checks argument types at the
call, so it is unreachable for valid components.

## Design notes

* `dispatch` takes, besides `lim q`, the host readiness `hr : HostReady σ` (needed by
  `syncLiftLoopBody`, `Task.requestCancellation` and the `*-then-promote` built-ins) and a
  record `host : HostImpl E σ` instead of the bare `hostFns : HostFuncId → CallerId → P E σ
  (Ret E)`: `HostImpl.funcs` is that function, and the record also supplies host thread bodies,
  host cancellation hooks (`CancelRef.host n`), embedder imports (`CanonHost.embedder`) and host
  buffers (`Call.hostBuffer`), with defaults (`HostImpl.ofFns hostFns`).
* **Nested instantiation** (`Call.instantiate c args`, no REF counterpart) is dispatched to
  `Instantiate.instantiateClosure Instantiate.callRecurse c args`: the closure is instantiated
  in a fresh component instance, and its own nested instantiations issue `Call.instantiate`
  again, so nesting depth is bounded only by the machine's fuel. This needs the instance
  `[∀ a b, Decidable (E.ExternSub a b)]` (core instantiation checks import subtyping,
  `Instantiate.coreImportsFor?`), which `dispatch` takes as an instance argument; `lime1`,
  `v1` and `mock` have one (`Engine/Interface.lean`), an abstract Core 3.0 engine must supply
  it.
* **Nested invoke results.** The resolution of a nested `hostInvoke` is recorded in its
  caller record `Caller.sub (.invoke args res)` (`DispatchSt.recordInvokeResult`), which
  `hostInvokeProg` reads back (`invokeStatus`); REF calls `on_resolve` at most once and after
  `on_start`.
* D-f: REF asserts (`not lockdown` in `invoke`/`on_cancel`, `nesting_depth > 0` in
  `Store.lift`/`Store.lower`) are preconditions, not checked.
* **Core callouts** (`hostCalloutProg`) first read the current thread and the store and run
  the entry check `calloutEntry` (`Canon/Callout.lean`, `withCalloutEntry`): `Store.lower`'s
  `assert(inst is current_instance())` (L548) is checked (`internal`, before `canon_lower`'s
  `may_leave` check, L2171, as in REF), and a built-in called from another instance than the
  one that defined it, or without a current instance, traps `internal` unless it traps
  `cannotLeave` itself (a check without REF counterpart: REF built-ins carry no instance). The
  canon code then runs as `calloutBody`; an embedder import called while the current instance
  may not leave runs `confine`d (its first exit traps `cannotLeave`).

Proved here: `dispatch` unfolds on each constructor by `rfl` (examples below); a recorded
nested-invoke resolution is read back (`invokeStatus_recordInvokeResult`). No semantic
property of dispatched programs is claimed here (end-to-end tests are in `Embedding.lean`,
`Examples/` and `Tests/`). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## Host behaviour (E1) -/

/-- The host (embedder / test harness) behaviour the dispatcher consults (choice point E1):
* `funcs fn caller`: the `FuncInst` of host function `fn` called with caller record `caller`
  (returns `Ret.cancel`, its `on_cancel`);
* `threadBody fn task`: the body of a host thread (`ThreadBody.host`, run_tests
  `mk_host_func`); default: `internal` trap;
* `cancel n`: the host cancellation hook `CancelRef.host n`; default: no-op;
* `embedder name ft args`: a core call of an embedder import (`CanonHost.embedder`), run
  `confine`d while the calling thread's instance may not leave (`calloutBody`); default:
  `hostTrap`;
* `buffer op`: host buffer operations (`Call.hostBuffer`); default: `internal` trap. -/
structure HostImpl (E : CoreEngine) (σ : Type) where
  funcs : HostFuncId → CallerId → P E σ (Ret E)
  threadBody : HostFuncId → TaskId → P E σ (Ret E) :=
    fun _ _ => internal "dispatch: no host thread bodies"
  cancel : Nat → P E σ Unit := fun _ => pure ()
  embedder : String → V1.FuncType → List FlatValue → P E σ (List FlatValue) :=
    fun _ _ _ => trap (.hostTrap "dispatch: no embedder imports")
  buffer : HostBufOp → P E σ (Ret E) := fun _ => internal "dispatch: no host buffers"

/-- The host behaviour given only by host function values `hostFns`. -/
def HostImpl.ofFns (hostFns : HostFuncId → CallerId → P E σ (Ret E)) : HostImpl E σ :=
  { funcs := hostFns }

/-- No host functions at all (every host function call is an `internal` trap). -/
def HostImpl.none : HostImpl E σ :=
  HostImpl.ofFns fun _ _ => internal "dispatch: no host functions"

/-! ## Nested invokes (`Store.invoke` from a host function) -/

namespace DispatchSt

/-- REF `self.nesting_depth += 1` (`Store.invoke` / `on_cancel`). -/
def incNestingSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth + 1 }

/-- REF `self.nesting_depth -= 1`. -/
def decNestingSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth - 1 }

/-- Record the resolution `r` of a nested invoke in its caller record
`Caller.sub (.invoke args _)` (REF `on_resolve(r)` of the host's `Store.invoke`). Other records
are unchanged. -/
def recordInvokeResult (r : Option (List Val)) : Caller E → Caller E
  | .sub (.invoke args _) => .sub (.invoke args (some r))
  | c => c

end DispatchSt

/-- The resolution recorded in caller record `c` of a nested invoke (`none`: pending). -/
def invokeStatus : Caller E → Option (Option (List Val))
  | .sub (.invoke _ res) => res
  | _ => none

/-- REF `Store.invoke(f, on_start, on_resolve)` (L524-529) issued by a host function
(`Call.hostInvoke f args`, `Ret.invoked`): a fresh caller record `Caller.sub (.invoke args
none)` whose `on_start` returns `args`, `nesting_depth += 1`, `f(on_start, on_resolve)`
(`call (.funcInst f caller)`, returning the `on_cancel` handle), `nesting_depth -= 1`; the
result carries the handle and the resolution recorded so far (`none`: pending). -/
def hostInvokeProg (f : FuncId) (args : List Val) : P E σ (Ret E) := do
  let caller ← allocObj ArenaField.callers (Caller.sub (.invoke args none) : Caller E)
  modifyStore DispatchSt.incNestingSt
  let r ← callCancel (.funcInst f caller)
  modifyStore DispatchSt.decNestingSt
  let c ← getObj ArenaField.callers caller
  return .invoked r (invokeStatus c)

/-- REF `on_cancel()` returned by `Store.invoke` (L530-534) (`Call.hostCancel r`):
`nesting_depth += 1`, `request_cancellation()` (`call (.onCancel r)`), `nesting_depth -= 1`. -/
def hostCancelProg (r : CancelRef) : P E σ (Ret E) := do
  modifyStore DispatchSt.incNestingSt
  callUnit (.onCancel r)
  modifyStore DispatchSt.decNestingSt
  return .unit

/-! ## Caller records -/

/-- REF `on_start()` of caller record `c` (`Ret.vals`): a top-level host caller (depth `0`)
emits `HostObs.started call` (the harness's `on_start` closure ran and handed its arguments
over; delayed under backpressure, K1) and returns the stored arguments. -/
def callerOnStart (lim : Limits) (q : Quirks) (c : CallerId) : P E σ (Ret E) := do
  match ← getObj ArenaField.callers c with
  | .host call args depth =>
    if depth = 0 then emit (.started call)
    return .vals args
  | .lower .. => return .vals (← lowerOnStart lim q c)
  | .sub (.invoke args _) => return .vals args
  | .sub _ => onStartProg c

/-- REF `on_resolve(r)` of caller record `c` (`Ret.unit`): a top-level host caller emits the
resolution (recorded by the machine), a nested invoke's record stores it. -/
def callerOnResolve (lim : Limits) (q : Quirks) (c : CallerId) (r : Option (List Val)) :
    P E σ (Ret E) := do
  match ← getObj ArenaField.callers c with
  | .host call _ depth =>
    if depth = 0 then emit (.resolved call r)
    return .unit
  | .lower .. =>
    lowerOnResolve lim q c r
    return .unit
  | .sub (.invoke _ _) =>
    modifyObj ArenaField.callers c (DispatchSt.recordInvokeResult r)
    return .unit
  | .sub _ => onResolveProg c r

/-- REF `OnCancel()` (`Ret.unit`): a guest callee's `Task.request_cancellation` (L467-476,
resume site R2), a host hook, or nothing. -/
def onCancelProg (hr : HostReady σ) (host : HostImpl E σ) : CancelRef → P E σ (Ret E)
  | .task t => do Task.requestCancellation hr t; return .unit
  | .host n => do host.cancel n; return .unit
  | .none => pure .unit

/-- REF `FuncInst(on_start, on_resolve)` of function value `f` (`Ret.cancel`): a lifted
function runs `canon_lift` (`Store.lift`, L539-543), a host function its host program. -/
def funcInstProg (lim : Limits) (q : Quirks) (host : HostImpl E σ) (f : FuncId)
    (caller : CallerId) : P E σ (Ret E) := do
  match ← getObj ArenaField.funcs f with
  | .lifted core ft opts inst => canonLift lim q core ft opts inst caller
  | .host _ fn => host.funcs fn caller

/-! ## Built-ins -/

section Args

variable {α : Type}

/-- No flat argument. -/
def withArgs0 (args : List FlatValue) (k : P E σ α) : P E σ α :=
  match args with
  | [] => k
  | _ => internal "built-in: wrong number of arguments"

/-- One flat argument, as an unsigned number. -/
def withArgs1 (args : List FlatValue) (k : Nat → P E σ α) : P E σ α :=
  match args with
  | [a] => k (flatNat a)
  | _ => internal "built-in: wrong number of arguments"

/-- Two flat arguments, as unsigned numbers. -/
def withArgs2 (args : List FlatValue) (k : Nat → Nat → P E σ α) : P E σ α :=
  match args with
  | [a, b] => k (flatNat a) (flatNat b)
  | _ => internal "built-in: wrong number of arguments"

/-- Three flat arguments, as unsigned numbers. -/
def withArgs3 (args : List FlatValue) (k : Nat → Nat → Nat → P E σ α) : P E σ α :=
  match args with
  | [a, b, c] => k (flatNat a) (flatNat b) (flatNat c)
  | _ => internal "built-in: wrong number of arguments"

end Args

open Builtins in
/-- The canon built-in `b` called by core code with the flat arguments `args` (REF
`canon_<builtin>`, `Canon/Builtins`), returning the flat results. A total match over
`ResolvedBuiltin`; the arguments are decoded in REF parameter order (see the module
docstring). -/
def builtinProg (lim : Limits) (q : Quirks) (hr : HostReady σ) (b : ResolvedBuiltin E)
    (args : List FlatValue) : P E σ (List FlatValue) :=
  match b with
  | .resourceNew rt _ => withArgs1 args fun rep => resourceNew lim rt rep
  | .resourceDrop rt => withArgs1 args fun i => resourceDrop lim q (destructorCall lim q) rt i
  | .resourceRep rt _ => withArgs1 args fun i => resourceRep lim rt i
  | .backpressureInc => withArgs0 args backpressureInc
  | .backpressureDec => withArgs0 args backpressureDec
  | .taskReturn result opts => taskReturn lim q result opts args
  | .taskCancel => withArgs0 args taskCancel
  | .contextGet t i => withArgs0 args (contextGet t i)
  | .contextSet t i => withArgs1 args fun v => contextSet t i v
  | .subtaskCancel async_ => withArgs1 args fun i => subtaskCancel lim async_ i
  | .subtaskDrop => withArgs1 args fun i => Builtins.subtaskDrop lim i
  | .streamNew t => withArgs0 args (streamNew lim t)
  | .streamRead t opts => withArgs3 args fun i p n => streamRead lim q t opts i p n
  | .streamWrite t opts => withArgs3 args fun i p n => streamWrite lim q t opts i p n
  | .streamCancelRead t async_ => withArgs1 args fun i => streamCancelRead lim t async_ i
  | .streamCancelWrite t async_ => withArgs1 args fun i => streamCancelWrite lim t async_ i
  | .streamDropReadable t => withArgs1 args fun i => streamDropReadable lim t i
  | .streamDropWritable t => withArgs1 args fun i => streamDropWritable lim t i
  | .streamForward t => withArgs2 args fun ri wi => streamForward lim q t ri wi
  | .futureNew t => withArgs0 args (futureNew lim t)
  | .futureRead t opts => withArgs2 args fun i p => futureRead lim q t opts i p
  | .futureWrite t opts => withArgs2 args fun i p => futureWrite lim q t opts i p
  | .futureCancelRead t async_ => withArgs1 args fun i => futureCancelRead lim t async_ i
  | .futureCancelWrite t async_ => withArgs1 args fun i => futureCancelWrite lim t async_ i
  | .futureDropReadable t => withArgs1 args fun i => futureDropReadable lim t i
  | .futureDropWritable t => withArgs1 args fun i => futureDropWritable lim t i
  | .futureForward t => withArgs2 args fun ri wi => futureForward lim q t ri wi
  | .errorContextNew opts => withArgs2 args fun p n => errorContextNew lim q opts p n
  | .errorContextDebugMessage opts =>
    withArgs2 args fun i p => errorContextDebugMessage lim q opts i p
  | .errorContextDrop => withArgs1 args fun i => errorContextDrop i
  | .waitableSetNew => withArgs0 args (waitableSetNew lim)
  | .waitableSetWait mem => withArgs2 args fun si p => waitableSetWait lim mem si p
  | .waitableSetPoll mem => withArgs2 args fun si p => waitableSetPoll lim mem si p
  | .waitableSetDrop => withArgs1 args fun i => waitableSetDrop lim i
  | .waitableJoin => withArgs2 args fun wi si => waitableJoin lim wi si
  | .threadIndex => withArgs0 args threadIndex
  | .threadNewIndirect tbl ft =>
    match args with
    | [fi, c] => threadNewIndirect tbl ft (flatNat fi) c
    | _ => internal "built-in: wrong number of arguments"
  | .threadResumeLater => withArgs1 args fun i => threadResumeLater i
  | .threadSuspend => withArgs0 args threadSuspend
  | .threadYield => withArgs0 args threadYield
  | .threadSuspendThenResume => withArgs1 args fun i => threadSuspendThenResume i
  | .threadYieldThenResume => withArgs1 args fun i => threadYieldThenResume i
  | .threadSuspendThenPromote => withArgs1 args fun i => threadSuspendThenPromote hr q i
  | .threadYieldThenPromote => withArgs1 args fun i => threadYieldThenPromote hr q i

/-! ## Thread bodies and loops -/

/-- REF `thread_func()` of a new thread (`Ret.unit`): `canon_lift`'s implicit thread
(L2077-2135, of a core callee or of the no-op destructor `lambda rep: []`, L2257),
`thread.new-indirect`'s `call_and_trap_on_throw(f.callee, [c])` followed by
`task.unregister_thread(new_thread)` (L2585-2587; the new thread is the current thread), or a
host thread. -/
def threadBodyProg (lim : Limits) (q : Quirks) (host : HostImpl E σ) :
    ThreadBody E → P E σ (Ret E)
  | .liftImplicit task callee => liftThreadBody lim q task callee
  | .newIndirect task f c => do
    let _ ← callCore f [c]
    let t ← currentThreadId
    Task.unregisterThread task t
    return .unit
  | .host fn task => host.threadBody fn task
  | .liftNoop task => liftNoopThreadBody lim q task

/-- One iteration of a REF `while` loop from its head (`Ret.unit`). -/
def loopProg (lim : Limits) (hr : HostReady σ) : LoopPoint E → P E σ (Ret E)
  | .syncLiftLoop task => syncLiftLoopBody hr task
  | .callbackLoop task thread code si => callbackLoopBody lim task thread code si

/-- The canon code of a core callout from thread `th` (store `s`) to `h` once its entry check
`calloutEntry s th h` passed (`Ret.flat`: what core code sees): `canon_lower` (`Store.lower`,
L545-552), a canon built-in, or an embedder import, `confine`d while the current instance may
not leave. -/
def calloutBody (lim : Limits) (q : Quirks) (hr : HostReady σ) (host : HostImpl E σ)
    (s : CStore E) (th : Option ThreadId) (h : CanonHost E) (args : List FlatValue) :
    P E σ (Ret E) :=
  match h with
  | .lowered callee ft opts inst => do return .flat (← canonLower lim q callee ft opts inst args)
  | .builtin b _ => do return .flat (← builtinProg lim q hr b args)
  | .embedder name ft => do
    return .flat (← if threadMayLeave s th then host.embedder name ft args
      else confine (host.embedder name ft args))

/-- A core call of a canon host function (`Ret.flat`: what core code sees), the program the
machine runs for a core activation parked on `callout h args`: read the current thread and the
store, trap with the answer of the entry check `calloutEntry` (REF `Store.lower`'s
`assert(inst is current_instance())`, L548, and the `may_leave` check of `canon_lower` on the
current instance, L2171; see `Canon/Callout.lean`), otherwise run `calloutBody`. -/
def hostCalloutProg (lim : Limits) (q : Quirks) (hr : HostReady σ) (host : HostImpl E σ)
    (h : CanonHost E) (args : List FlatValue) : P E σ (Ret E) := do
  let th ← currentThread
  let s ← getStore
  match calloutEntry s th h with
  | some r => trap r
  | none => calloutBody lim q hr host s th h args

/-! ## Nested instantiation -/

/-- Nested instantiation (`Call.instantiate c args`, `Ret.items`): instantiate the closure `c`
with the argument map `args` in a fresh component instance, tying its own nested
instantiations with `Call.instantiate` again (`Instantiate.callRecurse`). -/
def instantiateCallProg [∀ a b, Decidable (E.ExternSub a b)] (c : Instantiate.Closure E)
    (args : Instantiate.Exports E) : P E σ (Ret E) := do
  return .items (← Instantiate.instantiateClosure Instantiate.callRecurse c args)

/-! ## The dispatcher -/

/-- The non-recursive dispatcher of late-bound calls (see the table in the module docstring).
`lim`, `q`: limits and quirks (`Quirks.none` is the specification); `hr`: the machine's host
readiness; `host`: the host behaviour (E1). The instance argument decides core extern subtyping
(core instantiation inside nested instantiation). -/
def dispatch [∀ a b, Decidable (E.ExternSub a b)] (lim : Limits) (q : Quirks)
    (hr : HostReady σ) (host : HostImpl E σ) : Call E → P E σ (Ret E)
  | .reallocate cx old oldLen align newLen => reallocProg lim q cx old oldLen align newLen
  | .funcInst f caller => funcInstProg lim q host f caller
  | .onStart c => callerOnStart lim q c
  | .onResolve c r => callerOnResolve lim q c r
  | .onCancel r => onCancelProg hr host r
  | .hostCallout h args => hostCalloutProg lim q hr host h args
  | .threadBody b => threadBodyProg lim q host b
  | .loop l => loopProg lim hr l
  | .hostFunc fn caller => host.funcs fn caller
  | .hostBuffer op => host.buffer op
  | .hostInvoke f args => hostInvokeProg f args
  | .hostCancel r => hostCancelProg r
  | .instantiate c args => instantiateCallProg c args

/-- The specification dispatcher: `Limits.spec`, `Quirks.none`. -/
abbrev specDispatch [∀ a b, Decidable (E.ExternSub a b)] (hr : HostReady σ)
    (host : HostImpl E σ) : Call E → P E σ (Ret E) :=
  dispatch Limits.spec Quirks.none hr host

/-! ## Unfolding checks (the dispatcher is a plain case split) -/

section Checks

variable [∀ a b, Decidable (E.ExternSub a b)] (lim : Limits) (q : Quirks) (hr : HostReady σ)
  (host : HostImpl E σ)

-- FLAG(statement-change): the callout program begins with the entry check of REF
-- `Store.lower`'s `assert(inst is current_instance())` (L548) and of the built-in's defining
-- instance (`calloutEntry`).
end Checks

end Silmaril.Wasm.Component.Canon

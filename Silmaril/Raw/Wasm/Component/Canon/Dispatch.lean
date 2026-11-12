module

public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Lift
public import Silmaril.Raw.Wasm.Component.Canon.Lower
public import Silmaril.Raw.Wasm.Component.Canon.Builtins
public import Silmaril.Raw.Wasm.Component.Canon.Callout
public import Silmaril.Raw.Wasm.Component.Instantiate.Defs

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

/-! ## Nested invokes (`Store.invoke` from a host function) -/

namespace DispatchSt

end DispatchSt

theorem invokeStatus_recordInvokeResult (args : List Val) (res : Option (Option (List Val)))
    (r : Option (List Val)) :
    invokeStatus (DispatchSt.recordInvokeResult (E := E) r (.sub (.invoke args res))) =
      some r := rfl

/-! ## Caller records -/

/-! ## Built-ins -/

section Args

variable {α : Type}

end Args

/-! ## Thread bodies and loops -/

/-! ## Nested instantiation -/

/-- The store updates of the nested-instantiation arm only append to arenas
(`Instantiate.ArenasExtend`); its own nested instantiations are again late-bound calls. -/
theorem instantiateCallProg_inv [∀ a b, Decidable (E.ExternSub a b)] {s₀ : CStore E}
    (c : Instantiate.Closure E) (args : Instantiate.Exports E) :
    P.Inv (Instantiate.ArenasExtend s₀) (instantiateCallProg c args : P E σ (Ret E)) :=
  P.Inv.bind (Instantiate.instantiateClosure_inv (fun c a => Instantiate.callRecurse_inv c a)
    c args) fun _ => P.Inv.pure _

/-! ## The dispatcher -/

/-! ## Unfolding checks (the dispatcher is a plain case split) -/

section Checks

variable [∀ a b, Decidable (E.ExternSub a b)] (lim : Limits) (q : Quirks) (hr : HostReady σ)
  (host : HostImpl E σ)

example (l : LoopPoint E) : dispatch lim q hr host (.loop l) = loopProg lim hr l := rfl

example (task : TaskId) : dispatch lim q hr host (.loop (.syncLiftLoop task)) =
    syncLiftLoopBody hr task := rfl

example (task : TaskId) (callee : E.FuncAddr) :
    dispatch lim q hr host (.threadBody (.liftImplicit task callee)) =
      liftThreadBody lim q task callee := rfl

example (fn : HostFuncId) (c : CallerId) :
    dispatch lim q hr host (.hostFunc fn c) = host.funcs fn c := rfl

-- FLAG(statement-change): the callout program begins with the entry check of REF
-- `Store.lower`'s `assert(inst is current_instance())` (L548) and of the built-in's defining
-- instance (`calloutEntry`).
example (b : ResolvedBuiltin E) (inst : InstId) (args : List FlatValue) :
    dispatch lim q hr host (.hostCallout (.builtin b inst) args) =
      (do
        let th ← currentThread
        let s ← getStore
        match calloutEntry s th (.builtin b inst) with
        | some r => trap r
        | none => return .flat (← builtinProg lim q hr b args)) := rfl

example (s : CStore E) (th : Option ThreadId) (n : String) (ft : V1.FuncType)
    (args : List FlatValue) (h : threadMayLeave s th = false) :
    calloutBody lim q hr host s th (.embedder n ft) args =
      (do return .flat (← confine (host.embedder n ft args))) := by
  simp only [calloutBody, h, Bool.false_eq_true, ↓reduceIte]

example : builtinProg (E := E) (σ := σ) lim q hr .threadYield [] = Builtins.threadYield := rfl

example (a : FlatValue) : builtinProg (E := E) (σ := σ) lim q hr .threadYield [a] =
    internal "built-in: wrong number of arguments" := rfl

example (rt : RtId) (a : FlatValue) : builtinProg (E := E) (σ := σ) lim q hr (.resourceDrop rt)
    [a] = Builtins.resourceDrop lim q (destructorCall lim q) rt (flatNat a) := rfl

example (r : CancelRef) : dispatch lim q hr host (.hostCancel r) = hostCancelProg r := rfl

example (c : Instantiate.Closure E) (args : Instantiate.Exports E) :
    dispatch lim q hr host (.instantiate c args) =
      (do return .items (← Instantiate.instantiateClosure Instantiate.callRecurse c args)) :=
  rfl

example : DispatchSt.recordInvokeResult (E := E) (some [.bool true]) (.sub (.invoke [] none)) =
    .sub (.invoke [] (some (some [.bool true]))) := rfl

example (args : List Val) (r : Option (List Val)) :
    invokeStatus (DispatchSt.recordInvokeResult (E := E) r (.sub (.invoke args none))) =
      some r := rfl

end Checks

end Silmaril.Wasm.Component.Canon

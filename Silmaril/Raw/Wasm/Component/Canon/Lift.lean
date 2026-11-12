module

public import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Flat
public import Silmaril.Raw.Wasm.Component.Runtime.Task
public import Silmaril.Raw.Wasm.Component.Runtime.Waitable

/-!
# `canon lift`, `LiftLowerContext.reallocate`, start functions and destructor calls

Transcribes REF `canon_lift` and its `thread_func` (`design/mvp/canonical-abi/definitions.py`
at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L2076-2145; `CanonicalABI.md` §"`canon lift`"), REF `LiftLowerContext.reallocate` (L625-641) with
the `Store.invoke`/`Store.lift` wrappers it goes through (L524-543), and the nested synchronous
calls of core start functions and resource destructors, as programs in `P E σ` that the dispatcher
calls:

| Lean | REF (lines) | dispatched from |
| --- | --- | --- |
| `canonLift` | `canon_lift` (L2076, L2137-2145) | `funcInst` (lifted) |
| `syncLiftLoopBody hr task` | sync loop (L2141-2144), C3 | `loop (.syncLiftLoop _)` |
| `liftThreadBody` | `thread_func` (L2077-2135) | `threadBody (.liftImplicit _ _)` |
| `callbackLoopBody` | callback loop iteration (L2108-2134) | `loop (.callbackLoop ..)` |
| `reallocProg` | `LiftLowerContext.reallocate` (L625-641) | `reallocate ..` |
| `startFunctionTask` | start function as a sync `func()` task | direct |
| `destructorCall` | dtor call of `canon_resource_drop` (L2253-2260) | `dtorCall` |
| `canonLiftNoop`, `liftNoopThreadBody` | `canon_lift` of the no-op destructor `lambda rep: []` (L2257) | `destructorCall`, `threadBody (.liftNoop _)` |
| `onStartProg`, `onResolveProg` | `on_start`/`on_resolve` of `Caller.sub` | `onStart`/`onResolve` |

**Loops.** Both REF `while` loops of `canon_lift` are late-bound `LoopPoint` calls: the body
programs run ONE iteration and end with the tail call `callRet (.loop l')` (or return
`Ret.unit` when the loop condition fails), so no program here recurses.

* `LoopPoint.syncLiftLoop task` (L2141-2144): if the task is `RESOLVED` the loop exits;
  otherwise the candidates are `CStore.instCandidates` of the task's instance (REF
  `{ t for t in inst.threads if t.ready() }`), `trap_if(not candidates)` (`cannotBlockSync`),
  the C3 choice `pickSyncLoop` picks one, which is `Thread.resume`d (resume site R1), and the
  loop re-enters.
* `LoopPoint.callbackLoop task thread code si` (L2108-2134): with `code = EXIT` the loop exits
  into `task.exit_implicit_thread()` (L2134). Otherwise one iteration: deliver a pending cancel
  (event `TASK_CANCELLED`, lock still held), or release the exclusive lock and set
  `thread.cancellable` (ONE store update `LiftSt.releaseCallbackSt`), then `YIELD` (wait site K2,
  choice C1, `ReadyCond.exclusiveFree`; then `TASK_CANCELLED` or `NONE`) or `WAIT`
  (`inst.handles.get(si)`, resolved anew each turn; trap `wrongHandleType` unless a waitable
  set; `WaitableSet.wait_from_callback`, wait site K3), then retake the lock and clear
  `cancellable` (ONE store update `LiftSt.retakeCallbackSt`); then call the `callback` core
  function with `[event_code, p1, p2]` (`AsyncRef.EventTuple.callbackArgs`), unpack its single
  result (`AsyncRef.unpackCallbackResult`, trap `unsupportedCallbackCode`) and re-enter the loop.

**`reallocate`: the direct lift path.** REF `reallocate` does
`store.invoke(store.lift(opts.realloc, ft, CanonicalOptions(), inst), on_start, on_resolve)`.
Since `opts.realloc` is a core `FuncAddr` and not a component function value (`FuncId`),
`reallocProg` does NOT allocate a transient `CFuncInst`: `Store.lift`'s `func_inst`
(L539-543) is just `canon_lift(f, ft, opts, inst, on_start, on_resolve)` (its asserts on
`nesting_depth` are preconditions), so `reallocProg` calls `canonLift` directly (the
"direct `liftCore` path"), bracketed by the `Store.invoke` updates `nesting_depth += 1` /
`-= 1` (L526-528, `LiftSt.incNestingSt`/`decNestingSt`) and by `may_leave = False` / `True`
(L637-639). The `(on_start, on_resolve)` pair is a fresh `Caller.sub (.realloc args none)`
record whose `on_resolve` records the lifted pointer (`LiftSt.recordReallocResult`), read back
after the call (`assert(ptr is not None)` is an `internal` trap). `startFunctionTask` and
`destructorCall` use the same direct path (no `CFuncInst`; `runStart` registers one and
goes through `Call.funcInst`, which the dispatcher resolves to the same `canonLift` call).

## Deviations and non-claims

* D-f: REF asserts are preconditions, not checked: `types_match_values` of the flat arguments
  and results, `[] = callee(...)` of stackful/`post_return` calls (extra results are ignored),
  the exclusive-lock asserts of the callback loop, and the `nesting_depth > 0` asserts of
  `Store.lift`. Where a shape is needed to continue (the single `packed` result of a
  callback-lifted call, the callback option, the realloc option, the single realloc result)
  its absence is an `internal` trap.
* The `may_leave` asserts that open the two windows, `assert(self.inst.may_leave)` of
  `reallocate` (L636) and `assert(cx.inst.may_leave)` before `post_return` (L2093), are
  checked, in the form of `canon_lower`'s entry check (L2171): `trapIf (!(← getInst
  i).mayLeave) .cannotLeave` right before the opening write `inst.may_leave = False` (a
  dangling instance id traps `internal`, as every `getObj`). REF guarantees these asserts:
  while the flag of an instance is clear its core code cannot leave it (every exit traps
  `cannotLeave`), so no second window of the instance starts. Host programs (`HostImpl`, the
  programs of `HostEvent.run`) are arbitrary here and can reach a window without such an exit
  (a host-run program may call `reallocate` of any context directly), and the check then takes
  REF's `cannotLeave` trap at the window. So every opening write finds its instance allocated
  with the flag set (`Theorems.opensWhenSet`), and windows of one instance never nest. Not
  claimed: that the check never fires for hosts that issue no such call.
* `LoopPoint.callbackLoop` stores the callback code as a `Nat` (`AsyncRef.CallbackCode.toNat`);
  the body decodes it with `CallbackCode.ofNat?` and traps `unsupportedCallbackCode` on any
  other value (REF `case _: trap()`, unreachable after `unpack_callback_result`).
* REF `canon_lift` returns the bound method `task.request_cancellation`; here `Ret.cancel
  (.task task)` (the dispatcher runs `Task.requestCancellation` for it).
* `destructorCall` performs `store.lower(store.lift(dtor, ft, opts, rt.impl), ft, opts, inst)`
  applied to `[h.rep]` as REF does, except that the caller side `canon_lower` wrapper is
  reduced to its only observable part: its `trap_if(not inst.may_leave)` entry check
  (`cannotLeave`). The wrapper's `Subtask` is never added to a handle table (sync lower), and
  the callee function type is synchronous, so after `canon_lift` returns the subtask is
  `RETURNED` with no lenders (the argument is an integer) and `deliver_resolve` has no effect.
  When `rt.dtor` is `None`, REF lifts the no-op `lambda rep: []` (L2257) in `rt.impl`; so does
  `destructorCall`, by `canonLiftNoop`: a task and a thread of `rt.impl` are created, and the
  thread is registered in `rt.impl`'s thread table (`register_thread`, which traps
  `tableFull` on a full table, `Table.add` L677) and unregistered again before the call
  returns. The no-op callee runs no core code: the thread body `liftNoopThreadBody` is REF
  `thread_func` with `flat_results = []`. When `rt.impl` is `None` (a host resource, which
  REF does not have) no call is made. The argument type is `u32`, or `u64` for a resource
  whose representation is `i64` (🐘; REF always uses `U32Type()`); `onStartProg` reads the
  width from the callee task.
* `startFunctionTask` is the direct-path equivalent of `runStart` (type `func()`,
  default options, caller `Caller.sub .start`); it is provided for the dispatcher and tests.
* Proved here: `P.Inv` lemmas for every program (under `LiftHyps I`); no semantic property of
  the programs is claimed (machine-level properties are in `Machine/`, end-to-end runs in
  `Examples/` and `Tests/`). Tests: none. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

namespace LiftSt

end LiftSt

/-! ## Function types of the internal calls -/

/-! ## `canon lift` -/

-- FLAG(statement-change): the `post_return` branch checks REF's `assert(cx.inst.may_leave)`
-- (L2093) before the opening write; without the check `Theorems.opensWhenSet` is false.
/-! ## `on_start`/`on_resolve` of the internal callers -/

/-! ## `reallocate`, start functions and destructors -/

-- FLAG(statement-change): checks REF's `assert(self.inst.may_leave)` (L636) before the opening
-- write; without the check `Theorems.opensWhenSet` is false.
/-! ## Unfolding checks -/

example (hr : HostReady σ) (task : TaskId) :
    (syncLiftLoopBody hr task : P E σ (Ret E)) = (do
      let tk ← getTask task
      if tk.state = .resolved then return .unit
      let s ← getStore
      let h ← hostGet
      match s.instCandidates (hr h) tk.inst with
      | [] => trap .cannotBlockSync
      | c :: cs =>
        let t ← pickSyncLoop c cs
        Thread.resume t
        callRet (.loop (.syncLiftLoop task))) := rfl

example (lim : Limits) (task : TaskId) (thread : ThreadId) (si : Nat) :
    (callbackLoopBody lim task thread 0 si : P E σ (Ret E)) =
      (do Task.exitImplicitThread task; return .unit) := rfl

example : reallocType .i32 =
    (⟨[("old", .prim .u32), ("old_byte_length", .prim .u32), ("alignment", .prim .u32),
      ("new_byte_length", .prim .u32)], some (.prim .u32), false⟩ :
        WIT.FuncType Empty RtId) := rfl

example (rep : Nat) : repVal (paramTypes (dtorType .i64)) rep = .int .u64 rep := rfl
example (rep : Nat) : repVal (paramTypes (dtorType .i32)) rep = .int .u32 rep := rfl

example (args : List Val) (v : Val) :
    LiftSt.recordReallocResult (E := E) v (.sub (.realloc args none)) =
      .sub (.realloc args (some v)) := rfl

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem startFunctionTask (H : LiftHyps I) (lim : Limits) (q : Quirks) (inst : InstId)
    (sf : E.FuncAddr) : P.Inv I (Canon.startFunctionTask lim q inst sf : P E σ Unit) := by
  unfold Canon.startFunctionTask
  exact bind (allocObj _ _ (H.allocCaller _)) fun _ =>
    bind (canonLift H _ _ _ _ _ _ _) fun _ => pure _

end P.Inv

end Silmaril.Wasm.Component.Canon

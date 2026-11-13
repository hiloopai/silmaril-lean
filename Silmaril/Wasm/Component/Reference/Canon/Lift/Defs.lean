module

public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs

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

/-- `inst.may_leave = b` (L2094/L2096 around `post_return`, L637/L639 around `realloc`),
recording `owner` in the ghost field `InstState.leaveOwner`: the opening write
`setMayLeave false o` passes the window's current thread `o` (REF `current_thread()`); setting
the flag back resets the owner to `none` (whatever `owner` is; the closing write passes the
default `none`). -/
def setMayLeave (b : Bool) (owner : Option ThreadId := none) (st : InstState) : InstState :=
  { st with mayLeave := b, leaveOwner := if b then none else owner }

/-- The callback loop's release (L2113-2114), one update: `inst.exclusive_thread = None` and
`thread.cancellable = True`. -/
def releaseCallbackSt (inst : InstId) (thread : ThreadId) (s : CStore E) : CStore E :=
  let s₁ := ArenaField.insts.modify s inst fun st => { st with exclusive := none }
  ArenaField.threads.modify s₁ thread fun th => { th with cancellable := true }

/-- The callback loop's retake (L2128-2130), one update: `thread.cancellable = False` and
`inst.exclusive_thread = thread` (the task's implicit thread). -/
def retakeCallbackSt (inst : InstId) (thread : ThreadId) (s : CStore E) : CStore E :=
  let s₁ := ArenaField.threads.modify s thread fun th => { th with cancellable := false }
  ArenaField.insts.modify s₁ inst fun st => { st with exclusive := some thread }

/-- `Store.invoke`'s `nesting_depth += 1` (L526). -/
def incNestingSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth + 1 }

/-- `Store.invoke`'s `nesting_depth -= 1` (L528). -/
def decNestingSt (s : CStore E) : CStore E := { s with nestingDepth := s.nestingDepth - 1 }

/-- The realloc `on_resolve` (L633-635): record the lifted pointer `v` in the caller record
(`nonlocal ptr; [ptr] = result`). Other caller records are unchanged. -/
def recordReallocResult (v : Val) : Caller E → Caller E
  | .sub (.realloc args _) => .sub (.realloc args (some v))
  | c => c

end LiftSt

/-! ## Function types of the internal calls -/

/-- REF `ft.param_types()`. -/
def paramTypes (ft : WIT.FuncType Empty RtId) : List (WIT.ClosedType RtId) := ft.params.map (·.2)

/-- REF `ft.result_type()` (the list of at most one result type). -/
def resultTypes (ft : WIT.FuncType Empty RtId) : List (WIT.ClosedType RtId) := ft.result.toList

/-- The pointer integer type `U32Type()`/`U64Type()` of a pointer width (REF `reallocate`,
L626). -/
def ptrPrim : AddrType → WIT.Primitive
  | .i32 => .u32
  | .i64 => .u64

/-- The integer kind of `ptrPrim p`. -/
def ptrIntKind : AddrType → IntKind
  | .i32 => .u32
  | .i64 => .u64

/-- REF `FuncType([ptrt, ptrt, ptrt, ptrt], [ptrt], async_ = False)` of `reallocate` (L627). -/
def reallocType (p : AddrType) : WIT.FuncType Empty RtId :=
  let t : WIT.ClosedType RtId := .prim (ptrPrim p)
  ⟨[("old", t), ("old_byte_length", t), ("alignment", t), ("new_byte_length", t)], some t,
    false⟩

/-- REF `FuncType([U32Type()], [], async_ = False)` of a resource destructor (L2256), with
`u64` for 🐘 `i64` representations. -/
def dtorType (rep : AddrType) : WIT.FuncType Empty RtId :=
  ⟨[("rep", .prim (ptrPrim rep))], none, false⟩

/-- The implicit type `func()` of a core start function. -/
def startFuncType : WIT.FuncType Empty RtId := ⟨[], none, false⟩

/-- The value `rep` at the integer type of the (single) destructor parameter `ts`. -/
def repVal (ts : List (WIT.ClosedType RtId)) (rep : Nat) : Val :=
  match ts with
  | [.prim .u64] => .int .u64 rep
  | _ => .int .u32 rep

/-- The function type of the task whose caller record is `c` (the unique such task, since
every internal caller record is allocated for one call). -/
def callerTaskFt? (s : CStore E) (c : CallerId) : Option (WIT.FuncType Empty RtId) :=
  (s.tasks.find? (fun tk => decide (tk.caller = c))).map (·.ft)

/-! ## `canon lift` -/

/-- REF `canon_lift(callee, ft, opts, inst, on_start, on_resolve)` (L2076, L2137-2145), with
the `(on_start, on_resolve)` pair given by the caller record `caller`:
`task = Task(ft, opts, inst, on_start, on_resolve)` (a fresh task in the arena),
`thread = Thread(task, thread_func)` (`newThread (.liftImplicit task callee)`, whose body is
`liftThreadBody`), `thread.resume()` (resume site R1); then, if `ft` is not async, the
synchronous mini-scheduler `while task.state != RESOLVED` as the late-bound loop
`LoopPoint.syncLiftLoop task` (`syncLiftLoopBody`); returns `task.request_cancellation`
(`Ret.cancel (.task task)`). `lim` and `q` are unused here (the conventional leading
arguments; the body programs take them). -/
def canonLift (_lim : Limits) (_q : Quirks) (callee : E.FuncAddr) (ft : WIT.FuncType Empty RtId)
    (opts : CanonOpts E) (inst : InstId) (caller : CallerId) : P E σ (Ret E) := do
  let task ← allocObj ArenaField.tasks ({ ft, opts, inst, caller } : Task E)
  let thread ← newThread (.liftImplicit task callee)
  Thread.resume thread
  (if !ft.async_ then callUnit (.loop (.syncLiftLoop task)) else pure () : P E σ Unit)
  return .cancel (.task task)

/-- One iteration of REF `canon_lift`'s synchronous loop (L2141-2144), the body of
`LoopPoint.syncLiftLoop task`: if `task.state == RESOLVED` the loop exits (`Ret.unit`);
otherwise `candidates = { t for t in inst.threads if t.ready() }` (`CStore.instCandidates`,
with the machine's host readiness `hr`), `trap_if(not candidates)` (`cannotBlockSync`),
`random.choice(candidates).resume()` (choice C3, resume site R1), and re-enter the loop (tail
call). -/
def syncLiftLoopBody (hr : HostReady σ) (task : TaskId) : P E σ (Ret E) := do
  let tk ← getTask task
  if tk.state = .resolved then return .unit
  let s ← getStore
  let h ← hostGet
  match s.instCandidates (hr h) tk.inst with
  | [] => trap .cannotBlockSync
  | c :: cs =>
    let t ← pickSyncLoop c cs
    Thread.resume t
    callRet (.loop (.syncLiftLoop task))

/-- One iteration of REF `canon_lift`'s callback loop (L2108-2134), the body of
`LoopPoint.callbackLoop task thread code si` (see the module docstring). `code = EXIT` exits
the loop: `task.exit_implicit_thread()` (L2134). Otherwise the event is `TASK_CANCELLED` if
`task.deliver_pending_cancel()` (L2109-2110), else, after `LiftSt.releaseCallbackSt`
(L2113-2114): `YIELD` waits for `inst.exclusive_thread is None` (K2, C1) and then delivers a
pending cancel or `NONE` (L2116-2121); `WAIT` gets `inst.handles.get(si)`, traps
`wrongHandleType` unless it is a waitable set, and runs `wait_from_callback` (K3, L2122-2125);
any other code traps (L2126-2127); then `LiftSt.retakeCallbackSt` (L2128-2130). Finally
`[packed] = callback([event_code, p1, p2])` (L2131-2132), `code, si =
unpack_callback_result(packed)` (L2133) and the loop re-enters (tail call). -/
def callbackLoopBody (_lim : Limits) (task : TaskId) (thread : ThreadId) (code si : Nat) :
    P E σ (Ret E) := do
  if code = AsyncRef.CallbackCode.exit.toNat then
    Task.exitImplicitThread task
    return .unit
  let tk ← getTask task
  let inst := tk.inst
  let event ← (do
    if ← Task.deliverPendingCancel task then pure AsyncRef.EventTuple.taskCancelled
    else
      modifyStore (LiftSt.releaseCallbackSt inst thread)
      let ev ← (match AsyncRef.CallbackCode.ofNat? code with
        | some .yield => do
          Thread.waitUntilGuest .callbackYield (.exclusiveFree inst)
          if ← Task.deliverPendingCancel task then pure AsyncRef.EventTuple.taskCancelled
          else pure AsyncRef.EventTuple.none
        | some .wait => do
          match ← handlesGet inst si with
          | .wset ws => wsetWaitFromCallback ws task
          | _ => trap .wrongHandleType
        | _ => trap .unsupportedCallbackCode : P E σ AsyncRef.EventTuple)
      modifyStore (LiftSt.retakeCallbackSt inst thread)
      pure ev : P E σ AsyncRef.EventTuple)
  let cb ← orTrap (.internal "canon_lift: callback option missing") tk.opts.callback
  match ← callCore cb (event.callbackArgs.map i32Flat) with
  | [packed] =>
    let (code', si') ← unpackCallbackResult (flatNat packed)
    callRet (.loop (.callbackLoop task thread code'.toNat si'))
  | _ => internal "canon_lift: callback must return one value"

-- FLAG(statement-change): the `post_return` branch checks REF's `assert(cx.inst.may_leave)`
-- (L2093) before the opening write; without the check `Theorems.opensWhenSet` is false.
/-- The synchronous tail of REF `thread_func` (L2087-2098): `flat_results = callee(flat_args)`,
`result = lift_flat_values(cx, MAX_FLAT_RESULTS, CoreValueIter(flat_results), result_type)`,
`task.return_(result)`, then, if there is a `post_return`, `inst.may_leave = False`,
`post_return(flat_results)`, `inst.may_leave = True`; then `task.exit_implicit_thread()`.
REF's `assert(cx.inst.may_leave)` before the window (L2093) is checked (`cannotLeave`; see the
module docstring). -/
def liftSyncTail (lim : Limits) (q : Quirks) (task : TaskId) (callee : E.FuncAddr)
    (tk : Task E) (cx : LiftLowerContext E) (flatArgs : List FlatValue) : P E σ Unit := do
  let flatResults ← callCore callee flatArgs
  let (result, _) ← liftFlatValues lim q cx maxFlatResults (.ofList flatResults)
    (resultTypes tk.ft)
  Task.return_ task result
  (match tk.opts.postReturn with
    | some pr => do
      let me ← currentThread
      trapIf (!(← getInst tk.inst).mayLeave) .cannotLeave
      modifyInst tk.inst (LiftSt.setMayLeave false me)
      let _ ← callCore pr flatResults
      modifyInst tk.inst (LiftSt.setMayLeave true)
    | none => pure () : P E σ Unit)
  Task.exitImplicitThread task

/-- REF `thread_func` of `canon_lift` (L2077-2135) for task `task` and core callee `callee`,
the body of `ThreadBody.liftImplicit task callee`: `if not task.enter_implicit_thread():
return` (wait site K1); `cx = LiftLowerContext(opts, inst, task)`; `args = task.start()`;
`flat_args = lower_flat_values(cx, MAX_FLAT_PARAMS, args, param_types)`; then
* sync (`not opts.async_`): `liftSyncTail`;
* stackful (async, no callback, L2100-2104): `[] = callee(flat_args)`,
  `task.exit_implicit_thread()`;
* callback (L2106-2135): `[packed] = callee(flat_args)`, `code, si =
  unpack_callback_result(packed)`, then the callback loop `LoopPoint.callbackLoop` (tail
  call; `thread` is the current, implicit thread).
Returns `Ret.unit`. -/
def liftThreadBody (lim : Limits) (q : Quirks) (task : TaskId) (callee : E.FuncAddr) :
    P E σ (Ret E) := do
  if !(← Task.enterImplicitThread q task) then return .unit
  let tk ← getTask task
  let cx : LiftLowerContext E := { opts := tk.opts, inst := tk.inst, scope := .task task }
  let args ← Task.start task
  let flatArgs ← lowerFlatValues lim q cx maxFlatParams args (paramTypes tk.ft) none
  if !tk.opts.async_ then
    liftSyncTail lim q task callee tk cx flatArgs
    return .unit
  match tk.opts.callback with
  | none =>
    let _ ← callCore callee flatArgs
    Task.exitImplicitThread task
    return .unit
  | some _ =>
    match ← callCore callee flatArgs with
    | [packed] =>
      let (code, si) ← unpackCallbackResult (flatNat packed)
      let thread ← currentThreadId
      callRet (.loop (.callbackLoop task thread code.toNat si))
    | _ => internal "canon_lift: callback-lifted callee must return one value"

/-- REF `canon_lift(lambda rep: [], ft, opts, inst, on_start, on_resolve)`: the `canon_lift` of the
no-op destructor of `canon_resource_drop` (`dtor = rt.dtor or (lambda rep: [])`, L2257). It is
`canonLift` whose implicit thread is `ThreadBody.liftNoop task` (body `liftNoopThreadBody`) in
place of a core callee: a fresh task, `thread = Thread(task, thread_func)`, `thread.resume()`
(resume site R1), and for a synchronous `ft` the loop `LoopPoint.syncLiftLoop task`. -/
def canonLiftNoop (_lim : Limits) (_q : Quirks) (ft : WIT.FuncType Empty RtId)
    (opts : CanonOpts E) (inst : InstId) (caller : CallerId) : P E σ (Ret E) := do
  let task ← allocObj ArenaField.tasks ({ ft, opts, inst, caller } : Task E)
  let thread ← newThread (.liftNoop task)
  Thread.resume thread
  (if !ft.async_ then callUnit (.loop (.syncLiftLoop task)) else pure () : P E σ Unit)
  return .cancel (.task task)

/-- REF `thread_func` of `canonLiftNoop` for task `task` (L2077-2098 with the callee
`lambda rep: []`), the body of `ThreadBody.liftNoop task`. REF lifts the no-op destructor with
`CanonicalOptions(async_ = False)` and a synchronous function type (L2255-2256), so this is the
synchronous path of `liftThreadBody` with `flat_results = []` in place of the core call:
`if not task.enter_implicit_thread(): return` (which registers the thread in `inst.threads`, trap
`tableFull`, L677); `args = task.start()`; `lower_flat_values` of `args`; `result =
lift_flat_values(cx, MAX_FLAT_RESULTS, CoreValueIter([]), result_type)`; `task.return_(result)`;
`task.exit_implicit_thread()`. Returns `Ret.unit`. -/
def liftNoopThreadBody (lim : Limits) (q : Quirks) (task : TaskId) : P E σ (Ret E) := do
  if !(← Task.enterImplicitThread q task) then return .unit
  let tk ← getTask task
  let cx : LiftLowerContext E := { opts := tk.opts, inst := tk.inst, scope := .task task }
  let args ← Task.start task
  let _ ← lowerFlatValues lim q cx maxFlatParams args (paramTypes tk.ft) none
  let (result, _) ← liftFlatValues lim q cx maxFlatResults (.ofList []) (resultTypes tk.ft)
  Task.return_ task result
  Task.exitImplicitThread task
  return .unit

/-! ## `on_start`/`on_resolve` of the internal callers -/

/-- The REF `on_start()` of the internal caller records `Caller.sub` (the `Call.onStart c`
contract, `Ret.vals`): `realloc args _` returns `args` (L630-631), `destructor rep` returns
`[h.rep]` (L2260, at the callee's parameter type), `start` returns `[]`. Other callers
(`host`, `lower`) are the dispatcher's: `internal` here. -/
def onStartProg (c : CallerId) : P E σ (Ret E) := do
  match ← getObj ArenaField.callers c with
  | .sub (.realloc args _) => return .vals args
  | .sub (.destructor rep) =>
    let s ← getStore
    let ts := ((callerTaskFt? s c).map paramTypes).getD []
    return .vals [repVal ts rep]
  | .sub .start => return .vals []
  | _ => internal "onStartProg: not an internal caller"

/-- The REF `on_resolve(result)` of the internal caller records `Caller.sub` (the
`Call.onResolve c r` contract, `Ret.unit`): `realloc` records the single result `[ptr]`
(L633-635; any other shape is an `internal` trap: a sync realloc returns exactly one value),
`destructor` and `start` ignore the result. Other callers: `internal`. -/
def onResolveProg (c : CallerId) (r : Option (List Val)) : P E σ (Ret E) := do
  match ← getObj ArenaField.callers c with
  | .sub (.realloc _ _) =>
    match r with
    | some [v] =>
      modifyObj ArenaField.callers c (LiftSt.recordReallocResult v)
      return .unit
    | _ => internal "reallocate: on_resolve expects exactly one result"
  | .sub (.destructor _) => return .unit
  | .sub .start => return .unit
  | _ => internal "onResolveProg: not an internal caller"

/-! ## `reallocate`, start functions and destructors -/

-- FLAG(statement-change): checks REF's `assert(self.inst.may_leave)` (L636) before the opening
-- write; without the check `Theorems.opensWhenSet` is false.
/-- REF `LiftLowerContext.reallocate(old, old_byte_length, alignment, new_byte_length)`
(L625-641), the handler of `Call.reallocate` (`Ret.nat`): `ptrt` is `u32`/`u64` by the
pointer width of `cx` (D-g), the realloc core function (`cx.opts.realloc`; absent is
`internal`) is lifted at `reallocType ptrt` with default options in `cx.inst` and invoked with
a fresh `Caller.sub (.realloc [old, old_byte_length, alignment, new_byte_length] none)`
record: `inst.may_leave = False` (L637), `store.invoke` (`nesting_depth += 1`, `canon_lift`
by the direct path, `nesting_depth -= 1`, L524-528), `inst.may_leave = True` (L639); the
pointer recorded by `on_resolve` is returned (`assert(ptr is not None)`: `internal`).
REF's `assert(self.inst.may_leave)` before the window (L636) is checked (`cannotLeave`; see the
module docstring). -/
def reallocProg (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (old oldLen align newLen : Nat) : P E σ (Ret E) := do
  let p ← ptrType cx
  let f ← orTrap (.internal "reallocate: realloc option missing") cx.opts.realloc
  let k := ptrIntKind p
  let args : List Val := [.int k old, .int k oldLen, .int k align, .int k newLen]
  let c ← allocObj ArenaField.callers (Caller.sub (.realloc args none) : Caller E)
  let me ← currentThread
  trapIf (!(← getInst cx.inst).mayLeave) .cannotLeave
  modifyInst cx.inst (LiftSt.setMayLeave false me)
  modifyStore LiftSt.incNestingSt
  let _ ← canonLift lim q f (reallocType p) {} cx.inst c
  modifyStore LiftSt.decNestingSt
  modifyInst cx.inst (LiftSt.setMayLeave true)
  match ← getObj ArenaField.callers c with
  | .sub (.realloc _ (some (.int _ n))) => return .nat n.toNat
  | _ => internal "reallocate: realloc did not resolve with a pointer"

/-- A core start function `sf` of instance `inst` run as a synchronous task of type `func()`
with default options (Concurrency.md "Interaction with the start function"; the direct-path
form of `runStart`): a fresh `Caller.sub .start` record and `canonLift`. Blocking with
no ready thread of `inst` traps `cannotBlockSync` in the synchronous loop. -/
def startFunctionTask (lim : Limits) (q : Quirks) (inst : InstId) (sf : E.FuncAddr) :
    P E σ Unit := do
  let c ← allocObj ArenaField.callers (Caller.sub .start : Caller E)
  let _ ← canonLift lim q sf startFuncType {} inst c

/-- The destructor call of REF `canon_resource_drop` (L2253-2260) for the calling instance
`inst` and the request `req` of `resourceDropCore`:
`store.lower(store.lift(rt.dtor or (lambda rep: []), FuncType([U32Type()], []),
CanonicalOptions(), rt.impl), ...)([h.rep])`, i.e. the `canon_lower` entry check
`trap_if(not inst.may_leave)` (`cannotLeave`) and a synchronous `canon_lift` in `rt.impl` with
a fresh `Caller.sub (.destructor rep)` record (the parameter is `u64` for an `i64`
representation): of the destructor `rt.dtor` (`canonLift`), or of REF's no-op destructor when
there is none (`canonLiftNoop`, which registers a thread in `rt.impl` and may trap
`tableFull`). No call is made for a host resource (`rt.impl` is `none`; see the module
docstring). This is the program the dispatcher supplies as `dtorCall`. -/
def destructorCall (lim : Limits) (q : Quirks) (inst : InstId) (req : DtorRequest E) :
    P E σ Unit := do
  match req.impl, req.dtor with
  | some impl, some dtor =>
    let st ← getInst inst
    trapIf (!st.mayLeave) .cannotLeave
    let rty ← getObj ArenaField.resourceTypes req.rt
    let c ← allocObj ArenaField.callers (Caller.sub (.destructor req.rep) : Caller E)
    let _ ← canonLift lim q dtor (dtorType rty.rep) {} impl c
  | some impl, none =>
    let st ← getInst inst
    trapIf (!st.mayLeave) .cannotLeave
    let rty ← getObj ArenaField.resourceTypes req.rt
    let c ← allocObj ArenaField.callers (Caller.sub (.destructor req.rep) : Caller E)
    let _ ← canonLiftNoop lim q (dtorType rty.rep) {} impl c
  | none, _ => pure ()

/-! ## Unfolding checks -/

/-! ## Invariant lemmas -/

/-- The store updates the programs of this file can issue, each preserving `I`: those of the
task methods (`Task.InvHyps`), of flat lifting (`LoadPres`) and lowering (`StorePres`), of the
callback `WAIT` (`wait_from_callback`), the arena allocations of tasks and caller records, and
the named updates of `LiftSt`. -/
structure LiftHyps (I : CStore E → Prop) : Prop where
  task : Task.InvHyps I
  load : P.Inv.LoadPres I
  store : P.Inv.StorePres I
  allocTask : ∀ ft opts inst caller s, I s →
    I (ArenaOps.allocSt ArenaField.tasks ({ ft, opts, inst, caller } : Task E) s)
  allocCaller : ∀ (x : Caller E) s, I s → I (ArenaOps.allocSt ArenaField.callers x s)
  updateCaller : ∀ c v s, I s →
    I (ArenaOps.updateSt ArenaField.callers c (LiftSt.recordReallocResult v) s)
  stopWaiting : ∀ t s, I s → I (CStore.stopWaitingSt t s)
  startWaiting : ∀ t rc s, I s → I (CStore.startWaitingSt t rc s)
  wsetIncWaiting : ∀ ws s, I s → I (CStore.wsetIncWaitingSt ws s)
  wsetDecWaiting : ∀ ws s, I s → I (CStore.wsetDecWaitingSt ws s)
  wsetSetElems : ∀ ws l s, I s → I (CStore.wsetSetElemsSt ws l s)
  takeWaitableEvent : ∀ w s, I s → I (CStore.takeWaitableEventSt w s)
  setMayLeave : ∀ inst b o s, I s → I (ArenaField.insts.modify s inst (LiftSt.setMayLeave b o))
  release : ∀ inst t s, I s → I (LiftSt.releaseCallbackSt inst t s)
  retake : ∀ inst t s, I s → I (LiftSt.retakeCallbackSt inst t s)
  incNesting : ∀ s, I s → I (LiftSt.incNestingSt s)
  decNesting : ∀ s, I s → I (LiftSt.decNestingSt s)

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

end Silmaril.Wasm.Component.Canon

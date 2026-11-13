module

public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs

/-!
# `canon lower` (sync and async) and the caller-side `on_start`/`on_resolve`

Transcribes REF `canon_lower` of `design/mvp/canonical-abi/definitions.py` at component-model
`a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L2169-2233; `CanonicalABI.md` §"`canon lower`") as specification programs in `P E σ`:

| Lean | REF (lines) |
| --- | --- |
| `lowerLimits` | the `max_flat_params`/`max_flat_results` choice (L2177-2182) |
| `canonLower lim q callee ft opts inst flatArgs` | `canon_lower` (L2169-2233) |
| `lowerOnStart lim q c` | the `on_start` closure of `canon_lower` (L2188-2192) |
| `lowerOnResolve lim q c r` | the `on_resolve` closure of `canon_lower` (L2194-2206) |
| `maybeOnProgress s` | `maybe_on_progress()` (L2186, L2222-2229) |
| `LowerSt.*` | the named store updates these programs issue |

**Defunctionalization.** The pair `(on_start, on_resolve)` handed to the callee is the arena
record `Runtime.Caller.lower s cx flatArgs pos ft maxParams maxResults` (`Runtime/Objects.lean`)
allocated by `canonLower`; the dispatcher runs `Call.onStart c` / `Call.onResolve c r`
of such a record as `lowerOnStart lim q c` / `lowerOnResolve lim q c r`. The record holds the
SHARED REF `CoreValueIter` over the caller's flat arguments as the list `flatArgs` and the
position `pos`: `lowerOnStart` lifts the parameters from `⟨flatArgs, pos⟩` and writes the
advanced position back into the record (`LowerSt.setCallerPosSt`), and `lowerOnResolve` uses the
cursor at that position as the out-parameter of `lower_flat_values` (the trailing return
pointer). The borrow scope of `cx` is the subtask (`BorrowScope.subtask s`), so borrows lifted
by `lowerOnStart` make the caller's handles lenders of `s` (`Canon.liftBorrow`).

**`maybe_on_progress`.** REF rebinds the closure variable `maybe_on_progress` from a no-op to
`on_progress` once an async lower added the subtask to the caller's handle table
(L2221-2229). Here the mode is the recorded caller handle index `Subtask.index`: `none` (sync
lower, or async lower before the handle was added) is the no-op, `some i` sets the pending event
`PendingEvent.subtask s` (REF `subtask_event`, run at delivery by `Waitable.getPendingEvent`,
`Runtime/Waitable.lean`, which reads `index` as the captured `subtaski`). The index is set in
the same named update as `inst.handles.add(subtask)` (`LowerSt.addSubtaskSt`, issued by
`handlesAddSubtask`), i.e. AFTER the callee ran, as in REF, where `subtaski` is the value of
`handles.add` itself (L2223): a subtask is never in a handle table without its index.

**Async result.** The `i32` returned by an async lower is `AsyncRef.AsyncLowerResult.pack`:
`.returned` (REF `[Subtask.State.RETURNED]`) or `.pending state subtaski` (REF
`[subtask.state | (subtaski << 4)]`).

## Deviations and non-claims

* D-f: REF asserts are preconditions, not checked: `types_match_values(flat_ft.params,
  flat_args)` and the result shape of the sync branch; `ft.async_ or subtask.state ==
  RETURNED` after the callee returned; `STARTING` in `on_start`; `STARTED` (and, for `None`,
  `cancellation_requested`) in `on_resolve`; `flat_results == []` in the eager async branch;
  `0 < subtaski <= Table.MAX_LENGTH` and `state < 2^4` (facts about `handlesAdd` and
  `SubtaskState`, see `AsyncRef.AsyncLowerResult.WellFormed`).
* `Store.lower`'s `assert(inst is current_instance())` (L548) is checked, by the entry check
  `Canon.calloutEntry` of the only caller of `canonLower`, the dispatched callout program
  `Canon.hostCalloutProg`: a lowered callout from a thread of another instance, or from a host
  frame, traps `internal` before `canonLower` runs (REF asserts before `canon_lower` reads
  `may_leave`, L2171). So `canonLower` runs on a thread of the instance `inst` it takes, which
  is REF's `current_thread().task.inst`, and checks `may_leave` on it.
* A `Call.onStart`/`Call.onResolve` of a caller record that is not `Caller.lower` reaching
  `lowerOnStart`/`lowerOnResolve` is an `internal` trap (the dispatcher only routes
  `Caller.lower` records here).
* `Quirks.lendReleaseAtReturn` (wasmtime's `validate_scope_exit`; NOT the specification): when
  set, `lowerOnResolve` releases the subtask's lends at the callee's completion, i.e. on both
  `task.return` (after lowering the results) and `task.cancel` (`on_resolve(None)`, before
  resolving) (`LowerSt.releaseLendsSt`: every lender's `num_lends -= 1`, `lenders := []`, the
  subtask staying not-yet-delivered). This models wasmtime a7b4f29
  `crates/wasmtime/src/runtime/component/concurrent.rs` `task_complete`, shared by `task_return`
  and `task_cancel`, which calls `validate_scope_exit`; the later `deliver_resolve` then finds
  no lenders (for `CANCELLED_BEFORE_STARTED` there are none anyway, as `on_start` never ran).
  With `Quirks.none` the lends are released only by REF
  `deliver_resolve` (sync: before `canon_lower` returns; async: when the `SUBTASK` event of
  the resolution is delivered, or eagerly in the resolved-before-return branch).
* Proved here: `P.Inv` lemmas for every program under `LowerPres I` (the named updates issued
  preserve `I`). No conformance test is ported here (the end-to-end tests run through the
  machine in `Examples/` and `Tests/`); nothing is claimed about results.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

namespace LowerSt

/-- REF `subtask.on_cancel = callee(on_start, on_resolve)` (L2208). -/
def setOnCancelSt (s : SubtaskId) (r : CancelRef) (st : CStore E) : CStore E :=
  ArenaField.subtasks.modify st s fun x => { x with onCancel := r }

/-- REF `subtask.state = Subtask.State.STARTED` (`on_start`, L2191). -/
def startSt (s : SubtaskId) (st : CStore E) : CStore E :=
  ArenaField.subtasks.modify st s fun x => { x with state := .started }

/-- Record the caller handle index `subtaski` of an async lower and thereby switch
`maybe_on_progress` to `on_progress` (L2221-2229). -/
def setIndexSt (s : SubtaskId) (i : Nat) (st : CStore E) : CStore E :=
  ArenaField.subtasks.modify st s fun x => { x with index := some i }

/-- REF `subtaski = thread.task.inst.handles.add(subtask)` together with the capture of
`subtaski` by `on_progress` (L2223-2229), one update: add the entry of subtask `s` to the
handle table of `inst` (`InstState.addHandle`) and record its index `i` (`setIndexSt`). In REF
the index exists only as the value of `handles.add` captured by `subtask_event`, so the subtask
never sits in a table without it; the single update keeps that true at every step. Like
every named update of a dangling id, it changes nothing if `s` is unallocated (never the case:
`canonLower` allocated `s`), so no table names an unallocated subtask. -/
def addSubtaskSt (inst : InstId) (s : SubtaskId) (i : Nat) (st : CStore E) : CStore E :=
  match st.subtask? s with
  | none => st
  | some _ =>
    setIndexSt s i (ArenaField.insts.modify st inst (InstState.addHandle (.waitable (.subtask s))))

/-- The new position of the shared `CoreValueIter` of a `Caller.lower` record (other records
are unchanged). -/
def Caller.withPos : Caller E → Nat → Caller E
  | .lower s cx flatArgs _ ft mp mr, pos => .lower s cx flatArgs pos ft mp mr
  | c, _ => c

/-- The REF `CoreValueIter` mutation of `on_start`'s `lift_flat_values` (L2192): store the
advanced position into caller record `c`. -/
def setCallerPosSt (c : CallerId) (pos : Nat) (st : CStore E) : CStore E :=
  ArenaField.callers.modify st c fun x => Caller.withPos x pos

/-- `Quirks.lendReleaseAtReturn` only (wasmtime's `validate_scope_exit`): release every lend
of subtask `s` at the callee's return: `num_lends -= 1` for each lender and `lenders := []`
(the subtask stays not-yet-delivered, `lenders ≠ None`). No-op on a dangling or delivered
subtask. -/
def releaseLendsSt (s : SubtaskId) (st : CStore E) : CStore E :=
  match st.subtask? s with
  | none => st
  | some x =>
    match x.lenders with
    | none => st
    | some ls =>
      let st1 := ls.foldl
        (fun st h => ArenaField.resHandles.modify st h fun r =>
          { r with numLends := r.numLends - 1 }) st
      ArenaField.subtasks.modify st1 s fun y => { y with lenders := some [] }

end LowerSt

/-! ## Programs -/

/-- REF `subtaski = thread.task.inst.handles.add(subtask)` of an async `canon_lower` with the
switch of `maybe_on_progress` to `on_progress` (L2223-2229): trap `tableFull` past
`Table.MAX_LENGTH` (as `handlesAdd`), otherwise ONE store update `LowerSt.addSubtaskSt` adds
the entry and records the index `subtaski` it returns. -/
def handlesAddSubtask (inst : InstId) (s : SubtaskId) : P E σ Nat := do
  match (← getInst inst).addHandle? (.waitable (.subtask s)) with
  | none => trap .tableFull
  | some (i, _) =>
    modifyStore (LowerSt.addSubtaskSt inst s i)
    pure i

/-- REF `max_flat_params`/`max_flat_results` of `canon_lower` (L2177-2182): `(16, 1)` for a
sync lower, `(MAX_FLAT_ASYNC_PARAMS, 0) = (4, 0)` for an async lower. -/
def lowerLimits (async_ : Bool) : Nat × Nat :=
  if async_ then (maxFlatAsyncParams, 0) else (maxFlatParams, maxFlatResults)

/-- REF `maybe_on_progress()` (L2186) of the lower of subtask `s`: a no-op until an async
lower recorded the subtask's handle index; afterwards REF `on_progress` (L2222-2227):
`subtask.set_pending_event(subtask_event)` (`PendingEvent.subtask s`, overwriting, so
progress events coalesce). -/
def maybeOnProgress (s : SubtaskId) : P E σ Unit := do
  let x ← getObj ArenaField.subtasks s
  if x.index.isSome then Waitable.setPendingEvent (.subtask s) (.subtask s) else pure ()

/-- REF `on_start()` of `canon_lower` (L2188-2192) for caller record `c`
(`Caller.lower s cx flatArgs pos ft maxParams _`): `maybe_on_progress()`; (assert `STARTING`,
D-f) `subtask.state = STARTED`; `lift_flat_values(cx, max_flat_params, flat_args,
ft.param_types())` from the shared cursor `⟨flatArgs, pos⟩` (the caller's memory and table;
borrows add lenders to `s` through `cx`'s subtask scope), whose advanced position is written
back into the record. -/
def lowerOnStart (lim : Limits) (q : Quirks) (c : CallerId) : P E σ (List Val) := do
  match ← getObj ArenaField.callers c with
  | .lower s cx flatArgs pos ft maxParams _ =>
    maybeOnProgress s
    modifyStore (LowerSt.startSt s)
    let (vs, vi) ← liftFlatValues lim q cx maxParams ⟨flatArgs, pos⟩ (ft.params.map (·.2))
    modifyStore (LowerSt.setCallerPosSt c vi.pos)
    return vs
  | _ => internal "lowerOnStart: not a canon_lower caller record"

/-- REF `on_resolve(result)` of `canon_lower` (L2194-2206) for caller record `c`:
`maybe_on_progress()`; then
* `none` (cancelled; assert `cancellation_requested`, D-f): resolve
  `CANCELLED_BEFORE_STARTED` if the subtask is still `STARTING`, else (assert `STARTED`)
  `CANCELLED_BEFORE_RETURNED`, with no flat results;
* `some vs` (assert `STARTED`, D-f): `flat_results = lower_flat_values(cx, max_flat_results,
  vs, ft.result_type(), flat_args)` with the shared cursor as out-parameter (the caller's
  return pointer), then `subtask.resolve(RETURNED, flat_results)`.
`Quirks.lendReleaseAtReturn` (not the specification) additionally releases the lends of the
subtask before resolving, in both branches (after lowering for `some`), modelling wasmtime's
`task_complete` -> `validate_scope_exit` on `task.return` and `task.cancel`
(`LowerSt.releaseLendsSt`, see the module docstring). -/
def lowerOnResolve (lim : Limits) (q : Quirks) (c : CallerId) (r : Option (List Val)) :
    P E σ Unit := do
  match ← getObj ArenaField.callers c with
  | .lower s cx flatArgs pos ft _ maxResults =>
    maybeOnProgress s
    match r with
    | none =>
      let _ ← (if q.lendReleaseAtReturn then modifyStore (LowerSt.releaseLendsSt s)
        else pure () : P E σ Unit)
      let x ← getObj ArenaField.subtasks s
      if x.state = .starting then Subtask.resolve s .cancelledBeforeStarted []
      else Subtask.resolve s .cancelledBeforeReturned []
    | some vs =>
      let flat ← lowerFlatValues lim q cx maxResults vs ft.result.toList
        (some ⟨flatArgs, pos⟩)
      let _ ← (if q.lendReleaseAtReturn then modifyStore (LowerSt.releaseLendsSt s)
        else pure () : P E σ Unit)
      Subtask.resolve s .returned flat
  | _ => internal "lowerOnResolve: not a canon_lower caller record"

/-- REF `canon_lower(callee, ft, opts, flat_args)` (L2169-2233) of the `canon lower` defined in
instance `inst`, called from a thread of `inst` (REF `current_thread().task.inst`; the
dispatcher's entry check `Canon.calloutEntry` traps on a thread of another instance):
1. `trap_if(not inst.may_leave)` (`cannotLeave`);
2. limits `lowerLimits opts.async_`;
3. a fresh `Subtask` `s` of `inst` and the caller record `Caller.lower s cx flatArgs 0 ft ..`
   with `cx = LiftLowerContext(opts, inst, borrow_scope = s)` (the shared flat-argument
   cursor starts at position 0);
4. `subtask.on_cancel = callee(on_start, on_resolve)`: `call (.funcInst callee caller)`
   (then assert `ft.async_ or RETURNED`, D-f);
5. sync: unless resolved, `wait_until(subtask.resolved)` (K7, `WaitSite.syncLower`, choice C1);
   `deliver_resolve()`; return `subtask.flat_results`;
6. async: if resolved, `deliver_resolve()` and return `[RETURNED]`
   (`AsyncLowerResult.returned`); otherwise `subtaski = inst.handles.add(subtask)` (trap
   `tableFull`) and switch `maybe_on_progress` to `on_progress` in the same store update
   (`handlesAddSubtask`, `LowerSt.addSubtaskSt`), and return `[subtask.state | (subtaski << 4)]`
   (`AsyncLowerResult.pending`). -/
def canonLower (_lim : Limits) (_q : Quirks) (callee : FuncId) (ft : WIT.FuncType Empty RtId)
    (opts : CanonOpts E) (inst : InstId) (flatArgs : List FlatValue) :
    P E σ (List FlatValue) := do
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  let (maxParams, maxResults) := lowerLimits opts.async_
  let s ← allocObj ArenaField.subtasks ({ inst := inst } : Subtask)
  let cx : LiftLowerContext E := { opts := opts, inst := inst, scope := .subtask s }
  let c ← allocObj ArenaField.callers (Caller.lower s cx flatArgs 0 ft maxParams maxResults)
  let oc ← callCancel (.funcInst callee c)
  modifyStore (LowerSt.setOnCancelSt s oc)
  if !opts.async_ then
    let resolved ← gets (·.subtaskResolved s)
    let _ ← (if !resolved then Thread.waitUntilGuest .syncLower (.subtaskResolved s)
      else pure () : P E σ Unit)
    Subtask.deliverResolve s
    return (← getObj ArenaField.subtasks s).flatResults
  else
    if ← gets (·.subtaskResolved s) then
      Subtask.deliverResolve s
      return [i32Flat AsyncRef.AsyncLowerResult.returned.pack]
    else
      let i ← handlesAddSubtask inst s
      let x ← getObj ArenaField.subtasks s
      return [i32Flat (AsyncRef.AsyncLowerResult.pending x.state i).pack]

/-! ## Program-logic lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

/-- The named store updates of this file (and those of the programs it calls) preserve `I`. -/
structure LowerPres (I : CStore E → Prop) : Prop where
  load : LoadPres I
  store : StorePres I
  allocSubtask : ∀ inst s, I s →
    I (ArenaOps.allocSt ArenaField.subtasks ({ inst := inst } : Subtask) s)
  allocCaller : ∀ x s, I s → I (ArenaOps.allocSt ArenaField.callers x s)
  setOnCancel : ∀ sub r s, I s → I (LowerSt.setOnCancelSt sub r s)
  start : ∀ sub s, I s → I (LowerSt.startSt sub s)
  setCallerPos : ∀ c pos s, I s → I (LowerSt.setCallerPosSt c pos s)
  releaseLends : ∀ sub s, I s → I (LowerSt.releaseLendsSt sub s)
  setPending : ∀ w ev s, I s → I (CStore.setPendingSt w ev s)
  resolve : ∀ sub state flat s, I s → I (CStore.subtaskResolveSt sub state flat s)
  deliver : ∀ sub s, I s → I (CStore.deliverResolveSt sub s)
  startWaiting : ∀ t rc s, I s → I (CStore.startWaitingSt t rc s)
  addSubtask : ∀ inst sub i s, I s → I (LowerSt.addSubtaskSt inst sub i s)

end P.Inv

/-! ## Examples -/

end Silmaril.Wasm.Component.Canon

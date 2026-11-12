module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs

/-!
# Handle lifting and lowering: resources, error contexts, stream/future ends

Specification programs `P E σ` transcribing the handle-valued lift/lower functions of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
and the table-manipulating cores of the resource built-ins:

| Lean | REF (lines) |
| --- | --- |
| `liftOwn lim cx rt i` | `lift_own` (L1425-1431) |
| `liftBorrow lim cx rt i` | `lift_borrow` (L1433-1439), `Subtask.add_lender` (L848-851) |
| `liftErrorContext lim cx i` | `lift_error_context` (L1368-1371) |
| `liftAsyncValue lim kind cx t i` | `lift_async_value` (L1447-1457) |
| `liftStream`, `liftFuture` | `lift_stream` (L1441-1442), `lift_future` (L1444-1445) |
| `lowerOwn lim cx rt rep` | `lower_own` (L1736-1738) |
| `lowerBorrow lim cx rt rep` | `lower_borrow` (L1740-1746) |
| `lowerErrorContext lim cx x` | `lower_error_context` (L1677-1678) |
| `lowerAsyncValue lim kind cx e` | `lower_async_value` (L1754-1760) |
| `lowerStream`, `lowerFuture` | `lower_stream` (L1748-1749), `lower_future` (L1751-1752) |
| `resourceNewCore lim inst rt rep` | `canon_resource_new` (L2237-2242) after `may_leave` |
| `resourceDropCore lim inst rt i` | `canon_resource_drop` (L2246-2263) up to the destructor call |
| `resourceRepCore lim inst rt i` | `canon_resource_rep` (L2267-2271) |

The REF type argument `t` of `lift_own`/`lift_borrow`/`lower_own`/`lower_borrow` is only used
through `t.rt`, so these programs take the resource type id `rt : RtId` directly (REF compares
resource types by object identity, `h.rt is not t.rt`; here: equality of arena ids).

**Structure.** Handle-table accesses go through the `Effects.lean` helpers `handlesAdd`,
`handlesGet`, `handlesRemove` (REF `Table.add/get/remove`, L665-685, trapping `tableFull` and
`unknownHandle`). Every other store mutation is one `modifyStore` of a *named* pure function
of namespace `HandleSt` (one per REF multi-field update), or an arena allocation `allocObj`.
Each program has a `P.Inv` lemma (namespace `P.Inv`) whose hypotheses are exactly that these
named updates preserve the invariant.

**Convention.** Every program takes the numeric `Limits` as its explicit leading argument
(unused here: the handle-table bound is the fixed `Runtime.Table.maxLength`, see
`Effects.lean`); no program here has a quirk branch (the wasmtime quirk
`lendReleaseAtReturn` concerns the *release* of lends, `Subtask.deliver_resolve`, not
`add_lender`), so none takes `Quirks`.

**Trap reasons** (informative; the specification compares traps only as "some trap"): an
entry of the wrong kind traps `wrongHandleType`; a resource-type mismatch
`resourceTypeMismatch`; a lent own handle `ownLent`; a borrow where an own is required
`notOwnHandle`; a stream/future end of the wrong element type `wrongHandleType`; a non-idle
end `liftBusyEnd`; an end in a waitable set `endInSet`.

## Deviations and non-claims

* (D-f) REF `assert`s are preconditions, never traps: `lift_borrow`'s "scope is a Subtask",
  `lower_borrow`'s "scope is a Task", `add_lender`'s "not resolved, not delivered",
  `lift_async_value`'s `not contains_borrow(t)` and `end.owner is cx.inst and end.index == i`,
  `lower_async_value`'s kind/type/state assertions, and `canon_resource_drop`'s "an own handle
  has no borrow scope". Where the precondition fixes the shape of data the program must
  inspect (the borrow scope; the scope task of a dropped borrow), a violation reaches
  `internal` (unreachable in well-formed runs); the other assertions are not checked.
* `resourceDropCore` returns `Option (DtorRequest E)` rather than
  `Option (E.FuncAddr × Nat)`: REF calls `rt.dtor or (lambda rep: [])` through
  `store.lift`/`store.lower` even when there is no destructor, and the no-op call still lifts
  in the implementing instance (it registers a thread there, which can trap `tableFull`). So
  the request records the optional destructor, the implementing instance `rt.impl` (`none` for
  a host resource, which REF does not have and for which no call is made) and the resource
  type besides the `rep`. `none` means a borrow handle was dropped (no call). The call itself
  is made by `resourceDrop` (`Canon/Builtins/Resource.lean`) through `Canon.destructorCall`
  (`Canon/Lift.lean`).
* The `ResourceHandle` objects stay in their (append-only) arena after their table entry is
  removed; only the table entry is freed, as REF frees only the table slot.
* Nothing here is proved about the counters `numLends`/`numBorrows` along runs. No tests
  here (`Examples/Resources.lean` and the `run_tests.py` ports test these programs).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.AsyncRef

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

namespace HandleSt

/-- REF `Subtask.add_lender(h)` (L848-851): `h.num_lends += 1; self.lenders.append(h)`, as one
update of the handle object `h` and the subtask `s` (the REF asserts are preconditions). -/
def addLender (s : SubtaskId) (h : HandleObjId) (st : CStore E) : CStore E :=
  let st := ArenaField.resHandles.modify st h fun rh => { rh with numLends := rh.numLends + 1 }
  ArenaField.subtasks.modify st s fun sub => { sub with lenders := sub.lenders.map (· ++ [h]) }

/-- REF `h.borrow_scope.num_borrows += 1` (`lower_borrow`, L1745). -/
def incBorrows (t : TaskId) (st : CStore E) : CStore E :=
  ArenaField.tasks.modify st t fun tk => { tk with numBorrows := tk.numBorrows + 1 }

/-- REF `h.borrow_scope.num_borrows -= 1` (`canon_resource_drop`, L2262). -/
def decBorrows (t : TaskId) (st : CStore E) : CStore E :=
  ArenaField.tasks.modify st t fun tk => { tk with numBorrows := tk.numBorrows - 1 }

/-- REF `end.owner = None; end.index = None` (`lift_async_value`, L1455-1456). -/
def releaseEnd (e : EndId) (st : CStore E) : CStore E :=
  ArenaField.ends.modify st e fun en => { en with owner := none, index := none }

/-- REF `end.owner = cx.inst` (`lower_async_value`, L1759). -/
def setEndOwner (e : EndId) (inst : InstId) (st : CStore E) : CStore E :=
  ArenaField.ends.modify st e fun en => { en with owner := some inst }

/-- REF `end.index = ...` (`lower_async_value`, L1760). -/
def setEndIndex (e : EndId) (i : Nat) (st : CStore E) : CStore E :=
  ArenaField.ends.modify st e fun en => { en with index := some i }

end HandleSt

/-! ## Handle objects -/

/-- The resource handle object behind table entry `e`, trapping `wrongHandleType` for any
other kind of entry (REF `trap_if(not isinstance(h, ResourceHandle))`). -/
def expectResource (e : HandleEntry) : P E σ HandleObjId :=
  match e with
  | .resource h => pure h
  | _ => trap .wrongHandleType

/-- The resource handle object `h`. -/
def getResHandle (h : HandleObjId) : P E σ ResourceHandle := getObj ArenaField.resHandles h

/-- The resource type `rt`. -/
def getResourceType (rt : RtId) : P E σ (ResourceType E) := getObj ArenaField.resourceTypes rt

/-- A fresh handle object `h` in the arena, then `inst.handles.add(h)` (REF `Table.add`,
L670-679; trap `tableFull`). -/
def addResHandle (inst : InstId) (h : ResourceHandle) : P E σ Nat := do
  let hid ← allocObj ArenaField.resHandles h
  handlesAdd inst (.resource hid)

/-! ## Resources -/

/-- REF `lift_own(cx, i, t)` (L1425-1431): `h = cx.inst.handles.remove(i)` FIRST (trap
`unknownHandle`), then trap unless `h` is a resource handle (`wrongHandleType`), of type `rt`
(`resourceTypeMismatch`), with `num_lends == 0` (`ownLent`), and owning (`notOwnHandle`);
return `h.rep`. The early removal is observable only through lockdown (a trap locks the whole store
down). -/
def liftOwn (_lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (i : Nat) : P E σ Nat := do
  let hid ← expectResource (← handlesRemove cx.inst i)
  let h ← getResHandle hid
  trapIf (h.rt != rt) .resourceTypeMismatch
  trapIf (h.numLends != 0) .ownLent
  trapIf (!h.own) .notOwnHandle
  return h.rep

/-- REF `lift_borrow(cx, i, t)` (L1433-1439). Precondition (REF assert, D-f): the borrow scope
is a `Subtask` (otherwise `internal`). `h = cx.inst.handles.get(i)` (trap `unknownHandle`),
trap unless a resource handle (`wrongHandleType`) of type `rt` (`resourceTypeMismatch`), then
`cx.borrow_scope.add_lender(h)` (L848-851, `HandleSt.addLender`: `num_lends += 1` and append
to `lenders`); return `h.rep`. Own and borrow handles may both be lent. -/
def liftBorrow (_lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (i : Nat) : P E σ Nat :=
  match cx.scope with
  | .subtask s => do
    let hid ← expectResource (← handlesGet cx.inst i)
    let h ← getResHandle hid
    trapIf (h.rt != rt) .resourceTypeMismatch
    modifyStore (HandleSt.addLender s hid)
    return h.rep
  | _ => internal "lift_borrow: borrow scope is not a Subtask (REF assert)"

/-- REF `lower_own(cx, rep, t)` (L1736-1738): add `ResourceHandle(t.rt, rep, own = True)` to
`cx.inst.handles` (trap `tableFull`) and return its index. -/
def lowerOwn (_lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) : P E σ Nat :=
  addResHandle cx.inst { rt := rt, rep := rep, own := true }

/-- REF `lower_borrow(cx, rep, t)` (L1740-1746). Precondition (REF assert, D-f): the borrow
scope is a `Task` `task` (otherwise `internal`). If `cx.inst is t.rt.impl` the borrow is
passed back to the implementing instance as the bare `rep` (no handle, no counter).
Otherwise create `ResourceHandle(t.rt, rep, own = False, borrow_scope = task)`, perform
`task.num_borrows += 1` (`HandleSt.incBorrows`) and return `cx.inst.handles.add(h)` (trap
`tableFull`), in this REF order. A host-defined resource (`impl = none`) is never
implemented by `cx.inst`. -/
def lowerBorrow (_lim : Limits) (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) :
    P E σ Nat :=
  match cx.scope with
  | .task task => do
    let rty ← getResourceType rt
    if rty.impl = some cx.inst then
      return rep
    else
      let hid ← allocObj ArenaField.resHandles
        { rt := rt, rep := rep, own := false, scope := some task }
      modifyStore (HandleSt.incBorrows task)
      handlesAdd cx.inst (.resource hid)
  | _ => internal "lower_borrow: borrow scope is not a Task (REF assert)"

/-! ## Error contexts -/

/-- REF `lift_error_context(cx, i)` (L1368-1371): `cx.inst.handles.get(i)` (NOT removed; trap
`unknownHandle`), trap unless an error context (`wrongHandleType`); return it (the shared,
immutable `ErrorContext` object, here its arena id). -/
def liftErrorContext (_lim : Limits) (cx : LiftLowerContext E) (i : Nat) : P E σ ErrCtxId := do
  match ← handlesGet cx.inst i with
  | .errCtx x => pure x
  | _ => trap .wrongHandleType

/-- REF `lower_error_context(cx, v)` (L1677-1678): add the same error context object under a
new index of `cx.inst.handles` (trap `tableFull`). -/
def lowerErrorContext (_lim : Limits) (cx : LiftLowerContext E) (x : ErrCtxId) : P E σ Nat :=
  handlesAdd cx.inst (.errCtx x)

/-! ## Stream and future ends -/

/-- The checks of REF `lift_async_value` (L1450-1454) on the removed entry `ent`: it must be
an end of class `kind` (REF `isinstance(end, ReadableEndT)`, trap `wrongHandleType`), of
element type `t` (`trap_if(end.t != t)`, `wrongHandleType`), idle (`liftBusyEnd`) and in no
waitable set (`endInSet`). Returns the end id. -/
def checkLiftEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ent : HandleEntry) :
    P E σ EndId :=
  match ent with
  | .waitable (.end_ e) => do
    let en ← getObj ArenaField.ends e
    trapIf (en.kind != kind) .wrongHandleType
    trapIf (en.t != t) .wrongHandleType
    trapIf (en.state != .idle) .liftBusyEnd
    trapIf en.common.wset.isSome .endInSet
    return e
  | _ => trap .wrongHandleType

/-- REF `lift_async_value(ReadableEndT, cx, i, t)` (L1447-1457); `kind` is the readable end
class (`.readableStream` for `lift_stream`, `.readableFuture` for `lift_future`).
`end = cx.inst.handles.remove(i)` (trap `unknownHandle`), the checks of `checkLiftEnd`, then
`end.owner = None; end.index = None` (`HandleSt.releaseEnd`): the end leaves the instance and
is transferred with the lifted value. Preconditions (REF asserts, D-f, not checked):
`not contains_borrow(t)`, `end.owner is cx.inst and end.index == i`. -/
def liftAsyncValue (_lim : Limits) (kind : EndKind) (cx : LiftLowerContext E)
    (t : Option (WIT.ClosedType RtId)) (i : Nat) : P E σ EndId := do
  let e ← checkLiftEnd kind t (← handlesRemove cx.inst i)
  modifyStore (HandleSt.releaseEnd e)
  return e

/-- REF `lift_stream(cx, i, t)` (L1441-1442). -/
def liftStream (lim : Limits) (cx : LiftLowerContext E) (t : Option (WIT.ClosedType RtId))
    (i : Nat) : P E σ EndId :=
  liftAsyncValue lim .readableStream cx t i

/-- REF `lift_future(cx, i, t)` (L1444-1445). -/
def liftFuture (lim : Limits) (cx : LiftLowerContext E) (t : Option (WIT.ClosedType RtId))
    (i : Nat) : P E σ EndId :=
  liftAsyncValue lim .readableFuture cx t i

/-- REF `lower_async_value(ReadableEndT, cx, end, t)` (L1754-1760): `end.owner = cx.inst`
(`HandleSt.setEndOwner`), then `end.index = cx.inst.handles.add(end)` (trap `tableFull`;
`HandleSt.setEndIndex`); return the index. The class `_kind` and REF's assertions (class,
element type, idle state, `not contains_borrow(t)`) are preconditions (D-f). -/
def lowerAsyncValue (_lim : Limits) (_kind : EndKind) (cx : LiftLowerContext E) (e : EndId) :
    P E σ Nat := do
  modifyStore (HandleSt.setEndOwner e cx.inst)
  let i ← handlesAdd cx.inst (.waitable (.end_ e))
  modifyStore (HandleSt.setEndIndex e i)
  return i

/-- REF `lower_stream(cx, end, t)` (L1748-1749). -/
def lowerStream (lim : Limits) (cx : LiftLowerContext E) (e : EndId) : P E σ Nat :=
  lowerAsyncValue lim .readableStream cx e

/-- REF `lower_future(cx, end, t)` (L1751-1752). -/
def lowerFuture (lim : Limits) (cx : LiftLowerContext E) (e : EndId) : P E σ Nat :=
  lowerAsyncValue lim .readableFuture cx e

/-! ## Cores of the resource built-ins (used by `Canon/Builtins/Resource.lean`) -/

/-- The destructor call REF `canon_resource_drop` (L2253-2259) makes when an own handle is
dropped: `store.lift(rt.dtor or (lambda rep: []), ft, opts, rt.impl)` lowered into the
current instance and called with `[h.rep]`. `dtor = none` is REF's no-op `lambda rep: []`,
which is still called through `lift`/`lower`. -/
structure DtorRequest (E : CoreEngine) where
  /-- The resource type of the dropped handle. -/
  rt : RtId
  /-- REF `rt.impl` (the instance the destructor runs in; `none` for host resources). -/
  impl : Option InstId
  /-- REF `rt.dtor` (`none`: the no-op `lambda rep: []`). -/
  dtor : Option E.FuncAddr
  /-- REF `h.rep`, the destructor's argument. -/
  rep : Nat
  deriving DecidableEq

/-- REF `canon_resource_new(rt, rep)` (L2237-2242) after `trap_if(not inst.may_leave)` (which
`Builtins.resourceNew` performs): add `ResourceHandle(rt, rep, own = True)` to `inst.handles` (trap
`tableFull`) and return the index. -/
def resourceNewCore (_lim : Limits) (inst : InstId) (rt : RtId) (rep : Nat) : P E σ Nat :=
  addResHandle inst { rt := rt, rep := rep, own := true }

/-- REF `canon_resource_rep(rt, i)` (L2267-2271): `h = inst.handles.get(i)` (trap
`unknownHandle`), trap unless a resource handle (`wrongHandleType`) of type `rt`
(`resourceTypeMismatch`); return `h.rep`. REF performs no `may_leave` check here. -/
def resourceRepCore (_lim : Limits) (inst : InstId) (rt : RtId) (i : Nat) : P E σ Nat := do
  let hid ← expectResource (← handlesGet inst i)
  let h ← getResHandle hid
  trapIf (h.rt != rt) .resourceTypeMismatch
  return h.rep

/-- The tail of REF `canon_resource_drop` for the removed handle `h`: an own handle requests
its destructor call (REF asserts `h.borrow_scope is None`: precondition); a borrow handle
performs `h.borrow_scope.num_borrows -= 1` (`HandleSt.decBorrows`; the scope task may be
another task than the current one) and requests nothing. -/
def dropHandleTail (rt : RtId) (h : ResourceHandle) : P E σ (Option (DtorRequest E)) :=
  if h.own then do
    let rty ← getResourceType rt
    return some { rt := rt, impl := rty.impl, dtor := rty.dtor, rep := h.rep }
  else
    match h.scope with
    | some task => do
      modifyStore (HandleSt.decBorrows task)
      return none
    | none => internal "resource.drop: borrow handle without a borrow scope"

/-- REF `canon_resource_drop(rt, i)` (L2246-2263) after `trap_if(not inst.may_leave)` and
before the destructor call (both in `Builtins.resourceDrop`): `h = inst.handles.remove(i)` (trap
`unknownHandle`), trap unless a resource handle (`wrongHandleType`) of type `rt`
(`resourceTypeMismatch`) with `num_lends == 0` (`ownLent`), then `dropHandleTail`. The result is the
destructor call to make (`some`, own handle) or `none` (borrow handle). -/
def resourceDropCore (_lim : Limits) (inst : InstId) (rt : RtId) (i : Nat) :
    P E σ (Option (DtorRequest E)) := do
  let hid ← expectResource (← handlesRemove inst i)
  let h ← getResHandle hid
  trapIf (h.rt != rt) .resourceTypeMismatch
  trapIf (h.numLends != 0) .ownLent
  dropHandleTail rt h

/-! ## Invariant preservation -/

/-- A handle-table entry that is not a subtask. Subtasks enter a table only through
`canon lower`'s `LowerSt.addSubtaskSt`, together with their index; every other insertion
(`handlesAdd`) adds such an entry. -/
def NotSubtaskEntry (e : HandleEntry) : Prop := ∀ sub, e ≠ .waitable (.subtask sub)

theorem NotSubtaskEntry.resource (h : HandleObjId) : NotSubtaskEntry (.resource h) :=
  fun _ e => nomatch e

theorem NotSubtaskEntry.errCtx (x : ErrCtxId) : NotSubtaskEntry (.errCtx x) :=
  fun _ e => nomatch e

theorem NotSubtaskEntry.wset (ws : WsetId) : NotSubtaskEntry (.wset ws) :=
  fun _ e => nomatch e

theorem NotSubtaskEntry.end_ (e : EndId) : NotSubtaskEntry (.waitable (.end_ e)) :=
  fun _ h => nomatch h

namespace P.Inv

variable {I : CStore E → Prop}

/-- Hypothesis shape: adding any entry other than a subtask (`NotSubtaskEntry`) to any
instance's handle table preserves `I`. -/
abbrev AddHandlePres (I : CStore E → Prop) : Prop :=
  ∀ s inst (e : {e : HandleEntry // NotSubtaskEntry e}), I s →
    I (ArenaField.insts.modify s inst (InstState.addHandle e.1))

/-- Hypothesis shape: removing any entry from any instance's handle table preserves `I`. -/
abbrev RemoveHandlePres (I : CStore E → Prop) : Prop :=
  ∀ s inst i, I s → I (ArenaField.insts.modify s inst (InstState.removeHandle i))

/-- Hypothesis shape: allocating any resource handle object preserves `I`. -/
abbrev AllocResHandlePres (I : CStore E → Prop) : Prop :=
  ∀ s (h : ResourceHandle), I s → I (ArenaOps.allocSt ArenaField.resHandles h s)

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon

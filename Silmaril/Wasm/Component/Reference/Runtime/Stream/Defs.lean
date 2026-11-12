module

public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs
public import Silmaril.Wasm.Component.Reference.Trap.Defs

/-!
# The stream/future `End` state machine (pure)

A transcription of the REF stream/future end logic of `design/mvp/canonical-abi/definitions.py`
at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
as PURE functions on the component store `Runtime.CStore E` (ends are `End E` records in the
`ends` arena, REF object identity is `EndId`):

| Lean | REF |
| --- | --- |
| `copyCore` | `End.copy` (L956-979), cases 1-5 |
| `copy` | `End.copy` behind the `trap_if(end.state != End.State.IDLE)` of `copy` (L2466) |
| `cancel` | `End.cancel` (L981-988), the coin flip is the Bool `notifyNow` (choice C5) |
| `forward` | `End.forward` (L990-1006), both the drop branch and the splice branch |
| `dropEnd` | `End.drop` (L1008-1016) with `Waitable.drop`/`join(None)` (L754-765) |
| `notify` | `StreamEnd.notify`/`FutureEnd.notify` (L1026-1066): only stores the closure |
| `deliver` | running the `stream_event`/`future_event` closure (L1028-1066) |
| `takeEvent` | `Waitable.get_pending_event` (L745-748) specialised to ends |
| `newStream`, `newFuture` | `new_stream`, `new_future` (L1085-1097) |

The pending-event closure is the defunctionalized `PendingEvent.streamEnd e progress` /
`PendingEvent.futureEnd e progress` (`Runtime/Objects.lean`); `notify` overwrites it, and all
state transitions happen when it is delivered (`deliver`). Stream delivery precedence is
DROPPED > CANCELLED > COMPLETED with payload `result | progress << 4`
(`Async.packStreamCopyResult`); future precedence is COMPLETED > DROPPED > CANCELLED with the
bare result (`Async.futureCopyPayload`). The event index is the end's CURRENT `index`.

## Element copying is abstracted

The pure layer never touches memory. When REF case 3 moves `n` elements, `copyCore` returns
`CopyAction.transfer writerEnd readerEnd n writerBuf readerBuf` with the two buffers AS THEY
WERE BEFORE the transfer; the Prog layer performs the element copy (and the per-element
handle transfers). The same-instance non-numeric trap (L964) is checked here, before `transfer`
is returned. Buffer bookkeeping is done here: the buffers' `progress` fields are advanced by `n`
(`BufferDesc.advance`), and the cumulative progress is what `notify` records.

Deviation (buffer cursor): REF `GuestBuffer.read`/`write` also advance `ptr` by
`n * elem_size(t)`. The pure layer keeps `ptr` as the buffer's BASE pointer and advances only
`progress`, so the REF cursor is `ptr + progress * elem_size(t)` (elem sizes need the memory's
address type, which lives in the core store). The Prog layer must use that cursor.

## Asserts and unreachable states (deviation D-f)

Python asserts are preconditions, never traps. Where a function needs a fallback for a
precondition violation it behaves as follows (all unreachable under `EndWF`, see
`Runtime/Stream/Properties.lean`, and the canon-level checks): unknown ends and a dangling or
self-referential `other` are `TrapReason.internal` for `copy`/`forward` and no-ops for the
store transformers; `cancel` of a non-`COPYING` end is a no-op; `cancel` with `other = none`
treats the peer as guest-owned (REF would crash on `self.other.owner`; the drop always left a
pending event there); `FutureEnd.notify` asserts `progress ∈ {0, 1}` and `deliver` treats
every nonzero progress as `1`; the future COMPLETED branch asserts `buffer is None` and
`deliver` clears the buffer unconditionally. `forward` additionally clears the `other` links of
the two forwarded ends in the splice branch (REF leaves them dangling; the ends are removed
from their handle tables and unreachable), which keeps link symmetry an invariant.

`copy` includes the canon-level idle check of `copy` (L2466): a `DONE` end traps with
`streamDone`, a `COPYING`/`CANCELLING_COPY` end with `concurrentStreamOp`. The other canon-level
checks (`may_leave`, handle type, element type, waitable-set membership, buffer bounds) belong to
the canon built-ins.

Not modelled here: memory access and element transfer, handle tables, waiting and
waitable-set event selection, host buffers' behaviour (choice point E1).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async

/-- The peer class of an end class (`new_stream`/`new_future` pair a readable end with a
writable end of the same kind). -/
def _root_.Silmaril.Wasm.Component.Async.EndKind.dual : EndKind → EndKind
  | .readableStream => .writableStream
  | .writableStream => .readableStream
  | .readableFuture => .writableFuture
  | .writableFuture => .readableFuture

/-- `Readable*End` classes (their `copy` passes `is_read = True`, L1070-1083). -/
def _root_.Silmaril.Wasm.Component.Async.EndKind.isReadable : EndKind → Bool
  | .readableStream | .readableFuture => true
  | .writableStream | .writableFuture => false

@[simp] theorem _root_.Silmaril.Wasm.Component.Async.EndKind.dual_dual (k : EndKind) :
    k.dual.dual = k := by cases k <;> rfl

@[simp] theorem _root_.Silmaril.Wasm.Component.Async.EndKind.isStream_dual (k : EndKind) :
    k.dual.isStream = k.isStream := by cases k <;> rfl

@[simp] theorem _root_.Silmaril.Wasm.Component.Async.EndKind.isReadable_dual (k : EndKind) :
    k.dual.isReadable = !k.isReadable := by cases k <;> rfl

variable {E : CoreEngine}

namespace BufferDesc

/-- Advance the buffer's `progress` by `n` (REF `read(n)`/`write(vs)` bookkeeping; the base
`ptr` is kept, see the module docstring). -/
def advance : BufferDesc E → Nat → BufferDesc E
  | .guest cx t ptr length progress, n => .guest cx t ptr length (progress + n)
  | .host b length progress, n => .host b length (progress + n)

@[simp] theorem progress_advance (b : BufferDesc E) (n : Nat) :
    (b.advance n).progress = b.progress + n := by cases b <;> rfl

@[simp] theorem remain_advance (b : BufferDesc E) (n : Nat) :
    (b.advance n).remain = b.remain - n := by
  cases b <;> simp [advance, remain] <;> omega

end BufferDesc

/-- The result of a copy at the pure level: nothing to move, or `n > 0` elements to move from
`writerBuf` (of `writerEnd`) to `readerBuf` (of `readerEnd`); the buffers are given as they were
before the transfer. -/
inductive CopyAction (E : CoreEngine) where
  | none
  | transfer (writerEnd readerEnd : EndId) (n : Nat) (writerBuf readerBuf : BufferDesc E)
  deriving DecidableEq

namespace End

/-- REF `has_pending_event`. -/
def hasPending (x : End E) : Bool := x.common.pending.isSome

/-- The defunctionalized closure `notify(progress)` of end `e` installs. -/
def pendingFor (x : End E) (e : EndId) (progress : Nat) : PendingEvent :=
  if x.kind.isStream then .streamEnd e progress else .futureEnd e progress

/-- REF `notify(progress)` on the record: `set_pending_event` (overwrite). -/
def withNotify (x : End E) (e : EndId) (progress : Nat) : End E :=
  { x with common := { x.common with pending := some (x.pendingFor e progress) } }

/-- Clear the pending event (the first half of `get_pending_event`). -/
def clearPending (x : End E) : End E :=
  { x with common := { x.common with pending := none } }

/-- The state transition of the `stream_event`/`future_event` closure with its captured
`progress`, and the copy result it reports. -/
def deliverStep (x : End E) (progress : Nat) : End E × CopyResult :=
  if x.kind.isStream then
    match x.other with
    | none => ({ x with buffer := none, state := .done }, .dropped)
    | some _ =>
      if x.state = .cancellingCopy then ({ x with buffer := none, state := .idle }, .cancelled)
      else ({ x with buffer := none, state := .idle }, .completed)
  else if progress ≠ 0 then ({ x with buffer := none, state := .done }, .completed)
  else match x.other with
    | none => ({ x with buffer := none, state := .done }, .dropped)
    | some _ => ({ x with buffer := none, state := .idle }, .cancelled)

/-- The event payload of a delivered copy result: `result | progress << 4` for streams, the bare
result for futures. -/
def payload (x : End E) (r : CopyResult) (progress : Nat) : Nat :=
  if x.kind.isStream then packStreamCopyResult r progress else futureCopyPayload r

/-- The peer update of `End.drop`: `other.other = None` and, if the peer is not DONE and has no
pending event, `other.notify(0)`. `o` is the peer's own id. -/
def dropPeer (y : End E) (o : EndId) : End E :=
  let y1 := { y with other := none }
  if y.state ≠ .done ∧ y.hasPending = false then y1.withNotify o 0 else y1

@[simp] theorem other_withNotify (x : End E) (e : EndId) (p : Nat) :
    (x.withNotify e p).other = x.other := rfl
@[simp] theorem kind_withNotify (x : End E) (e : EndId) (p : Nat) :
    (x.withNotify e p).kind = x.kind := rfl
@[simp] theorem state_withNotify (x : End E) (e : EndId) (p : Nat) :
    (x.withNotify e p).state = x.state := rfl
@[simp] theorem buffer_withNotify (x : End E) (e : EndId) (p : Nat) :
    (x.withNotify e p).buffer = x.buffer := rfl
@[simp] theorem pending_withNotify (x : End E) (e : EndId) (p : Nat) :
    (x.withNotify e p).common.pending = some (x.pendingFor e p) := rfl
@[simp] theorem other_clearPending (x : End E) : x.clearPending.other = x.other := rfl
@[simp] theorem kind_clearPending (x : End E) : x.clearPending.kind = x.kind := rfl
@[simp] theorem state_clearPending (x : End E) : x.clearPending.state = x.state := rfl
@[simp] theorem buffer_clearPending (x : End E) : x.clearPending.buffer = x.buffer := rfl

end End

/-- Replace end `e` (no-op if unallocated). -/
def setEnd (s : CStore E) (e : EndId) (x : End E) : CStore E := ArenaField.ends.set s e x

/-- `notify(progress)` (L1026-1066) of end `e`: install (overwrite) its pending event. The
buffer and state are only changed when the event is delivered (`deliver`). -/
def notify (e : EndId) (progress : Nat) (s : CStore E) : CStore E :=
  match s.end? e with
  | some x => setEnd s e (x.withNotify e progress)
  | none => s

/-- Run the pending-event closure of end `e` with its captured `progress`: the delivery-time
state transition of `stream_event`/`future_event` (L1028-1066) and the event tuple
`(event_code, index, payload)`, with the end's CURRENT index. -/
def deliver (e : EndId) (progress : Nat) (s : CStore E) : CStore E × EventTuple :=
  match s.end? e with
  | none => (s, EventTuple.none)
  | some x =>
    let r := x.deliverStep progress
    (setEnd s e r.1, ⟨x.kind.eventCode, x.index.getD 0, x.payload r.2 progress⟩)

/-- REF `Waitable.get_pending_event` (L745-748) on end `e`: clear the pending event and run it.
`none` if no end event is pending. -/
def takeEvent (e : EndId) (s : CStore E) : CStore E × Option EventTuple :=
  match s.end? e with
  | none => (s, none)
  | some x =>
    match x.common.pending with
    | some (.streamEnd _ p) | some (.futureEnd _ p) =>
      let r := deliver e p (setEnd s e x.clearPending)
      (r.1, some r.2)
    | _ => (s, none)

/-- REF `End.copy(buffer, is_read)` (L956-979), without the canon-level idle check:
1. peer dropped: just `COPYING` (the drop left a pending DROPPED event);
2. peer has no parked buffer: park `buf`;
3. both have room: same-instance non-numeric trap, then move `n = min` elements, notify both
   ends with their cumulative progress, unpark the peer's buffer if it is full;
4. `buf` has room (peer is zero-length) or a read meets a zero-length write: the peer's
   zero-length op completes, `buf` parks;
5. otherwise this zero-length op completes with progress 0; the peer stays parked. -/
def copyCore (e : EndId) (buf : BufferDesc E) (isRead : Bool) (s : CStore E) :
    Except TrapReason (CStore E × CopyAction E) :=
  match s.end? e with
  | none => .error (.internal "End.copy: unknown end")
  | some x =>
    if isRead ≠ x.kind.isReadable then .error (.internal "End.copy: wrong direction") else
    let x1 := { x with state := .copying }
    match x.other with
    | none => .ok (setEnd s e x1, .none)
    | some o =>
      if o = e then .error (.internal "End.copy: self-linked end") else
      match s.end? o with
      | none => .error (.internal "End.copy: dangling peer")
      | some y =>
        match y.buffer with
        | none => .ok (setEnd s e { x1 with buffer := some buf }, .none)
        | some ob =>
          if 0 < buf.remain ∧ 0 < ob.remain then
            if x.owner.isSome ∧ x.owner = y.owner ∧ ABI.noneOrNumberType x.t = false then
              .error .sameInstanceCopy
            else
              let n := min buf.remain ob.remain
              let ob' := ob.advance n
              let y' := { y.withNotify o ob'.progress with
                buffer := if ob'.remain = 0 then none else some ob' }
              .ok (setEnd (setEnd s e (x1.withNotify e (buf.advance n).progress)) o y',
                if isRead then .transfer o e n ob buf else .transfer e o n buf ob)
          else if 0 < buf.remain ∨ (isRead = true ∧ ob.remain = 0) then
            .ok (setEnd (setEnd s e { x1 with buffer := some buf }) o
              { y.withNotify o 0 with buffer := none }, .none)
          else .ok (setEnd s e (x1.withNotify e 0), .none)

/-- A stream/future read (`isRead`) or write of `buf` on end `e`: the idle check of the canon
`copy` (L2466; `streamDone` for a DONE end, `concurrentStreamOp` for a busy one) followed by
`End.copy` (`copyCore`). -/
def copy (e : EndId) (buf : BufferDesc E) (isRead : Bool) (s : CStore E) :
    Except TrapReason (CStore E × CopyAction E) :=
  match s.end? e with
  | none => .error (.internal "copy: unknown end")
  | some x =>
    match x.state with
    | .idle => copyCore e buf isRead s
    | .done => .error (.streamDone (!x.kind.isStream) (!x.kind.isReadable))
    | .copying | .cancellingCopy => .error .concurrentStreamOp

/-- REF `self.other.owner is not None` in `End.cancel` (L984). With `other = none` (unreachable:
the drop left a pending event) the peer counts as guest-owned. -/
def peerGuest (x : End E) (s : CStore E) : Bool :=
  match x.other with
  | some o => match s.end? o with
    | some y => y.owner.isSome
    | none => true
  | none => true

/-- REF `End.cancel` (L981-988): `CANCELLING_COPY`, and `notify(0)` if no event is pending and
(the peer is guest-owned or `notifyNow`). `notifyNow` is choice point C5 (the deterministic
profile passes `true`). -/
def cancel (e : EndId) (notifyNow : Bool) (s : CStore E) : CStore E :=
  match s.end? e with
  | none => s
  | some x =>
    if x.state ≠ .copying then s else
    let x1 := { x with state := .cancellingCopy }
    if x.hasPending = false ∧ (peerGuest x s = true ∨ notifyNow = true) then
      setEnd s e (x1.withNotify e 0)
    else setEnd s e x1

/-- Remove end `e` from waitable set `w` (`WaitableSet.elems.remove`). -/
def leaveSet (w : Option WsetId) (e : EndId) (s : CStore E) : CStore E :=
  match w with
  | none => s
  | some w => ArenaField.wsets.modify s w fun ws => { ws with elems := ws.elems.erase (.end_ e) }

/-- REF `End.drop` (L1008-1016): unlink the peer (notifying it with progress 0 unless it is DONE
or already has a pending event), clear `other`, and leave the waitable set
(`Waitable.drop`). -/
def dropEnd (e : EndId) (s : CStore E) : CStore E :=
  match s.end? e with
  | none => s
  | some x =>
    let s1 := match x.other with
      | none => s
      | some o =>
        if o = e then s else
        match s.end? o with
        | none => s
        | some y => setEnd s o (y.dropPeer o)
    leaveSet x.common.wset e
      (setEnd s1 e { x with other := none, common := { x.common with wset := none } })

/-- REF `End.forward(src, dst)` (L990-1006) of a readable end `src` and a writable end `dst`:
* if `src.other is dst`, or either end's peer was dropped: `src.drop(); dst.drop()`;
* otherwise splice the writer `W = src.other` to the reader `R = dst.other` and, if both have a
  parked buffer, re-issue the copy of the one with less remaining room (`copyCore`).
The two forwarded ends are unlinked (see the module docstring). -/
def forward (src dst : EndId) (s : CStore E) : Except TrapReason (CStore E × CopyAction E) :=
  match s.end? src, s.end? dst with
  | some xs, some xd =>
    if xs.kind.isReadable = false ∨ xd.kind ≠ xs.kind.dual then
      .error (.internal "End.forward: wrong end kinds")
    else
    match xs.other, xd.other with
    | some w, some r =>
      if w = dst then .ok (dropEnd dst (dropEnd src s), .none) else
      if r = src ∨ w = src ∨ r = dst ∨ w = r then .error (.internal "End.forward: bad links")
      else
      match s.end? w, s.end? r with
      | some yw, some yr =>
        let s1 := setEnd (setEnd s src { xs with other := none }) dst { xd with other := none }
        let yw1 := { yw with other := some r }
        let yr1 := { yr with other := some w }
        match yw.buffer, yr.buffer with
        | some bw, some br =>
          if bw.remain < br.remain then
            copyCore w bw false (setEnd (setEnd s1 w { yw1 with buffer := none }) r yr1)
          else
            copyCore r br true (setEnd (setEnd s1 w yw1) r { yr1 with buffer := none })
        | _, _ => .ok (setEnd (setEnd s1 w yw1) r yr1, .none)
      | _, _ => .error (.internal "End.forward: dangling peer")
    | _, _ => .ok (dropEnd dst (dropEnd src s), .none)
  | _, _ => .error (.internal "End.forward: unknown end")

/-- A linked `(readable, writable)` pair of ends of class `k` (readable allocated first). -/
def newEnds (k : EndKind) (t : Option (WIT.ClosedType RtId)) (owner : Option InstId)
    (s : CStore E) : CStore E × EndId × EndId :=
  let r : EndId := ⟨s.ends.length⟩
  let w : EndId := ⟨s.ends.length + 1⟩
  let s1 := (ArenaField.ends.alloc s { kind := k, t, owner, other := some w }).1
  let s2 := (ArenaField.ends.alloc s1 { kind := k.dual, t, owner, other := some r }).1
  (s2, r, w)

/-- REF `new_stream(t, owner)` (L1085-1090): `(readable, writable)`. -/
def newStream (t : Option (WIT.ClosedType RtId)) (owner : Option InstId) (s : CStore E) :
    CStore E × EndId × EndId :=
  newEnds .readableStream t owner s

/-- REF `new_future(t, owner)` (L1092-1097): `(readable, writable)`. -/
def newFuture (t : Option (WIT.ClosedType RtId)) (owner : Option InstId) (s : CStore E) :
    CStore E × EndId × EndId :=
  newEnds .readableFuture t owner s

/-! ## Tests (kernel-checked by `rfl`, any engine, host buffers)

Ends `0,1` are the first pair, `2,3` the second (readable first). -/

section Tests

end Tests

end Silmaril.Wasm.Component.Runtime

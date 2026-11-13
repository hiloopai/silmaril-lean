module

public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Store
public import Silmaril.Raw.Wasm.Component.ABI.Predicates
public import Silmaril.Raw.Wasm.Component.Trap

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
(`AsyncRef.packStreamCopyResult`); future precedence is COMPLETED > DROPPED > CANCELLED with the
bare result (`AsyncRef.futureCopyPayload`). The event index is the end's CURRENT `index`.

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

open Engine AsyncRef

theorem _root_.Silmaril.Wasm.Component.AsyncRef.EndKind.dual_ne (k : EndKind) : k.dual ≠ k := by
  cases k <;> decide

variable {E : CoreEngine}

namespace BufferDesc

end BufferDesc

namespace End

theorem deliverStep_other (x : End E) (p : Nat) : (x.deliverStep p).1.other = x.other := by
  unfold deliverStep; split
  · split <;> (try split) <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem deliverStep_kind (x : End E) (p : Nat) : (x.deliverStep p).1.kind = x.kind := by
  unfold deliverStep; split
  · split <;> (try split) <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem deliverStep_buffer (x : End E) (p : Nat) : (x.deliverStep p).1.buffer = none := by
  unfold deliverStep; split
  · split <;> (try split) <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem deliverStep_state (x : End E) (p : Nat) :
    (x.deliverStep p).1.state = .idle ∨ (x.deliverStep p).1.state = .done := by
  unfold deliverStep; split
  · split
    · exact .inr rfl
    · split <;> exact .inl rfl
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · exact .inl rfl

theorem dropPeer_other (y : End E) (o : EndId) : (y.dropPeer o).other = none := by
  unfold dropPeer; split <;> rfl
theorem dropPeer_kind (y : End E) (o : EndId) : (y.dropPeer o).kind = y.kind := by
  unfold dropPeer; split <;> rfl
theorem dropPeer_state (y : End E) (o : EndId) : (y.dropPeer o).state = y.state := by
  unfold dropPeer; split <;> rfl
theorem dropPeer_buffer (y : End E) (o : EndId) : (y.dropPeer o).buffer = y.buffer := by
  unfold dropPeer; split <;> rfl

end End

/-! ## Tests (kernel-checked by `rfl`, any engine, host buffers)

Ends `0,1` are the first pair, `2,3` the second (readable first). -/

section Tests

/-- A fresh host buffer of `n` elements. -/
private def hb (n : Nat) : BufferDesc E := .host ⟨0⟩ n 0

/-- Observable per-end summary: state, pending event, parked buffer. -/
private def obs (s : CStore E) (e : EndId) :
    Option (EndState × Option PendingEvent × Option (BufferDesc E)) :=
  (s.end? e).map fun x => (x.state, x.common.pending, x.buffer)

private def s1 (E : CoreEngine) : CStore E := (newStream none (some ⟨0⟩) CStore.empty).1
private def f1 (E : CoreEngine) : CStore E := (newFuture none (some ⟨0⟩) CStore.empty).1

example : (newStream none none (CStore.empty : CStore E)).2 = (⟨0⟩, ⟨1⟩) := rfl

/-- Zero-length write meets a parked zero-length read: the write completes (progress 0), the read
stays parked without an event. -/
example : ((copy ⟨0⟩ (hb 0) true (s1 E) >>= fun r => copy ⟨1⟩ (hb 0) false r.1).toOption.map
    fun r => (obs r.1 ⟨0⟩, obs r.1 ⟨1⟩, r.2)) =
    some (some (.copying, none, some (hb 0)), some (.copying, some (.streamEnd ⟨1⟩ 0), none),
      (.none : CopyAction E)) := rfl

/-- Zero-length read meets a parked zero-length write: the write completes, the read parks. -/
example : ((copy ⟨1⟩ (hb 0) false (s1 E) >>= fun r => copy ⟨0⟩ (hb 0) true r.1).toOption.map
    fun r => (obs r.1 ⟨0⟩, obs r.1 ⟨1⟩, r.2)) =
    some (some (.copying, none, some (hb 0)), some (.copying, some (.streamEnd ⟨1⟩ 0), none),
      (.none : CopyAction E)) := rfl

/-- Zero-length read against a parked real write completes eagerly; the write stays parked. -/
example : ((copy ⟨1⟩ (hb 3) false (s1 E) >>= fun r => copy ⟨0⟩ (hb 0) true r.1).toOption.map
    fun r => (obs r.1 ⟨0⟩, obs r.1 ⟨1⟩, r.2)) =
    some (some (.copying, some (.streamEnd ⟨0⟩ 0), none), some (.copying, none, some (hb 3)),
      (.none : CopyAction E)) := rfl

/-- A real write against a parked zero-length read: the read completes, the write parks. -/
example : ((copy ⟨0⟩ (hb 0) true (s1 E) >>= fun r => copy ⟨1⟩ (hb 3) false r.1).toOption.map
    fun r => (obs r.1 ⟨0⟩, obs r.1 ⟨1⟩, r.2)) =
    some (some (.copying, some (.streamEnd ⟨0⟩ 0), none), some (.copying, none, some (hb 3)),
      (.none : CopyAction E)) := rfl

/-- A 2-element write into a parked 5-element read: transfer of 2, the read stays parked with its
cumulative progress; a second write of 2 accumulates to 4. -/
example : ((copy ⟨0⟩ (hb 5) true (s1 E) >>= fun r => copy ⟨1⟩ (hb 2) false r.1).toOption.map
    fun r => (obs r.1 ⟨0⟩, obs r.1 ⟨1⟩, r.2)) =
    some (some (.copying, some (.streamEnd ⟨0⟩ 2), some (.host ⟨0⟩ 5 2)),
      some (.copying, some (.streamEnd ⟨1⟩ 2), none),
      CopyAction.transfer ⟨1⟩ ⟨0⟩ 2 (hb 2) (hb 5)) := rfl

example : ((copy ⟨0⟩ (hb 5) true (s1 E) >>= fun r => copy ⟨1⟩ (hb 2) false r.1 >>= fun r =>
      copy ⟨1⟩ (hb 2) false (takeEvent ⟨1⟩ r.1).1).toOption.map
    fun r => (obs r.1 ⟨0⟩, r.2)) =
    some (some (.copying, some (.streamEnd ⟨0⟩ 4), some (.host ⟨0⟩ 5 4)),
      CopyAction.transfer ⟨1⟩ ⟨0⟩ 2 (hb 2) (.host ⟨0⟩ 5 2)) := rfl

/-- Same-instance copy of a non-numeric element type traps with `sameInstanceCopy`. -/
example : (match (copy ⟨0⟩ (hb 1) true
    (newStream (some (.prim .char)) (some ⟨0⟩) (CStore.empty : CStore E)).1 >>=
    fun r => copy ⟨1⟩ (hb 1) false r.1) with
    | .error .sameInstanceCopy => true
    | _ => false) = true := rfl

/-- The same copy on host-created ends (no owning instance) transfers the element. -/
example : ((copy ⟨0⟩ (hb 1) true
    (newStream (some (.prim .char)) none (CStore.empty : CStore E)).1 >>=
    fun r => copy ⟨1⟩ (hb 1) false r.1).toOption.map fun r => r.2) =
    some (CopyAction.transfer ⟨1⟩ ⟨0⟩ 1 (hb 1) (hb 1)) := rfl

/-- Dropping an idle writer gives the reader exactly one DROPPED event. -/
example : let s := dropEnd ⟨1⟩ (s1 E)
    let r := takeEvent ⟨0⟩ s
    (r.2, obs r.1 ⟨0⟩, (takeEvent ⟨0⟩ r.1).2) =
      (some ⟨.streamRead, 0, packStreamCopyResult .dropped 0⟩, some (.done, none, none), none) :=
  rfl

/-- Cancelling a read after a partial completion reports CANCELLED with the full progress and
returns the end to IDLE. -/
example : ((copy ⟨0⟩ (hb 5) true (s1 E) >>= fun r => copy ⟨1⟩ (hb 2) false r.1).toOption.map
    fun r => let t := takeEvent ⟨0⟩ (cancel ⟨0⟩ false r.1); (t.2, obs t.1 ⟨0⟩)) =
    some (some ⟨.streamRead, 0, packStreamCopyResult .cancelled 2⟩, some (.idle, none, none)) :=
  rfl

/-- Cancelling a future read after the value arrived reports COMPLETED; the end is DONE and a
second read traps. -/
example : ((copy ⟨0⟩ (hb 1) true (f1 E) >>= fun r => copy ⟨1⟩ (hb 1) false r.1).toOption.map
    fun r => let t := takeEvent ⟨0⟩ (cancel ⟨0⟩ false r.1)
      (t.2, obs t.1 ⟨0⟩, (copy ⟨0⟩ (hb 1) true t.1).toOption.isSome)) =
    some (some ⟨.futureRead, 0, futureCopyPayload .completed⟩, some (.done, none, none), false) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- Forwarding into a writable end whose reader was dropped drops both forwarded ends; the source
writer gets a DROPPED event. -/
example : let s := (newStream none (some ⟨0⟩) (s1 E)).1
    ((forward ⟨0⟩ ⟨3⟩ (dropEnd ⟨2⟩ s)).toOption.map fun r =>
      ((takeEvent ⟨1⟩ r.1).2, (r.1.end? ⟨0⟩).map (·.other), (r.1.end? ⟨3⟩).map (·.other))) =
      some (some ⟨.streamWrite, 0, packStreamCopyResult .dropped 0⟩, some none, some none) :=
  rfl

/-- The self-loop `forward r w` of one pair drops both ends. -/
example : ((forward ⟨0⟩ ⟨1⟩ (s1 E)).toOption.map fun r =>
      ((r.1.end? ⟨0⟩).map (·.other), (r.1.end? ⟨1⟩).map (·.other), r.2)) =
      some (some none, some none, .none) := rfl

/-- Splicing: `forward r0 w3` links `w1` to `r2`; parked buffers are re-issued (the smaller
write moves 2 elements into the parked read). -/
example : let s := (newStream none (some ⟨0⟩) (s1 E)).1
    ((copy ⟨1⟩ (hb 2) false s >>= fun r => copy ⟨2⟩ (hb 5) true r.1 >>= fun r =>
      forward ⟨0⟩ ⟨3⟩ r.1).toOption.map fun r =>
      ((r.1.end? ⟨1⟩).map (·.other), (r.1.end? ⟨2⟩).map (·.other), r.2)) =
      some (some (some ⟨2⟩), some (some ⟨1⟩),
        CopyAction.transfer ⟨1⟩ ⟨2⟩ 2 (hb 2) (hb 5)) := rfl

end Tests

end Silmaril.Wasm.Component.Runtime

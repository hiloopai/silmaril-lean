module

public import Silmaril.Wasm.Component.Async.CabiCopy.Defs
public import Silmaril.Wasm.Component.Reference.Defs

@[expose] public section

/-!
# The transcription against silmaril's machine: the stream/future end state machine

`Silmaril.Wasm.Component.Async.Cabi` transcribes `definitions.py` at `d095e2f`; the reference
machine copied from silmaril (`Silmaril.Wasm.Component.Reference`, whose runtime is
`Silmaril.Wasm.Component.Runtime`) follows `definitions.py` at `a25fc0b`. Between the two
revisions no async state machine changed (`tools/wasm-tools/README.md`, section *async*), so on
the async fragment the two transcriptions should agree. This module relates them on the
**stream/future end state machine**, the part both model as pure state updates:
`End.copy` (`Cabi.Store.copyEnd` / `Runtime.copyCore`), the delivery of a pending event
(`Cabi.Store.deliverEnd` / `Runtime.takeEvent`), `End.cancel` (`cancelEnd` / `cancel`) and
`End.drop` (`dropEnd` / `Runtime.dropEnd`).

**The relation** (`EndsRel`): every end of the transcription and the end with the same id in
silmaril's store agree on what the state machine reads (`View`): the end class (`kindR`), the
element type up to what `End.copy` asks of it (`tyR`: whether it is `None` or a number),
the state, the peer, the parked buffer (`bufR`: silmaril's pure layer keeps a buffer's
`length` and `progress`; the transcription's buffer `b` becomes the host buffer `b`), the
owner, the handle index and the pending event (`pendR`: silmaril's defunctionalized closure
`streamEnd e p`/`futureEnd e p` for the transcription's recorded progress `p`). Waitable-set
membership and sync waiters are not compared.

Silmaril's pure layer does not touch memory (it returns the element move as a
`CopyAction`); the transcription moves the elements. The relation compares only the ends.
-/

namespace Silmaril.Wasm.Component.Async.CabiRef

open Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Component (WIT.ClosedType)

/-- The end classes. -/
def kindR : Cabi.EndKind → Silmaril.Wasm.Component.AsyncRef.EndKind
  | .streamR => .readableStream
  | .streamW => .writableStream
  | .futureR => .readableFuture
  | .futureW => .writableFuture

/-- The end states. -/
def stateR : Cabi.EndState → Silmaril.Wasm.Component.AsyncRef.EndState
  | .idle => .idle
  | .copying => .copying
  | .cancelling => .cancellingCopy
  | .done => .done

/-- An element type, as far as `End.copy` reads it (`none_or_number_type`): `None`, `u32`,
or `char` for any other type. -/
def tyR (t : Cabi.Ty) : Option (WIT.ClosedType RtId) :=
  match t.kind with
  | .none => none
  | .number => some (.prim .u32)
  | .other => some (.prim .char)

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {α : Type}

/-- The transcription's buffer `b` as a buffer of silmaril's pure layer. -/
def bufR (b : Nat) (x : Cabi.Buf α) : BufferDesc E := .host ⟨b⟩ x.length x.progress

/-- A pending event: the closure `notify(p)` installs. -/
def pendR (k : Cabi.EndKind) (e : Nat) : Option Nat → Option PendingEvent
  | none => none
  | some p => some (if k.isStream then .streamEnd ⟨e⟩ p else .futureEnd ⟨e⟩ p)

/-- What the end state machine reads of an end. -/
structure View (E : Silmaril.Wasm.Component.Engine.CoreEngine) where
  kind : Silmaril.Wasm.Component.AsyncRef.EndKind
  t : Option (WIT.ClosedType RtId)
  state : Silmaril.Wasm.Component.AsyncRef.EndState
  other : Option EndId
  buffer : Option (BufferDesc E)
  owner : Option InstId
  index : Option Nat
  pending : Option PendingEvent

/-- The view of one of silmaril's ends. -/
def viewS (x : End E) : View E :=
  ⟨x.kind, x.t, x.state, x.other, x.buffer, x.owner, x.index, x.common.pending⟩

/-- The view of the transcription's end `e` (`none` if its parked buffer is missing). -/
def viewC (st : Cabi.Store α) (e : Nat) (x : Cabi.End) : Option (View E) :=
  match x.buffer with
  | none => some ⟨kindR x.kind, tyR x.t, stateR x.state, x.other.map EndId.mk, none,
      x.owner.map InstId.mk, x.index, pendR x.kind e x.pending⟩
  | some b => (st.bufs b).map fun bx => ⟨kindR x.kind, tyR x.t, stateR x.state,
      x.other.map EndId.mk, some (bufR b bx), x.owner.map InstId.mk, x.index,
      pendR x.kind e x.pending⟩

/-- **The relation**: every end has the same view in both stores. -/
def EndsRel (st : Cabi.Store α) (s : CStore E) : Prop :=
  ∀ e, (s.end? ⟨e⟩).map viewS = (st.ends e).bind (viewC st e)

/-- The end after its stream event was delivered, in state `ns`. -/
def delivered (x : Cabi.End) (ns : Cabi.EndState) : Cabi.End :=
  { x with pending := none, buffer := none, state := ns }

/-- The three outcomes of `stream_event` (L1030–1048): `DROPPED` if the peer is gone (and
the end is not `DONE`), `CANCELLED` while cancelling, `COMPLETED` while copying. -/
def StreamOutcome (x : Cabi.End) (ns : Cabi.EndState) (r : Cabi.CopyResult) : Prop :=
  (x.other = none ∧ x.state ≠ .done ∧ ns = .done ∧ r = .dropped) ∨
  (x.other ≠ none ∧ x.state = .cancelling ∧ ns = .idle ∧ r = .cancelled) ∨
  (x.other ≠ none ∧ x.state = .copying ∧ ns = .idle ∧ r = .completed)

/-- No two ends park the same buffer. -/
def BufsDistinct (st : Cabi.Store α) : Prop :=
  ∀ e1 e2 x1 x2 b, st.ends e1 = some x1 → st.ends e2 = some x2 → x1.buffer = some b →
    x2.buffer = some b → e1 = e2

end Silmaril.Wasm.Component.Async.CabiRef

module

public import Silmaril.Net.Qpack.Section.Defs

@[expose] public section

/-!
# QPACK encoder and decoder connection state (RFC 9204 §2.1, §2.2)

**Encoder (§2.1).** The encoder keeps its copy of the dynamic table, the **Known Received
Count** ("the total number of dynamic table insertions and duplications acknowledged by the
decoder", §2.1.4), and the encoded field sections with dynamic references that the decoder has
not acknowledged yet, with the absolute indices each references (§2.1.1: "an encoder that uses
the dynamic table has to keep track of each dynamic table entry referenced by each field
section until those representations are acknowledged").

* *Decoder instructions (§4.4).* A Section Acknowledgment acknowledges "the earliest
  unacknowledged field section containing dynamic table references sent on the given stream"
  (§2.2.2.1) and raises the Known Received Count to its Required Insert Count (§2.1.4); one for
  a stream without such a section is `QPACK_DECODER_STREAM_ERROR` (§4.4.1). A Stream
  Cancellation drops the stream's outstanding sections (§2.2.2.2). An Insert Count Increment
  "equal to zero, or one that increases the Known Received Count beyond what the encoder has
  sent" is `QPACK_DECODER_STREAM_ERROR` (§4.4.3).
* *Evictability (§2.1.1, §2.2.2.2).* "When an entry with an absolute index lower than the Known
  Received Count has zero references, then it is considered evictable." "The encoder MUST NOT
  cause a dynamic table entry to be evicted unless that entry is evictable" (§3.2.2, §4.3.1).
  `Encoder.applyInstr` performs an encoder instruction on the encoder's table only when every
  entry it evicts is evictable (`evictionOk`); otherwise it refuses (`none`): the encoder MUST
  NOT send that instruction. The invariant `Encoder.Valid` says that every *pinned* entry
  (unacknowledged, or referenced by an outstanding section) is still in the table.
* *Blocked streams (§2.1.2).* "An encoder MUST limit the number of streams that could become
  blocked to the value of SETTINGS_QPACK_BLOCKED_STREAMS at all times." A stream could become
  blocked when it has an outstanding section whose Required Insert Count exceeds the Known
  Received Count (`blockingStreams`); `sendSection` refuses a section that would exceed the
  limit.

**Decoder (§2.2).** The decoder keeps its table, the streams currently blocked, and the insert
count it has reported (its view of the Known Received Count, §2.1.4).

* An encoder instruction updates the table (`DynTable.applyInstr`, errors
  `QPACK_ENCODER_STREAM_ERROR`).
* A field section either blocks its stream (§2.2.1) — "If a decoder encounters more blocked
  streams than it promised to support, it MUST treat this as a connection error of type
  QPACK_DECOMPRESSION_FAILED" (§2.1.2) — or is decoded, after which the decoder emits a Section
  Acknowledgment if its Required Insert Count is not zero (§2.2.2.1, §4.4.1).
* Abandoning a stream emits a Stream Cancellation (§2.2.2.2); `insertCountIncrement` reports
  new insertions (§2.2.2.3, §4.4.3).

Field sections are given here already parsed (`EncodedSection`); `decodeFieldSectionBytes` adds
the wire format.
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry)

/-! ## Distinct elements -/

/-- The distinct elements of a list (first occurrences dropped, order otherwise kept). -/
def distinct : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ distinct xs then distinct xs else x :: distinct xs

/-! ## Encoder -/

/-- An encoded field section with dynamic references, sent and not yet acknowledged. -/
structure Outstanding where
  streamId : Nat
  ric : Nat
  refs : List Nat
  deriving DecidableEq, Repr

/-- Remove the first element satisfying `p`. -/
def removeFirst (p : Outstanding → Bool) : List Outstanding → Option (Outstanding × List Outstanding)
  | [] => none
  | x :: xs =>
    if p x then some (x, xs) else (removeFirst p xs).map fun (y, ys) => (y, x :: ys)

/-- An encoder's connection state (§2.1). -/
structure Encoder where
  table : DynTable
  /-- The Known Received Count (§2.1.4). -/
  krc : Nat
  /-- Unacknowledged field sections with dynamic references, oldest first (§2.1.1). -/
  pending : List Outstanding
  /-- The peer's `SETTINGS_QPACK_BLOCKED_STREAMS` (§2.1.2, §5). -/
  maxBlocked : Nat
  deriving DecidableEq, Repr

namespace Encoder

/-- The initial encoder for a peer's maximum table capacity and blocked-streams limit. -/
def init (maxCapacity maxBlocked : Nat) : Encoder := ⟨.empty maxCapacity, 0, [], maxBlocked⟩

/-- All absolute indices referenced by outstanding sections. -/
def refs (enc : Encoder) : List Nat := enc.pending.flatMap Outstanding.refs

/-- An entry is evictable when acknowledged and unreferenced (§2.1.1, §2.2.2.2). -/
def Evictable (enc : Encoder) (a : Nat) : Prop := a < enc.krc ∧ a ∉ enc.refs

/-- An entry is pinned while unacknowledged or referenced: it must not be evicted. -/
def Pinned (enc : Encoder) (a : Nat) : Prop :=
  (enc.krc ≤ a ∧ a < enc.table.insertCount) ∨ a ∈ enc.refs

/-- The encoder invariant: a valid table, `KRC ≤ insert count`, outstanding sections that
reference only entries below their Required Insert Count (itself at most the insert count),
and every pinned entry still in the table. -/
def Valid (enc : Encoder) : Prop :=
  enc.table.Valid ∧ enc.krc ≤ enc.table.insertCount ∧
  (∀ s ∈ enc.pending, s.ric ≤ enc.table.insertCount ∧ ∀ a ∈ s.refs, a < s.ric) ∧
  (∀ a, enc.Pinned a → (enc.table.lookupAbs a).isSome)

/-- The streams that could become blocked (§2.1.2). -/
def blockingStreams (enc : Encoder) : List Nat :=
  distinct ((enc.pending.filter fun s => decide (enc.krc < s.ric)).map Outstanding.streamId)

/-- The blocked-streams bound (§2.1.2). -/
def BlockedOk (enc : Encoder) : Prop := (blockingStreams enc).length ≤ enc.maxBlocked

/-- The eviction guard (§2.1.1): every entry evicted on the way from the encoder's table to `t'`
(absolute indices `[dropped, dropped')`) is evictable. -/
def evictionOk (enc : Encoder) (t' : DynTable) : Bool :=
  (List.range' enc.table.dropped (t'.dropped - enc.table.dropped)).all fun a =>
    decide (a < enc.krc) && !(enc.refs.contains a)

/-- Perform an encoder instruction on the encoder's table, if allowed: it must be valid
(§4.3) and evict only evictable entries (§2.1.1, §3.2.2). -/
def applyInstr (enc : Encoder) (i : EncoderInstr) : Option Encoder :=
  match enc.table.applyInstr i with
  | .ok t' => if enc.evictionOk t' then some { enc with table := t' } else none
  | .error _ => none

/-- Record a field section sent on `streamId` with Required Insert Count `ric` referencing the
absolute indices `refs` (§2.1.1, §2.1.2). A section with `ric = 0` has no dynamic references
and is not tracked (it is never acknowledged, §4.4.1). Refused when a reference is not below
`ric`, names an entry not in the table, `ric` exceeds the insert count, or the stream would
exceed the blocked-streams limit. -/
def sendSection (enc : Encoder) (streamId ric : Nat) (refs : List Nat) : Option Encoder :=
  if ric = 0 then (if refs = [] then some enc else none)
  else if refs.all (fun a => decide (a < ric) && (enc.table.lookupAbs a).isSome) &&
      decide (ric ≤ enc.table.insertCount) &&
      (decide (ric ≤ enc.krc) || decide (streamId ∈ blockingStreams enc) ||
        decide ((blockingStreams enc).length < enc.maxBlocked)) then
    some { enc with pending := enc.pending ++ [⟨streamId, ric, refs⟩] }
  else none

/-- Process a decoder instruction (§4.4); errors are `QPACK_DECODER_STREAM_ERROR`. -/
def onDecoderInstr (enc : Encoder) : DecoderInstr → Except QpackError Encoder
  | .sectionAck s =>
    match removeFirst (fun o => o.streamId == s) enc.pending with
    | none => .error .decoderStreamError
    | some (o, rest) => .ok { enc with pending := rest, krc := max enc.krc o.ric }
  | .streamCancel s => .ok { enc with pending := enc.pending.filter fun o => o.streamId != s }
  | .insertCountIncrement k =>
    if k = 0 ∨ enc.table.insertCount < enc.krc + k then .error .decoderStreamError
    else .ok { enc with krc := enc.krc + k }

end Encoder

/-! ## Decoder -/

/-- A decoder's connection state (§2.2). -/
structure Decoder where
  table : DynTable
  /-- Our `SETTINGS_QPACK_BLOCKED_STREAMS` (§2.1.2, §5). -/
  maxBlocked : Nat
  /-- Streams with a blocked field section (§2.2.1). -/
  blocked : List Nat
  /-- The insert count reported to the encoder so far (§2.1.4). -/
  krc : Nat
  deriving DecidableEq, Repr

namespace Decoder

/-- The initial decoder for our maximum table capacity and blocked-streams limit. -/
def init (maxCapacity maxBlocked : Nat) : Decoder := ⟨.empty maxCapacity, maxBlocked, [], 0⟩

/-- The decoder invariant: a valid table, at most `maxBlocked` blocked streams, and a reported
count within the insert count. -/
def Valid (d : Decoder) : Prop :=
  d.table.Valid ∧ d.blocked.length ≤ d.maxBlocked ∧ d.krc ≤ d.table.insertCount

/-- Process an encoder instruction (§4.3). -/
def onEncoderInstr (d : Decoder) (i : EncoderInstr) : Except QpackError Decoder :=
  match d.table.applyInstr i with
  | .ok t' => .ok { d with table := t' }
  | .error e => .error e

/-- Process an encoded field section on `streamId` (§2.2.1, §2.2.2.1): the new state, the
field lines if decoded, and the decoder instruction to emit. -/
def onSection (d : Decoder) (streamId : Nat) (s : EncodedSection) :
    Except QpackError (Decoder × Option (List Entry) × Option DecoderInstr) :=
  match decodeFieldSection d.table s with
  | .error e => .error e
  | .ok (.blocked _) =>
    if streamId ∈ d.blocked then .ok (d, none, none)
    else if d.blocked.length < d.maxBlocked then
      .ok ({ d with blocked := streamId :: d.blocked }, none, none)
    else .error .decompressionFailed
  | .ok (.decoded ric fs) =>
    .ok ({ d with blocked := d.blocked.filter (· != streamId), krc := max d.krc ric }, some fs,
      if ric = 0 then none else some (.sectionAck streamId))

/-- Abandon a stream (§2.2.2.2): forget it and emit a Stream Cancellation. -/
def cancelStream (d : Decoder) (streamId : Nat) : Decoder × DecoderInstr :=
  ({ d with blocked := d.blocked.filter (· != streamId) }, .streamCancel streamId)

/-- Report new insertions (§2.2.2.3, §4.4.3): an Insert Count Increment bringing the Known
Received Count to the insert count, if it is behind. -/
def insertCountIncrement (d : Decoder) : Decoder × Option DecoderInstr :=
  if d.krc < d.table.insertCount then
    ({ d with krc := d.table.insertCount }, some (.insertCountIncrement (d.table.insertCount - d.krc)))
  else (d, none)

end Decoder

end Silmaril.Net.Qpack

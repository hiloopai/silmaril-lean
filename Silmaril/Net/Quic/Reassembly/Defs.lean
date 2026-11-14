module

public import Silmaril.Net.Quic.Error.Defs

@[expose] public section

/-!
# QUIC stream reassembly (RFC 9000 §2.2)

"STREAM frames encapsulate data sent by an application. An endpoint uses the Stream ID and
Offset fields in STREAM frames to place data in order. Endpoints MUST be able to deliver
stream data to an application as an ordered byte stream. Delivering an ordered byte stream
requires that an endpoint buffer any data that is received out of order" (§2.2).

* `Segment`: the data of one STREAM frame placed at its offset.
* `byteAt segs i`: the byte at offset `i`, taken from the first segment that covers it ("Data
  that has already been received can be discarded").
* `contiguous segs`: the longest gap-free prefix of the stream starting at offset 0: what can
  be delivered in order.
* `conflict segs g`: `g` carries a byte at some offset that differs from one already
  received. "The data at a given offset MUST NOT change if it is sent multiple times; an
  endpoint MAY treat receipt of different data at the same offset within a stream as a
  connection error of type PROTOCOL_VIOLATION."
* `RecvBuffer`: segments received plus the number of bytes `delivered` to the application.
  `insert strict g` adds a segment; with `strict` a conflicting one is PROTOCOL_VIOLATION
  (the MAY taken), without it the earlier bytes win. `read` hands the application the
  contiguous bytes it has not seen yet.

This is a reference model: segments are kept as received (no coalescing or freeing), which
keeps the specification obviously right and the theorems simple. Final sizes and the
FIN bit are in `Silmaril.Net.Quic.Stream`, flow-control limits in `Silmaril.Net.Quic.Flow`;
those bound how much a real buffer must hold ("up to the advertised flow control limit").
"Implementations MAY choose to offer the ability to deliver data out of order": not modelled.
-/

namespace Silmaril.Net.Quic

/-- Stream data placed at an offset (the payload of a STREAM frame). -/
structure Segment where
  offset : Nat
  data : List UInt8
  deriving DecidableEq, Repr, Inhabited

namespace Segment

/-- The end offset of a segment. -/
def stop (g : Segment) : Nat := g.offset + g.data.length

/-- The byte the segment carries at stream offset `i`. -/
def byteAt (g : Segment) (i : Nat) : Option UInt8 :=
  if g.offset ≤ i then g.data[i - g.offset]? else none

/-- The segment carries offset `i`. -/
def Covers (g : Segment) (i : Nat) : Prop := g.offset ≤ i ∧ i < g.stop

/-- The segment is the slice of the byte string `s` at its offset. -/
def SliceOf (s : List UInt8) (g : Segment) : Prop :=
  g.stop ≤ s.length ∧ g.data = (s.drop g.offset).take g.data.length

end Segment

/-- The byte at offset `i`, from the first segment carrying it. -/
def byteAt (segs : List Segment) (i : Nat) : Option UInt8 := segs.findSome? (·.byteAt i)

/-- Some received segment carries offset `i`. -/
def Covered (segs : List Segment) (i : Nat) : Prop := ∃ g ∈ segs, g.Covers i

/-- The largest end offset of the segments. -/
def maxStop (segs : List Segment) : Nat := segs.foldr (fun g m => max g.stop m) 0

/-- The bytes at `i, i+1, …` while they are known, for at most `k` bytes. -/
def prefixFrom {α : Type} (f : Nat → Option α) : Nat → Nat → List α
  | 0, _ => []
  | k + 1, i =>
    match f i with
    | none => []
    | some b => b :: prefixFrom f k (i + 1)

/-- The bytes deliverable in order: the gap-free prefix from offset 0. -/
def contiguous (segs : List Segment) : List UInt8 := prefixFrom (byteAt segs) (maxStop segs) 0

/-- `g` disagrees with a byte already received. -/
def conflict (segs : List Segment) (g : Segment) : Bool :=
  (List.range g.data.length).any fun k =>
    match byteAt segs (g.offset + k), g.data[k]? with
    | some b, some c => b != c
    | _, _ => false

/-- A stream's receive buffer. -/
structure RecvBuffer where
  /-- The segments received, in arrival order. -/
  segs : List Segment := []
  /-- The number of bytes handed to the application. -/
  delivered : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace RecvBuffer

/-- Receive a segment; with `strict`, changed data is PROTOCOL_VIOLATION (§2.2). -/
def insert (strict : Bool) (b : RecvBuffer) (g : Segment) : Except TransportError RecvBuffer :=
  if strict && conflict b.segs g then .error .protocolViolation
  else .ok { b with segs := b.segs ++ [g] }

/-- The application reads every newly contiguous byte. -/
def read (b : RecvBuffer) : List UInt8 × RecvBuffer :=
  let c := contiguous b.segs
  (c.drop b.delivered, { b with delivered := max b.delivered c.length })

/-- Events of the buffer: a segment arrives, or the application reads. -/
inductive Event where
  | recv (g : Segment)
  | read
  deriving DecidableEq, Repr

/-- The segment an event delivers, if any. -/
def Event.segment? : Event → Option Segment
  | .recv g => some g
  | .read => none

/-- Run events, collecting what the application read; stops at the first error. -/
def run (strict : Bool) : RecvBuffer → List Event → Except TransportError (List UInt8 × RecvBuffer)
  | b, [] => .ok ([], b)
  | b, .recv g :: es => (b.insert strict g).bind (run strict · es)
  | b, .read :: es =>
    let (out, b') := b.read
    (run strict b' es).map fun (out', b'') => (out ++ out', b'')

/-- Every segment received is a slice of `s`. -/
def SlicesOf (s : List UInt8) (b : RecvBuffer) : Prop := ∀ g ∈ b.segs, g.SliceOf s

end RecvBuffer

end Silmaril.Net.Quic

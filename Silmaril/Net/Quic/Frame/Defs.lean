module

public import Silmaril.Net.Quic.VarInt.Defs
public import Silmaril.Net.Quic.Error.Defs
public import Silmaril.Net.Quic.StreamId.Defs

@[expose] public section

/-!
# QUIC frames (RFC 9000 §12.4, §19; RFC 9221 §4)

"The payload of QUIC packets, after removing packet protection, consists of a sequence of
complete frames" (§12.4):

```
Packet Payload {
  Frame (8..) ...,
}

Frame {
  Frame Type (i),
  Type-Dependent Fields (..),
}
```

All integer fields marked `(i)` are variable-length integers (`Silmaril.Net.Quic.VarInt`,
§16). `Frame` has one constructor per frame type of Table 3 and of RFC 9221:

| Type | Frame | Layout after the type |
| --- | --- | --- |
| 0x00 | PADDING (§19.1) | – |
| 0x01 | PING (§19.2) | – |
| 0x02–0x03 | ACK (§19.3) | Largest, Delay, Range Count, First Range, (Gap, Length) …, [ECN] |
| 0x04 | RESET_STREAM (§19.4) | Stream ID, Application Protocol Error Code, Final Size |
| 0x05 | STOP_SENDING (§19.5) | Stream ID, Application Protocol Error Code |
| 0x06 | CRYPTO (§19.6) | Offset, Length, Crypto Data |
| 0x07 | NEW_TOKEN (§19.7) | Token Length, Token |
| 0x08–0x0f | STREAM (§19.8) | Stream ID, [Offset], [Length], Stream Data |
| 0x10 | MAX_DATA (§19.9) | Maximum Data |
| 0x11 | MAX_STREAM_DATA (§19.10) | Stream ID, Maximum Stream Data |
| 0x12–0x13 | MAX_STREAMS (§19.11) | Maximum Streams |
| 0x14 | DATA_BLOCKED (§19.12) | Maximum Data |
| 0x15 | STREAM_DATA_BLOCKED (§19.13) | Stream ID, Maximum Stream Data |
| 0x16–0x17 | STREAMS_BLOCKED (§19.14) | Maximum Streams |
| 0x18 | NEW_CONNECTION_ID (§19.15) | Sequence, Retire Prior To, Length (8), CID, Token (128) |
| 0x19 | RETIRE_CONNECTION_ID (§19.16) | Sequence Number |
| 0x1a | PATH_CHALLENGE (§19.17) | Data (64) |
| 0x1b | PATH_RESPONSE (§19.18) | Data (64) |
| 0x1c–0x1d | CONNECTION_CLOSE (§19.19) | Error Code, [Frame Type], Reason Length, Reason |
| 0x1e | HANDSHAKE_DONE (§19.20) | – |
| 0x30–0x31 | DATAGRAM (RFC 9221 §4) | [Length], Datagram Data |

**STREAM type bits (§19.8).** "The OFF bit (0x04) … When set to 0, the Offset field is absent
and the Stream Data starts at an offset of 0." "The LEN bit (0x02) … If this bit is set to 0,
the Length field is absent and the Stream Data field extends to the end of the packet."
"The FIN bit (0x01) indicates that the frame marks the end of the stream." The constructor
keeps the bits: `stream id off len fin data` with `off : Option Nat` (`none`: OFF clear) and
`len : Bool`, so the encoding of a frame is a function of the frame. DATAGRAM likewise keeps
its LEN bit (0x01, RFC 9221 §4). A frame without a length "extends to the end of the packet"
(`Frame.toEnd`), so it can only be the last frame of a payload.

**Decoding.** `decode` reads one frame at the front of the input and returns the rest.
It fails (`none`) on:

* an unknown frame type: "An endpoint MUST treat the receipt of a frame of unknown type as a
  connection error of type FRAME_ENCODING_ERROR" (§12.4);
* a truncated field or a length that runs past the input: "a frame … that was badly
  formatted" (§20.1 FRAME_ENCODING_ERROR, e.g. "an ACK frame that has more acknowledgment
  ranges than the remainder of the packet could carry");
* the field checks that the RFC assigns to FRAME_ENCODING_ERROR: an ACK range that computes a
  negative packet number (§19.3.1); a STREAM or CRYPTO frame whose offset plus length exceeds
  `2^62 - 1` (§19.6, §19.8); MAX_STREAMS or STREAMS_BLOCKED above `2^60` (§19.11, §19.14);
  an empty NEW_TOKEN token (§19.7); a NEW_CONNECTION_ID length outside `1..20` or Retire Prior
  To above the Sequence Number (§19.15).

`readFrame` reports those failures as `TransportError.frameEncodingError`. `Frame.Valid`
is the same set of conditions on a frame (and that every integer fits in 62 bits); valid
frames round trip (`Silmaril.Net.Quic.Frame.Thms`).

**Payloads.** `decodePayload` splits a whole packet payload into frames: an empty payload is
PROTOCOL_VIOLATION ("An endpoint MUST treat receipt of a packet containing no frames as a
connection error of type PROTOCOL_VIOLATION", §12.4), any undecodable frame is
FRAME_ENCODING_ERROR.

**Choices.** "A frame type MUST use the shortest possible encoding … An endpoint MAY treat the
receipt of a frame type that uses a longer encoding than necessary as a connection error of
type PROTOCOL_VIOLATION" (§12.4): `encode` always uses the one-byte type, and `decode` accepts
longer encodings of known types (the MAY is not taken). PADDING frames are kept one per byte
(each is its own frame, §19.1).

**Not checked here** (they need connection state, and belong to the layers above): which packet
types may carry which frames (Table 3 "Pkts"; `Frame.allowedIn` lists them but packets are not
modelled); stream-state errors (STREAM_STATE_ERROR for a send-only or not-yet-created local
stream; `Frame.directionError` covers the send-only / receive-only cases); stream limits
(`Acceptor`), flow control (`Silmaril.Net.Quic.Flow`), final sizes (`Silmaril.Net.Quic.Stream`);
whether DATAGRAM was negotiated through `max_datagram_frame_size` (RFC 9221 §3); the meaning
of ACK, NEW_CONNECTION_ID, RETIRE_CONNECTION_ID, NEW_TOKEN and the path frames (loss recovery,
connection IDs and migration are not modelled, see `Silmaril.Net.Quic.Service`).
-/

namespace Silmaril.Net.Quic

/-- One additional ACK Range (§19.3.1). -/
structure AckRange where
  /-- "the number of contiguous unacknowledged packets preceding the packet number one lower
  than the smallest in the preceding ACK Range" (minus one). -/
  gap : Nat
  /-- "the number of contiguous acknowledged packets preceding the largest packet number". -/
  len : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The ECN counts of an ACK frame of type 0x03 (§19.3.2). -/
structure EcnCounts where
  ect0 : Nat
  ect1 : Nat
  ce : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The frames of RFC 9000 §19 and RFC 9221 §4. -/
inductive Frame where
  /-- PADDING (0x00). -/
  | padding
  /-- PING (0x01). -/
  | ping
  /-- ACK (0x02, or 0x03 with ECN counts). -/
  | ack (largest delay firstRange : Nat) (ranges : List AckRange) (ecn : Option EcnCounts)
  /-- RESET_STREAM (0x04). -/
  | resetStream (streamId errorCode finalSize : Nat)
  /-- STOP_SENDING (0x05). -/
  | stopSending (streamId errorCode : Nat)
  /-- CRYPTO (0x06). -/
  | crypto (offset : Nat) (data : List UInt8)
  /-- NEW_TOKEN (0x07). -/
  | newToken (token : List UInt8)
  /-- STREAM (0x08–0x0f): `off = none` is the OFF bit clear (offset 0); `len` is the LEN bit. -/
  | stream (streamId : Nat) (off : Option Nat) (len fin : Bool) (data : List UInt8)
  /-- MAX_DATA (0x10). -/
  | maxData (maximum : Nat)
  /-- MAX_STREAM_DATA (0x11). -/
  | maxStreamData (streamId maximum : Nat)
  /-- MAX_STREAMS (0x12 bidirectional, 0x13 unidirectional). -/
  | maxStreams (dir : Dir) (maximum : Nat)
  /-- DATA_BLOCKED (0x14). -/
  | dataBlocked (limit : Nat)
  /-- STREAM_DATA_BLOCKED (0x15). -/
  | streamDataBlocked (streamId limit : Nat)
  /-- STREAMS_BLOCKED (0x16 bidirectional, 0x17 unidirectional). -/
  | streamsBlocked (dir : Dir) (limit : Nat)
  /-- NEW_CONNECTION_ID (0x18). -/
  | newConnectionId (seq retirePriorTo : Nat) (cid resetToken : List UInt8)
  /-- RETIRE_CONNECTION_ID (0x19). -/
  | retireConnectionId (seq : Nat)
  /-- PATH_CHALLENGE (0x1a). -/
  | pathChallenge (data : List UInt8)
  /-- PATH_RESPONSE (0x1b). -/
  | pathResponse (data : List UInt8)
  /-- CONNECTION_CLOSE (0x1c): a transport error code (§20.1) and the offending frame type. -/
  | connectionClose (errorCode frameType : Nat) (reason : List UInt8)
  /-- CONNECTION_CLOSE (0x1d): an application error code (§20.2). -/
  | applicationClose (errorCode : Nat) (reason : List UInt8)
  /-- HANDSHAKE_DONE (0x1e). -/
  | handshakeDone
  /-- DATAGRAM (RFC 9221: 0x30 without, 0x31 with the Length field). -/
  | datagram (len : Bool) (data : List UInt8)
  deriving DecidableEq, Repr, Inhabited

namespace Frame

/-! ## Field encodings -/

/-- A variable-length integer field. -/
abbrev vi (v : Nat) : List UInt8 := VarInt.encode v

/-- A length-prefixed byte field. -/
def withLen (bs : List UInt8) : List UInt8 := vi bs.length ++ bs

/-- The STREAM type for the OFF, LEN and FIN bits (§19.8). -/
def streamType (off : Option Nat) (len fin : Bool) : Nat :=
  0x08 + (if off.isSome then 0x04 else 0) + (if len then 0x02 else 0) + (if fin then 0x01 else 0)

/-- The type of a frame (Table 3; RFC 9221 §4). -/
def type : Frame → Nat
  | padding => 0x00
  | ping => 0x01
  | ack _ _ _ _ ecn => if ecn.isSome then 0x03 else 0x02
  | resetStream .. => 0x04
  | stopSending .. => 0x05
  | crypto .. => 0x06
  | newToken .. => 0x07
  | stream _ off len fin _ => streamType off len fin
  | maxData .. => 0x10
  | maxStreamData .. => 0x11
  | maxStreams d _ => if d = .bidi then 0x12 else 0x13
  | dataBlocked .. => 0x14
  | streamDataBlocked .. => 0x15
  | streamsBlocked d _ => if d = .bidi then 0x16 else 0x17
  | newConnectionId .. => 0x18
  | retireConnectionId .. => 0x19
  | pathChallenge .. => 0x1a
  | pathResponse .. => 0x1b
  | connectionClose .. => 0x1c
  | applicationClose .. => 0x1d
  | handshakeDone => 0x1e
  | datagram len _ => if len then 0x31 else 0x30

/-- The fields after the type. -/
def body : Frame → List UInt8
  | padding | ping | handshakeDone => []
  | ack l d f rs ecn =>
    vi l ++ vi d ++ vi rs.length ++ vi f ++ rs.flatMap (fun r => vi r.gap ++ vi r.len) ++
      (match ecn with | none => [] | some e => vi e.ect0 ++ vi e.ect1 ++ vi e.ce)
  | resetStream i e s => vi i ++ vi e ++ vi s
  | stopSending i e => vi i ++ vi e
  | crypto o d => vi o ++ withLen d
  | newToken t => withLen t
  | stream i off len _ d =>
    vi i ++ (match off with | none => [] | some o => vi o) ++ (if len then withLen d else d)
  | maxData m | dataBlocked m | maxStreams _ m | streamsBlocked _ m | retireConnectionId m => vi m
  | maxStreamData i m | streamDataBlocked i m => vi i ++ vi m
  | newConnectionId s r c t => vi s ++ vi r ++ [c.length.toUInt8] ++ c ++ t
  | pathChallenge d | pathResponse d => d
  | connectionClose e t r => vi e ++ vi t ++ withLen r
  | applicationClose e r => vi e ++ withLen r
  | datagram len d => if len then withLen d else d

/-- The encoding of a frame: its one-byte type, then its fields. -/
def encode (f : Frame) : List UInt8 := vi f.type ++ f.body

/-- The frame has no length and extends to the end of the packet (§19.8 LEN bit clear;
RFC 9221 §4 LEN bit clear). -/
def toEnd : Frame → Bool
  | stream _ _ len _ _ => !len
  | datagram len _ => !len
  | _ => false

/-! ## Validity -/

/-- The ACK ranges below `smallest` compute non-negative packet numbers (§19.3.1:
"largest = previous_smallest - gap - 2", "smallest = largest - ack_range"; "If any computed
packet number is negative, an endpoint MUST generate a connection error of type
FRAME_ENCODING_ERROR"). -/
def rangesOk (smallest : Nat) : List AckRange → Bool
  | [] => true
  | r :: rs => decide (r.gap + 2 + r.len ≤ smallest) && rangesOk (smallest - r.gap - 2 - r.len) rs

/-- The ACK frame's packet numbers are non-negative. -/
def ackOk (largest firstRange : Nat) (ranges : List AckRange) : Bool :=
  decide (firstRange ≤ largest) && rangesOk (largest - firstRange) ranges

/-- Every number fits in a variable-length integer. -/
def AllVarInt (vs : List Nat) : Prop := ∀ v ∈ vs, VarInt.Valid v

instance (vs : List Nat) : Decidable (AllVarInt vs) :=
  inferInstanceAs (Decidable (∀ v ∈ vs, v ≤ VarInt.maxValue))

/-- A frame that its fields can carry and that the decoder accepts. -/
def Valid : Frame → Prop
  | padding | ping | handshakeDone => True
  | ack l d f rs ecn =>
    AllVarInt ([l, d, f, rs.length] ++ rs.flatMap (fun r => [r.gap, r.len]) ++
      (match ecn with | none => [] | some e => [e.ect0, e.ect1, e.ce])) ∧ ackOk l f rs = true
  | resetStream i e s => AllVarInt [i, e, s]
  | stopSending i e => AllVarInt [i, e]
  | crypto o d => o + d.length ≤ VarInt.maxValue
  | newToken t => t ≠ [] ∧ VarInt.Valid t.length
  | stream i off _ _ d => VarInt.Valid i ∧ off.getD 0 + d.length ≤ VarInt.maxValue
  | maxData m | dataBlocked m | retireConnectionId m => VarInt.Valid m
  | maxStreams _ m | streamsBlocked _ m => m ≤ maxStreamsLimit
  | maxStreamData i m | streamDataBlocked i m => AllVarInt [i, m]
  | newConnectionId s r c t =>
    VarInt.Valid s ∧ r ≤ s ∧ 1 ≤ c.length ∧ c.length ≤ 20 ∧ t.length = 16
  | pathChallenge d | pathResponse d => d.length = 8
  | connectionClose e t r => AllVarInt [e, t, r.length]
  | applicationClose e r => AllVarInt [e, r.length]
  | datagram _ d => VarInt.Valid d.length

instance : DecidablePred Valid := fun f => by
  cases f <;> simp only [Valid] <;> infer_instance

/-! ## Decoding -/

/-- Take exactly `n` bytes. -/
def takeN (n : Nat) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ xs.length then some (xs.take n, xs.drop n) else none

/-- A length-prefixed byte field. -/
def decodeWithLen (xs : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (n, xs) ← VarInt.decode xs
  takeN n xs

/-- `n` ACK Ranges. -/
def decodeRanges : Nat → List UInt8 → Option (List AckRange × List UInt8)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
    let (g, xs) ← VarInt.decode xs
    let (l, xs) ← VarInt.decode xs
    let (rs, xs) ← decodeRanges n xs
    pure (⟨g, l⟩ :: rs, xs)

/-- The fields of an ACK frame (§19.3). -/
def decodeAck (withEcn : Bool) (xs : List UInt8) : Option (Frame × List UInt8) := do
  let (l, xs) ← VarInt.decode xs
  let (d, xs) ← VarInt.decode xs
  let (n, xs) ← VarInt.decode xs
  let (f, xs) ← VarInt.decode xs
  let (rs, xs) ← decodeRanges n xs
  let (ecn, xs) ← if withEcn then do
      let (a, xs) ← VarInt.decode xs
      let (b, xs) ← VarInt.decode xs
      let (c, xs) ← VarInt.decode xs
      pure (some ⟨a, b, c⟩, xs)
    else pure (none, xs)
  if ackOk l f rs then pure (ack l d f rs ecn, xs) else none

/-- The fields of a STREAM frame with the given OFF, LEN and FIN bits (§19.8). -/
def decodeStream (off len fin : Bool) (xs : List UInt8) : Option (Frame × List UInt8) := do
  let (i, xs) ← VarInt.decode xs
  let (o, xs) ← if off then (VarInt.decode xs).map fun (o, xs) => (some o, xs) else pure (none, xs)
  let (d, xs) ← if len then decodeWithLen xs else pure (xs, [])
  if o.getD 0 + d.length ≤ VarInt.maxValue then pure (stream i o len fin d, xs) else none

/-- The fields of a frame of type `t`; `none` for an unknown type or a malformed frame. -/
def decodeBody (t : Nat) (xs : List UInt8) : Option (Frame × List UInt8) :=
  match t with
  | 0x00 => pure (padding, xs)
  | 0x01 => pure (ping, xs)
  | 0x02 => decodeAck false xs
  | 0x03 => decodeAck true xs
  | 0x04 => do
    let (i, xs) ← VarInt.decode xs
    let (e, xs) ← VarInt.decode xs
    let (s, xs) ← VarInt.decode xs
    pure (resetStream i e s, xs)
  | 0x05 => do
    let (i, xs) ← VarInt.decode xs
    let (e, xs) ← VarInt.decode xs
    pure (stopSending i e, xs)
  | 0x06 => do
    let (o, xs) ← VarInt.decode xs
    let (d, xs) ← decodeWithLen xs
    if o + d.length ≤ VarInt.maxValue then pure (crypto o d, xs) else none
  | 0x07 => do
    let (t, xs) ← decodeWithLen xs
    if t = [] then none else pure (newToken t, xs)
  | 0x08 => decodeStream false false false xs
  | 0x09 => decodeStream false false true xs
  | 0x0a => decodeStream false true false xs
  | 0x0b => decodeStream false true true xs
  | 0x0c => decodeStream true false false xs
  | 0x0d => decodeStream true false true xs
  | 0x0e => decodeStream true true false xs
  | 0x0f => decodeStream true true true xs
  | 0x10 => (VarInt.decode xs).map fun (m, xs) => (maxData m, xs)
  | 0x11 => do
    let (i, xs) ← VarInt.decode xs
    let (m, xs) ← VarInt.decode xs
    pure (maxStreamData i m, xs)
  | 0x12 => do
    let (m, xs) ← VarInt.decode xs
    if m ≤ maxStreamsLimit then pure (maxStreams .bidi m, xs) else none
  | 0x13 => do
    let (m, xs) ← VarInt.decode xs
    if m ≤ maxStreamsLimit then pure (maxStreams .uni m, xs) else none
  | 0x14 => (VarInt.decode xs).map fun (m, xs) => (dataBlocked m, xs)
  | 0x15 => do
    let (i, xs) ← VarInt.decode xs
    let (m, xs) ← VarInt.decode xs
    pure (streamDataBlocked i m, xs)
  | 0x16 => do
    let (m, xs) ← VarInt.decode xs
    if m ≤ maxStreamsLimit then pure (streamsBlocked .bidi m, xs) else none
  | 0x17 => do
    let (m, xs) ← VarInt.decode xs
    if m ≤ maxStreamsLimit then pure (streamsBlocked .uni m, xs) else none
  | 0x18 => do
    let (s, xs) ← VarInt.decode xs
    let (r, xs) ← VarInt.decode xs
    let (n, xs) ← takeN 1 xs
    let n := (n.headD 0).toNat
    let (c, xs) ← takeN n xs
    let (t, xs) ← takeN 16 xs
    if r ≤ s ∧ 1 ≤ n ∧ n ≤ 20 then pure (newConnectionId s r c t, xs) else none
  | 0x19 => (VarInt.decode xs).map fun (s, xs) => (retireConnectionId s, xs)
  | 0x1a => (takeN 8 xs).map fun (d, xs) => (pathChallenge d, xs)
  | 0x1b => (takeN 8 xs).map fun (d, xs) => (pathResponse d, xs)
  | 0x1c => do
    let (e, xs) ← VarInt.decode xs
    let (t, xs) ← VarInt.decode xs
    let (r, xs) ← decodeWithLen xs
    pure (connectionClose e t r, xs)
  | 0x1d => do
    let (e, xs) ← VarInt.decode xs
    let (r, xs) ← decodeWithLen xs
    pure (applicationClose e r, xs)
  | 0x1e => pure (handshakeDone, xs)
  | 0x30 => pure (datagram false xs, [])
  | 0x31 => (decodeWithLen xs).map fun (d, xs) => (datagram true d, xs)
  | _ => none

/-- The frame types this model knows: `0x00`–`0x1e` (Table 3) and `0x30`–`0x31` (RFC 9221). -/
def knownType (t : Nat) : Bool := t ≤ 0x1e || t == 0x30 || t == 0x31

/-- Read one frame at the front of the input. -/
def decode (xs : List UInt8) : Option (Frame × List UInt8) := do
  let (t, xs) ← VarInt.decode xs
  decodeBody t xs

/-- Read one frame; a malformed or unknown frame is FRAME_ENCODING_ERROR (§12.4, §20.1). -/
def readFrame (xs : List UInt8) : Except TransportError (Frame × List UInt8) :=
  match decode xs with
  | some r => .ok r
  | none => .error .frameEncodingError

/-! ## Packet payloads (§12.4) -/

/-- Read frames until the input is used up. Every frame takes at least one byte, so the length
of the input is enough fuel. -/
def decodeFramesFuel : Nat → List UInt8 → Option (List Frame)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, xs@(_ :: _) =>
    match decode xs with
    | none => none
    | some (f, rest) => (decodeFramesFuel fuel rest).map (f :: ·)

/-- Split a packet payload into its frames: PROTOCOL_VIOLATION when there are none,
FRAME_ENCODING_ERROR when one does not decode (§12.4). -/
def decodePayload (xs : List UInt8) : Except TransportError (List Frame) :=
  if xs = [] then .error .protocolViolation
  else match decodeFramesFuel xs.length xs with
    | some fs => .ok fs
    | none => .error .frameEncodingError

/-- The payload of a list of frames. -/
def encodePayload (fs : List Frame) : List UInt8 := fs.flatMap encode

/-- A frame list a packet can carry: every frame valid and only the last one without a
length (a frame extending to the end of the packet must be last). -/
def PayloadOk : List Frame → Prop
  | [] => True
  | [f] => f.Valid
  | f :: g :: fs => f.Valid ∧ f.toEnd = false ∧ PayloadOk (g :: fs)

/-! ## Classification (Table 3, §3.3, §12.4) -/

/-- The packet types of Table 3's "Pkts" column. -/
inductive PacketKind where
  | initial
  | handshake
  | zeroRtt
  | oneRtt
  deriving DecidableEq, Repr

/-- Whether a frame may appear in a packet of the kind (Table 3, "Pkts"; RFC 9221 §5:
DATAGRAM "MUST be protected with either 0-RTT or 1-RTT keys"). Receiving a frame in a packet
type that is not permitted is PROTOCOL_VIOLATION (§12.4). -/
def allowedIn (k : PacketKind) : Frame → Bool
  | padding | ping => true
  | ack .. | crypto .. => k != .zeroRtt
  | connectionClose .. => true
  | newToken .. | pathResponse .. | handshakeDone => k == .oneRtt
  | _ => k == .zeroRtt || k == .oneRtt

/-- "Packets containing only frames with this marking are not ack-eliciting": ACK, PADDING
and CONNECTION_CLOSE (Table 3 "N", §1.2 "Ack-eliciting packet"). -/
def ackEliciting : Frame → Bool
  | padding | ack .. | connectionClose .. | applicationClose .. => false
  | _ => true

/-- The stream a frame is about, if any. -/
def streamId? : Frame → Option Nat
  | resetStream i .. | stopSending i .. | stream i .. | maxStreamData i .. |
    streamDataBlocked i .. => some i
  | _ => none

/-- STREAM_STATE_ERROR for a frame naming a stream in the wrong direction, as received by
endpoint `r`: STREAM, RESET_STREAM and STREAM_DATA_BLOCKED on a stream `r` cannot receive on
("for a send-only stream", §19.4, §19.8, §19.13); STOP_SENDING and MAX_STREAM_DATA on a
stream `r` cannot send on ("for a receive-only stream", §19.5, §19.10). -/
def directionError (r : Role) : Frame → Option TransportError
  | stream i .. | resetStream i .. | streamDataBlocked i .. =>
    if StreamId.canRecv r i then none else some .streamStateError
  | stopSending i .. | maxStreamData i .. =>
    if StreamId.canSend r i then none else some .streamStateError
  | _ => none

end Frame

end Silmaril.Net.Quic

module

public import Silmaril.Net.Quic.VarInt.Defs
public import Silmaril.Net.Quic.Error.Defs

@[expose] public section

/-!
# QUIC stream identifiers and stream limits (RFC 9000 §2.1, §4.6)

**Stream identifiers (§2.1).** "A stream ID is a 62-bit integer (0 to 2^62-1) that is unique
for all streams on a connection." "The least significant bit (0x01) of the stream ID
identifies the initiator of the stream. Client-initiated streams have even-numbered stream IDs
(with the bit set to 0), and server-initiated streams have odd-numbered stream IDs (with the
bit set to 1). The second least significant bit (0x02) of the stream ID distinguishes between
bidirectional streams (with the bit set to 0) and unidirectional streams (with the bit set
to 1)."

| Bits | Stream Type |
| --- | --- |
| 0x00 | Client-Initiated, Bidirectional |
| 0x01 | Server-Initiated, Bidirectional |
| 0x02 | Client-Initiated, Unidirectional |
| 0x03 | Server-Initiated, Unidirectional |

"The stream space for each type begins at the minimum value (0x00 through 0x03,
respectively); successive streams of each type are created with numerically increasing stream
IDs": `StreamId.nth t n = 4 n + t.bits` is the `n`-th stream (from 0) of type `t`, and
`StreamId.index id = id / 4` is its position. "Unidirectional streams carry data in one
direction: from the initiator of the stream to its peer": `StreamId.canSend r id` /
`canRecv r id` say whether endpoint `r` may send / receive stream data on `id`.

**Stream limits (§4.6).** "Only streams with a stream ID less than (max_streams * 4 +
first_stream_id_of_type) can be opened" (`StreamId.withinLimit`). "If a max_streams transport
parameter or a MAX_STREAMS frame is received with a value greater than 2^60 … the connection
MUST be closed … FRAME_ENCODING_ERROR if it was received in a frame" (`maxStreamsLimit`).
"MAX_STREAMS frames that do not increase the stream limit MUST be ignored."

* `Opener`: the local view of one stream type that this endpoint initiates: the peer's limit
  and the number of streams opened so far. `Opener.open` hands out `nth t opened` when the
  limit allows ("Endpoints MUST NOT exceed the limit set by their peer"), otherwise it is
  blocked (and "SHOULD send a STREAMS_BLOCKED frame"). `Opener.onMaxStreams` applies a
  MAX_STREAMS frame.
* `Acceptor`: the local view of one stream type that the peer initiates: the limit this
  endpoint advertised and how many streams the peer has opened. `Acceptor.accept id`
  rejects a stream id beyond the limit ("STREAM_LIMIT_ERROR") and otherwise opens it *and all
  lower-numbered streams of that type* ("A stream ID that is used out of order results in all
  streams of that type with lower-numbered stream IDs also being opened", §2.1;
  "Before a stream is created, all streams of the same type with lower-numbered stream IDs
  MUST be created", §3.2). `Acceptor.raise` is sending MAX_STREAMS: limits never shrink.

Not modelled here: when to send MAX_STREAMS (§4.6 leaves it to implementations), and the
transport parameters `initial_max_streams_bidi/uni` (§18.2), which are only the initial
`limit`s.
-/

namespace Silmaril.Net.Quic

/-- The two endpoints of a connection (§1.2). -/
inductive Role where
  | client
  | server
  deriving DecidableEq, Repr, Inhabited

/-- The other endpoint. -/
def Role.peer : Role → Role
  | .client => .server
  | .server => .client

/-- Stream directionality (§2.1). -/
inductive Dir where
  | bidi
  | uni
  deriving DecidableEq, Repr, Inhabited

/-- One of the four stream types of Table 1. -/
structure StreamType where
  initiator : Role
  dir : Dir
  deriving DecidableEq, Repr, Inhabited

/-- The two low bits of the stream ids of a type (Table 1). -/
def StreamType.bits (t : StreamType) : Nat :=
  (match t.initiator with | .client => 0 | .server => 1) +
    (match t.dir with | .bidi => 0 | .uni => 2)

/-- The four stream types, in the order of Table 1. -/
def StreamType.all : List StreamType :=
  [⟨.client, .bidi⟩, ⟨.server, .bidi⟩, ⟨.client, .uni⟩, ⟨.server, .uni⟩]

/-- MAX_STREAMS and `max_streams` values may not exceed `2^60` (§4.6, §19.11). -/
def maxStreamsLimit : Nat := 2 ^ 60

namespace StreamId

/-- A stream id is a 62-bit integer (§2.1). -/
def Valid (id : Nat) : Prop := id ≤ VarInt.maxValue

instance (id : Nat) : Decidable (Valid id) := inferInstanceAs (Decidable (id ≤ _))

/-- Bit `0x01`: the initiator. -/
def initiator (id : Nat) : Role := if id % 2 = 0 then .client else .server

/-- Bit `0x02`: the directionality. -/
def dir (id : Nat) : Dir := if id / 2 % 2 = 0 then .bidi else .uni

/-- The type of a stream id. -/
def type (id : Nat) : StreamType := ⟨initiator id, dir id⟩

/-- The position of a stream among the streams of its type. -/
def index (id : Nat) : Nat := id / 4

/-- The `n`-th stream (counting from 0) of type `t`. -/
def nth (t : StreamType) (n : Nat) : Nat := 4 * n + t.bits

/-- Endpoint `r` initiated the stream. -/
def isLocal (r : Role) (id : Nat) : Bool := initiator id == r

/-- Endpoint `r` may send stream data on `id`: bidirectional, or it initiated it (§2.1). -/
def canSend (r : Role) (id : Nat) : Bool := dir id == .bidi || initiator id == r

/-- Endpoint `r` may receive stream data on `id`: bidirectional, or the peer initiated it. -/
def canRecv (r : Role) (id : Nat) : Bool := dir id == .bidi || initiator id != r

/-- "Only streams with a stream ID less than (max_streams * 4 + first_stream_id_of_type) can
be opened" (§4.6). -/
def withinLimit (maxStreams id : Nat) : Bool := id < maxStreams * 4 + (type id).bits

end StreamId

/-- The streams of one type that this endpoint opens, as limited by the peer (§4.6). -/
structure Opener where
  type : StreamType
  /-- The peer's limit: the largest `max_streams` / MAX_STREAMS value received. -/
  limit : Nat
  /-- How many streams of the type were opened. -/
  opened : Nat := 0
  deriving DecidableEq, Repr

namespace Opener

/-- Open the next stream if the limit allows it; `none` means blocked (send STREAMS_BLOCKED
with `limit`, §19.14). -/
def «open» (o : Opener) : Option (Nat × Opener) :=
  if o.opened < o.limit then some (StreamId.nth o.type o.opened, { o with opened := o.opened + 1 })
  else none

/-- Receive a MAX_STREAMS frame: values above `2^60` are FRAME_ENCODING_ERROR (§19.11; the
frame decoder already rejects them); values that do not increase the limit are ignored. -/
def onMaxStreams (o : Opener) (m : Nat) : Except TransportError Opener :=
  if maxStreamsLimit < m then .error .frameEncodingError
  else .ok { o with limit := max o.limit m }

/-- The limit is respected: `opened ≤ limit`. -/
def Ok (o : Opener) : Prop := o.opened ≤ o.limit

end Opener

/-- The streams of one type that the peer opens, as limited by this endpoint (§4.6). -/
structure Acceptor where
  type : StreamType
  /-- The limit this endpoint advertised. -/
  limit : Nat
  /-- How many streams of the type are open (the peer opened `0, …, opened - 1`). -/
  opened : Nat := 0
  deriving DecidableEq, Repr

namespace Acceptor

/-- A frame from the peer names stream `id` of this type: STREAM_LIMIT_ERROR beyond the
advertised limit, otherwise `id` and every lower stream of the type are open. -/
def accept (a : Acceptor) (id : Nat) : Except TransportError Acceptor :=
  if a.limit ≤ StreamId.index id then .error .streamLimitError
  else .ok { a with opened := max a.opened (StreamId.index id + 1) }

/-- Advertise a new limit (MAX_STREAMS, §19.11): never more than `2^60`, never smaller than
before. -/
def raise (a : Acceptor) (m : Nat) : Acceptor :=
  { a with limit := max a.limit (min m maxStreamsLimit) }

/-- Stream `id` of this type is open. -/
def isOpen (a : Acceptor) (id : Nat) : Bool := StreamId.index id < a.opened

/-- The peer never opened more than allowed. -/
def Ok (a : Acceptor) : Prop := a.opened ≤ a.limit

end Acceptor

end Silmaril.Net.Quic

module

public import Silmaril.Net.Http3.Frame.Defs

@[expose] public section

/-!
# HTTP/3 Datagrams (RFC 9297 §2, §2.1) over QUIC DATAGRAM frames (RFC 9221)

"When used with HTTP/3, the Datagram Data field of QUIC DATAGRAM frames uses the following
format" (RFC 9297 §2.1):

```
HTTP/3 Datagram {
  Quarter Stream ID (i),
  HTTP Datagram Payload (..),
}
```

"Quarter Stream ID: A variable-length integer that contains the value of the client-initiated
bidirectional stream that this datagram is associated with divided by four … The largest legal
QUIC stream ID value is 2^62-1, so the largest legal value of the Quarter Stream ID field is
2^60-1. Receipt of an HTTP/3 Datagram that includes a larger value MUST be treated as an HTTP/3
connection error of type H3_DATAGRAM_ERROR (0x33)." "Receipt of a QUIC DATAGRAM frame whose
payload is too short to allow parsing the Quarter Stream ID field MUST be treated as an HTTP/3
connection error of type H3_DATAGRAM_ERROR (0x33)."

**Stream identifiers.** This module restates the two low bits of a QUIC stream ID (RFC 9000
§2.1): "The least significant bit (0x01) of the stream ID identifies the initiator of the
stream. Client-initiated streams have even-numbered stream IDs (with the bit set to 0) … The
second least significant bit (0x02) of the stream ID distinguishes between bidirectional
streams (with the bit set to 0) and unidirectional streams (with the bit set to 1)." So the
client-initiated bidirectional streams (HTTP/3 request streams) are the IDs `≡ 0 (mod 4)`
below `2^62` (`isRequestStreamId`). Stream IDs are plain `Nat`s here; this module does not
depend on the QUIC stream service.

**Modelled concretely.** The datagram format and its errors (`Datagram.encode`,
`Datagram.decode`); the `SETTINGS_H3_DATAGRAM` negotiation (§2.1.1: "QUIC DATAGRAM frames MUST
NOT be sent until the SETTINGS_H3_DATAGRAM setting has been both sent and received with a value
of 1"), its 0-RTT rule, and RFC 9221 §3's `max_datagram_frame_size` transport parameter as a
number; what a receiver does with a datagram given the state of the stream it names
(`Datagram.disposition`, §2 and §2.1).

**Assumed (abstract).** The QUIC DATAGRAM frame itself (RFC 9221 §4), its size limit and its
unreliable delivery, and the state of the request stream (supplied as a `StreamStatus`).
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Quic

/-- An HTTP/3 Datagram (RFC 9297 §2.1). -/
structure Datagram where
  quarterStreamId : Nat
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

namespace Datagram

/-- The largest QUIC stream ID, `2^62 - 1` (RFC 9000 §2.1, §16). -/
def maxStreamId : Nat := 2 ^ 62 - 1

/-- The largest legal Quarter Stream ID, `2^60 - 1` (RFC 9297 §2.1). -/
def maxQuarterStreamId : Nat := 2 ^ 60 - 1

/-- A client-initiated bidirectional stream ID (RFC 9000 §2.1: bits `0x01` and `0x02` clear),
in range: the streams that carry HTTP/3 requests (RFC 9114 §6.1). -/
def isRequestStreamId (id : Nat) : Bool := id % 4 == 0 && id ≤ maxStreamId

/-- The request stream a datagram belongs to. -/
def streamId (d : Datagram) : Nat := 4 * d.quarterStreamId

/-- The datagram for a payload on request stream `sid`. -/
def ofStream (sid : Nat) (payload : List UInt8) : Datagram := ⟨sid / 4, payload⟩

/-- A datagram a sender may produce: its Quarter Stream ID is at most `2^60 - 1`. -/
def Valid (d : Datagram) : Prop := d.quarterStreamId ≤ maxQuarterStreamId

instance (d : Datagram) : Decidable d.Valid :=
  inferInstanceAs (Decidable (d.quarterStreamId ≤ maxQuarterStreamId))

/-- The Datagram Data field of the QUIC DATAGRAM frame. -/
def encode (d : Datagram) : List UInt8 := VarInt.encode d.quarterStreamId ++ d.payload

/-- Parse the Datagram Data field of a QUIC DATAGRAM frame (§2.1): a truncated Quarter Stream
ID or one above `2^60 - 1` is a connection error of type `H3_DATAGRAM_ERROR`. -/
def decode (xs : List UInt8) : Except ErrorCode Datagram :=
  match VarInt.decode xs with
  | none => .error .datagramError
  | some (q, payload) =>
    if maxQuarterStreamId < q then .error .datagramError else .ok ⟨q, payload⟩

/-! ## Receiving (RFC 9297 §2, §2.1) -/

/-- What the receiver knows about the stream a datagram names. -/
inductive StreamStatus where
  /-- The request stream exists, its receive side is open, and its request defines semantics
  for HTTP Datagrams (for example an extended CONNECT whose upgrade token uses them). -/
  | active
  /-- The stream's receive side is closed. -/
  | receiveClosed
  /-- The stream has not been created yet (it can still be). -/
  | notYetCreated
  /-- The stream cannot be created: it is beyond the client-initiated bidirectional stream
  limit. -/
  | beyondLimit
  /-- The request has no known semantics for HTTP Datagrams (for example GET or POST). -/
  | noDatagramSemantics
  deriving DecidableEq, Repr

/-- What the receiver does with a well-formed datagram. -/
inductive Disposition where
  | deliver
  /-- "the received datagrams MUST be silently dropped" -/
  | drop
  /-- "SHALL either drop that datagram silently or buffer it temporarily (on the order of a
  round trip) while awaiting the creation of the corresponding stream" -/
  | dropOrBuffer
  /-- An HTTP/3 connection error (`SHOULD` for `H3_ID_ERROR`). -/
  | connectionError (e : ErrorCode)
  /-- "the request stream MUST be aborted with H3_DATAGRAM_ERROR (0x33)" -/
  | abortStream (e : ErrorCode)
  deriving DecidableEq, Repr

/-- The receiver's reaction to a datagram, by the state of its stream (RFC 9297 §2, §2.1). -/
def disposition : StreamStatus → Disposition
  | .active => .deliver
  | .receiveClosed => .drop
  | .notYetCreated => .dropOrBuffer
  | .beyondLimit => .connectionError .idError
  | .noDatagramSemantics => .abortStream .datagramError

end Datagram

/-! ## Negotiation (RFC 9297 §2.1.1, RFC 9221 §3) -/

/-- "QUIC DATAGRAM frames MUST NOT be sent until the SETTINGS_H3_DATAGRAM setting has been both
sent and received with a value of 1." `sent` is this endpoint's SETTINGS, `received` its
peer's (`none` while the peer's SETTINGS frame has not arrived). -/
def h3DatagramsNegotiated (sent : Settings) (received : Option Settings) : Bool :=
  sent.h3Datagram && (received.map (·.h3Datagram)).getD false

/-- QUIC datagram support announced by the `max_datagram_frame_size` transport parameter (RFC
9221 §3): "A value greater than 0 indicates that the endpoint supports the DATAGRAM frame
types". Its default is 0. -/
def quicDatagramsSupported (maxDatagramFrameSize : Nat) : Bool := 0 < maxDatagramFrameSize

/-- An endpoint may send HTTP/3 Datagrams: the setting is negotiated both ways and the peer's
transport parameter allows QUIC DATAGRAM frames (RFC 9221 §3: "An endpoint MUST NOT send
DATAGRAM frames until it has received the max_datagram_frame_size transport parameter with a
non-zero value"). -/
def maySendDatagrams (sent : Settings) (received : Option Settings)
    (peerMaxDatagramFrameSize : Nat) : Bool :=
  h3DatagramsNegotiated sent received && quicDatagramsSupported peerMaxDatagramFrameSize

/-- 0-RTT (§2.1.1): a client that stored the server's `SETTINGS_H3_DATAGRAM` "MUST validate
that the new value … is greater than or equal to the stored value; if not, the client MUST
terminate the connection with error H3_SETTINGS_ERROR". -/
def checkZeroRttH3Datagram (stored new : Bool) : Except ErrorCode Unit :=
  if stored && !new then .error .settingsError else .ok ()

end Silmaril.Net.Http3

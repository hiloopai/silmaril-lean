module

public import Silmaril.Net.Http3.Datagram.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: data stream headers and session IDs (draft-ietf-webtrans-http3-17
§4, §4.2, §4.3, §4.4, §4.5)

Codepoints are those of draft -17 (in WG Last Call, not an RFC) and may change before RFC
publication.

**Session IDs (§4).** "Session IDs are derived from the stream ID of the CONNECT stream that
established the session and therefore MUST always correspond to a client-initiated
bidirectional stream, as defined in Section 2.1 of [RFC9000]. If an endpoint receives a session
ID on a unidirectional stream, bidirectional stream, or datagram that does not correspond to a
client-initiated bidirectional stream ID, the endpoint MUST close the connection with an
H3_ID_ERROR error code." `validSessionId` is `Http3.Datagram.isRequestStreamId` (stream ID
`≡ 0 mod 4`, below `2^62`, restated from RFC 9000 §2.1 there).

**Unidirectional streams (§4.2).**

```
Unidirectional Stream {
    Stream Type (i) = 0x54,
    Session ID (i),
    User-Specified Stream Data (..)
}
```

**Bidirectional streams (§4.3).**

```
Bidirectional Stream {
    Signal Value (i) = 0x41,
    Session ID (i),
    Stream Body (..)
}
```

"This document reserves the special signal value 0x41 as a WT_STREAM frame type. … Endpoints
MUST NOT send WT_STREAM as a frame type on HTTP/3 streams other than as the very first bytes
sent by the initiator of a bidirectional stream. Receiving this frame type in any other
circumstances MUST be treated as a connection error of type H3_FRAME_UNEXPECTED."
(`checkFrameType`.)

**Resetting (§4.4).** "WebTransport implementations MUST use the RESET_STREAM_AT frame … with a
Reliable Size set to the size of the WebTransport header on that stream plus any offset
provided by the application": `reliableSize`.

**Datagrams (§4.5).** A session's datagrams are HTTP/3 Datagrams (RFC 9297 §2.1) whose Quarter
Stream ID names the CONNECT stream: `sessionDatagram`.

**Modelled concretely**: header encoding and parsing, session ID checks, the Reliable Size.
**Assumed (abstract)**: the QUIC streams themselves, RESET_STREAM_AT (draft-ietf-quic-reliable-
stream-reset) and the delivery of stream bytes.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Quic Silmaril.Net.Http3

/-- The WebTransport unidirectional stream type (§4.2, §9.4). -/
def uniStreamType : Nat := 0x54

/-- The WT_STREAM signal value opening a bidirectional WebTransport stream (§4.3, §9.3). -/
def bidiSignal : Nat := 0x41

/-- A session ID is the stream ID of a client-initiated bidirectional stream (§4). -/
def validSessionId (sid : Nat) : Bool := Datagram.isRequestStreamId sid

/-- The header of a stream: the stream type or signal value, then the session ID. -/
def encodeHeader (lead sid : Nat) : List UInt8 := VarInt.encode lead ++ VarInt.encode sid

/-- The header of a unidirectional WebTransport stream (§4.2). -/
def uniHeader (sid : Nat) : List UInt8 := encodeHeader uniStreamType sid

/-- The header of a bidirectional WebTransport stream (§4.3). -/
def bidiHeader (sid : Nat) : List UInt8 := encodeHeader bidiSignal sid

/-- Why a stream header was not read. -/
inductive HeaderError where
  /-- The stream bytes so far end inside the header. -/
  | incomplete
  /-- The leading integer is not the expected one: not a WebTransport stream (another HTTP/3
  stream type, or a request stream starting with an HTTP/3 frame), left to HTTP/3. -/
  | other (lead : Nat)
  /-- A protocol error (`H3_ID_ERROR` for a bad session ID). -/
  | protocol (e : Http3.ErrorCode)
  deriving DecidableEq, Repr

/-- Read a stream header whose leading integer should be `lead`: the session ID and the rest
of the stream. -/
def decodeHeader (lead : Nat) (xs : List UInt8) : Except HeaderError (Nat × List UInt8) :=
  match VarInt.decode xs with
  | none => .error .incomplete
  | some (t, r1) =>
    if t ≠ lead then .error (.other t)
    else
      match VarInt.decode r1 with
      | none => .error .incomplete
      | some (sid, r2) =>
        if validSessionId sid then .ok (sid, r2) else .error (.protocol .idError)

/-- Read the header of a unidirectional stream (§4.2). -/
def decodeUniHeader (xs : List UInt8) : Except HeaderError (Nat × List UInt8) :=
  decodeHeader uniStreamType xs

/-- Read the header of a bidirectional stream (§4.3). -/
def decodeBidiHeader (xs : List UInt8) : Except HeaderError (Nat × List UInt8) :=
  decodeHeader bidiSignal xs

/-- An HTTP/3 frame type met anywhere but at the very start of a bidirectional stream:
WT_STREAM there is `H3_FRAME_UNEXPECTED` (§4.3). -/
def checkFrameType (t : Nat) : Except Http3.ErrorCode Unit :=
  if t = bidiSignal then .error .frameUnexpected else .ok ()

/-- The Reliable Size of the RESET_STREAM_AT frame resetting a WebTransport stream whose header
is `header` (§4.4): the header plus the application's offset. -/
def reliableSize (header : List UInt8) (appOffset : Nat) : Nat := header.length + appOffset

/-- The HTTP/3 Datagram carrying a WebTransport datagram of session `sid` (§4.5). -/
def sessionDatagram (sid : Nat) (payload : List UInt8) : Datagram := Datagram.ofStream sid payload

end Silmaril.Net.WebTransport

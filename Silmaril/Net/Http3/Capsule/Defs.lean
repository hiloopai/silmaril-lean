module

public import Silmaril.Net.Http3.Frame.Defs
public import Silmaril.Net.Hpack.Table.Defs

@[expose] public section

/-!
# The HTTP Capsule Protocol (RFC 9297 §3)

"The Capsule Protocol is a sequence of type-length-value tuples that definitions of new HTTP
upgrade tokens can choose to use." (RFC 9297 §3) The data stream of such a request (§3.1: in
HTTP/3, "all bytes sent in DATA frames" of the request stream, after the 2xx response) is

```
Capsule Protocol {
  Capsule (..) ...,
}

Capsule {
  Capsule Type (i),
  Capsule Length (i),
  Capsule Value (..),
}
```

with QUIC variable-length integers (`Silmaril.Net.Quic.VarInt`, RFC 9000 §16). The layout is
the same as an HTTP/3 frame's (RFC 9114 §7.1), but capsules are carried *inside* the data
stream, so they get their own codec here.

**Modelled concretely.**

* `Capsule`, `Capsule.encode`, `Capsule.read maxValue`: one capsule. The reader reports
  `incomplete` when the input ends inside a capsule and `tooLarge` when the announced length
  exceeds the caller's limit, before taking the value ("If an incoming DATAGRAM Capsule has a
  length that is known to be so large as to not be usable, the implementation SHOULD discard
  the Capsule without buffering its contents into memory", §3.5). `Capsule.readAll`: a whole
  data stream. "If the receive side of a stream carrying Capsules is terminated cleanly … and
  the last Capsule on the stream was truncated, this MUST be treated as if it were a malformed
  or incomplete message" (§3.3): `readAll` reports `incomplete` then, and `malformedError` is
  the HTTP/3 reaction (RFC 9114 §4.1.2, `H3_MESSAGE_ERROR`).
* The DATAGRAM capsule (`0x00`, §3.5) and `Capsule.datagrams`, the HTTP Datagram payloads of a
  capsule sequence.
* "Endpoints that receive a Capsule with an unknown Capsule Type MUST silently drop that
  Capsule and skip over it to parse the next Capsule." (§3.2): `Capsule.known`, which keeps the
  capsules whose type the endpoint knows.
* The message rules of §3.2: no `content-length`, `content-type` or `transfer-encoding` field
  (`fieldsAllowCapsules`) and no 204, 205 or 206 status (`statusAllowsCapsules`); the Capsule
  Protocol is only in use after a 2xx or 101 response (`statusStartsDataStream`).

**Not modelled here.** The Capsule-Protocol header field (§3.4, a Structured Field), the
intermediary forwarding and re-encoding rules (§3.2, §3.5), and the HTTP/3 DATA framing of
the data stream (RFC 9114 §7.2.1; see `Silmaril.Net.Http3.Frame`).
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Quic Silmaril.Net.Hpack

/-- A capsule as it is on the wire: a type and a value (RFC 9297 §3.2). -/
structure Capsule where
  type : Nat
  value : List UInt8
  deriving DecidableEq, Repr, Inhabited

namespace Capsule

/-- The DATAGRAM capsule type (RFC 9297 §3.5). -/
def typeDatagram : Nat := 0x00

/-- The fields of a capsule fit variable-length integers. -/
def Valid (c : Capsule) : Prop := VarInt.Valid c.type ∧ VarInt.Valid c.value.length

/-- Serialize a capsule with the shortest integer encodings. -/
def encode (c : Capsule) : List UInt8 :=
  VarInt.encode c.type ++ VarInt.encode c.value.length ++ c.value

/-- Serialize a sequence of capsules (the Capsule Protocol stream format, Figure 2). -/
def encodeAll (cs : List Capsule) : List UInt8 := cs.flatMap encode

/-- Read one capsule whose value is at most `maxValue` bytes. -/
def read (maxValue : Nat) (xs : List UInt8) : Except ReadError (Capsule × List UInt8) :=
  match VarInt.decode xs with
  | none => .error .incomplete
  | some (ty, r1) =>
    match VarInt.decode r1 with
    | none => .error .incomplete
    | some (len, r2) =>
      if maxValue < len then .error .tooLarge
      else if r2.length < len then .error .incomplete
      else .ok (⟨ty, r2.take len⟩, r2.drop len)

/-- Read capsules until the input is used up (each takes at least two bytes, so the length is
enough fuel). -/
def readAllFuel (maxValue : Nat) : Nat → List UInt8 → Except ReadError (List Capsule)
  | _, [] => .ok []
  | 0, _ :: _ => .error .incomplete
  | fuel + 1, xs@(_ :: _) =>
    match read maxValue xs with
    | .error e => .error e
    | .ok (c, rest) =>
      match readAllFuel maxValue fuel rest with
      | .error e => .error e
      | .ok cs => .ok (c :: cs)

/-- The capsules of a complete data stream (one that ended cleanly). -/
def readAll (maxValue : Nat) (xs : List UInt8) : Except ReadError (List Capsule) :=
  readAllFuel maxValue xs.length xs

/-- The HTTP/3 reaction to a Capsule Protocol error: the message is malformed (RFC 9297 §3.3),
which RFC 9114 §4.1.2 answers with a stream error of type `H3_MESSAGE_ERROR`. -/
def malformedError : ErrorCode := .messageError

/-- The capsules an endpoint processes: those whose type it knows; the others are silently
dropped (RFC 9297 §3.2). -/
def known (isKnown : Nat → Bool) (cs : List Capsule) : List Capsule :=
  cs.filter fun c => isKnown c.type

/-- A DATAGRAM capsule carrying an HTTP Datagram payload (§3.5). -/
def datagram (payload : List UInt8) : Capsule := ⟨typeDatagram, payload⟩

/-- The HTTP Datagram payloads of a capsule sequence, in order (§3.5). -/
def datagrams (cs : List Capsule) : List (List UInt8) :=
  cs.filterMap fun c => if c.type = typeDatagram then some c.value else none

end Capsule

/-! ## Messages that may use the Capsule Protocol (RFC 9297 §3.2) -/

/-- "The Capsule Protocol MUST NOT be used with messages that contain Content-Length,
Content-Type, or Transfer-Encoding header fields." -/
def fieldsAllowCapsules (fs : List Entry) : Bool :=
  fs.all fun e => !([ascii "content-length", ascii "content-type",
    ascii "transfer-encoding"].contains e.name)

/-- "HTTP status codes 204 (No Content), 205 (Reset Content), and 206 (Partial Content) MUST
NOT be sent on responses that use the Capsule Protocol." -/
def statusAllowsCapsules (status : Nat) : Bool := !([204, 205, 206].contains status)

/-- "The Capsule Protocol is not in use unless the response includes a 2xx (Successful) or 101
(Switching Protocols) status code." (§3.2, by the definition of the data stream, §3.1) -/
def statusStartsDataStream (status : Nat) : Bool := (200 ≤ status && status < 300) || status == 101

end Silmaril.Net.Http3

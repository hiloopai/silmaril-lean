module

public import Silmaril.Net.Http3.Capsule.Defs
public import Silmaril.Net.WebTransport.ErrorCode.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: capsules (draft-ietf-webtrans-http3-17 §4.7, §5.4, §5.6, §6, §9.6)

Codepoints are those of draft -17 (in WG Last Call, not an RFC) and may change before RFC
publication. A WebTransport session's CONNECT stream carries the Capsule Protocol (RFC 9297
§3.2, `Silmaril.Net.Http3.Capsule`); this module gives the WebTransport capsules a typed view.

| Capsule | Type | Value |
| --- | --- | --- |
| DATAGRAM (RFC 9297 §3.5) | `0x00` | HTTP Datagram Payload |
| WT_CLOSE_SESSION (§6) | `0x2843` | Application Error Code (32), Application Error Message (..8192) |
| WT_DRAIN_SESSION (§4.7) | `0x78ae` | empty |
| WT_MAX_STREAMS (§5.6.2) | `0x190B4D3F` (bidi), `0x190B4D40` (uni) | Maximum Streams (i) |
| WT_STREAMS_BLOCKED (§5.6.3) | `0x190B4D43` (bidi), `0x190B4D44` (uni) | Maximum Streams (i) |
| WT_MAX_DATA (§5.6.4) | `0x190B4D3D` | Maximum Data (i) |
| WT_DATA_BLOCKED (§5.6.5) | `0x190B4D41` | Maximum Data (i) |

Receiving rules:

* "Each Capsule's payload MUST contain exactly the fields identified in its description"
  (RFC 9297 §3.3): otherwise the message is malformed (`CapsuleError.malformed`; in HTTP/3, a
  stream error of type `H3_MESSAGE_ERROR`).
* WT_CLOSE_SESSION: "If the Application Error Message exceeds 1024 bytes or is not valid UTF-8,
  the receiver MUST reset the stream with code H3_MESSAGE_ERROR." (§6; `validUtf8` is RFC 3629
  §4.) The message field's figure says `(..8192)` *bits*, i.e. at most 1024 bytes.
* WT_MAX_STREAMS, WT_STREAMS_BLOCKED: "This value cannot exceed 2^60 … Recipients of a capsule
  with a Maximum Streams value larger than this limit MUST close the WebTransport session with a
  WT_FLOW_CONTROL_ERROR error code." (`CapsuleError.flowControl`.)
* "The WT_MAX_STREAM_DATA and WT_STREAM_DATA_BLOCKED capsules … are not used and are prohibited.
  Endpoints MUST treat receipt of a WT_MAX_STREAM_DATA or a WT_STREAM_DATA_BLOCKED capsule as a
  session error." (§5.4; `CapsuleError.prohibited`.) Their type values, `0x190B4D3E` and
  `0x190B4D42`, are defined by draft-ietf-webtrans-http2 (§6.6, §6.9 of -16; not by draft -17).
* Every other type is unknown and silently skipped (RFC 9297 §3.2): `ofCapsule` returns `none`.

What the session does with these capsules (flow control, draining, closing) is in
`Silmaril.Net.WebTransport.Flow` and `Silmaril.Net.WebTransport.Session`.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Quic Silmaril.Net.Http3

/-! ## Capsule types (§9.6) -/

def typeCloseSession : Nat := 0x2843
def typeDrainSession : Nat := 0x78ae
def typeMaxStreamsBidi : Nat := 0x190B4D3F
def typeMaxStreamsUni : Nat := 0x190B4D40
def typeStreamsBlockedBidi : Nat := 0x190B4D43
def typeStreamsBlockedUni : Nat := 0x190B4D44
def typeMaxData : Nat := 0x190B4D3D
def typeDataBlocked : Nat := 0x190B4D41
/-- WT_MAX_STREAM_DATA (draft-ietf-webtrans-http2), prohibited over HTTP/3 (§5.4). -/
def typeMaxStreamData : Nat := 0x190B4D3E
/-- WT_STREAM_DATA_BLOCKED (draft-ietf-webtrans-http2), prohibited over HTTP/3 (§5.4). -/
def typeStreamDataBlocked : Nat := 0x190B4D42

/-- The capsule types WebTransport over HTTP/3 gives a meaning to (including the prohibited
ones). -/
def knownCapsuleTypes : List Nat :=
  [Capsule.typeDatagram, typeCloseSession, typeDrainSession, typeMaxStreamsBidi,
   typeMaxStreamsUni, typeStreamsBlockedBidi, typeStreamsBlockedUni, typeMaxData,
   typeDataBlocked, typeMaxStreamData, typeStreamDataBlocked]

/-- The largest Maximum Streams value, `2^60` (§5.6.2, §5.6.3). -/
def maxStreamsLimit : Nat := 2 ^ 60

/-- The largest Application Error Message, 1024 bytes (§6). -/
def maxCloseMessage : Nat := 1024

/-- Stream direction, for the two variants of WT_MAX_STREAMS and WT_STREAMS_BLOCKED. -/
inductive Dir where
  | bidi
  | uni
  deriving DecidableEq, Repr, Inhabited

/-! ## Helpers: 32-bit integers and UTF-8 -/

/-- A 32-bit big-endian integer (RFC 9000 §1.3 notation `(32)`). -/
def u32Bytes (n : Nat) : List UInt8 :=
  [(n / 2 ^ 24 % 256).toUInt8, (n / 2 ^ 16 % 256).toUInt8, (n / 2 ^ 8 % 256).toUInt8,
   (n % 256).toUInt8]

/-- Read a 32-bit big-endian integer. -/
def u32Read : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest =>
    some (a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat, rest)
  | _ => none

/-- A continuation byte `80–BF` (RFC 3629 §4). -/
def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- Well-formed UTF-8 (RFC 3629 §4, `UTF8-octets`): no overlong forms, no surrogates, nothing
above U+10FFFF. -/
def validUtf8 : List UInt8 → Bool
  | [] => true
  | b :: rest =>
    if b ≤ 0x7f then validUtf8 rest
    else if 0xc2 ≤ b && b ≤ 0xdf then
      match rest with
      | c :: rest' => isCont c && validUtf8 rest'
      | [] => false
    else if 0xe0 ≤ b && b ≤ 0xef then
      match rest with
      | c1 :: c2 :: rest' =>
        (if b = 0xe0 then 0xa0 ≤ c1 && c1 ≤ 0xbf
         else if b = 0xed then 0x80 ≤ c1 && c1 ≤ 0x9f else isCont c1) &&
          isCont c2 && validUtf8 rest'
      | _ => false
    else if 0xf0 ≤ b && b ≤ 0xf4 then
      match rest with
      | c1 :: c2 :: c3 :: rest' =>
        (if b = 0xf0 then 0x90 ≤ c1 && c1 ≤ 0xbf
         else if b = 0xf4 then 0x80 ≤ c1 && c1 ≤ 0x8f else isCont c1) &&
          isCont c2 && isCont c3 && validUtf8 rest'
      | _ => false
    else false

/-- A payload that is exactly one variable-length integer. -/
def oneVarInt (v : List UInt8) : Option Nat :=
  match VarInt.decode v with
  | some (n, []) => some n
  | _ => none

/-! ## Typed capsules -/

/-- A WebTransport capsule. -/
inductive WtCapsule where
  /-- DATAGRAM (RFC 9297 §3.5). -/
  | datagram (payload : List UInt8)
  /-- WT_CLOSE_SESSION (§6): a 32-bit application error code and a UTF-8 message. -/
  | closeSession (code : Nat) (message : List UInt8)
  /-- WT_DRAIN_SESSION (§4.7). -/
  | drainSession
  /-- WT_MAX_STREAMS (§5.6.2): the cumulative number of streams the peer may open. -/
  | maxStreams (dir : Dir) (n : Nat)
  /-- WT_STREAMS_BLOCKED (§5.6.3): the limit at which the sender was blocked. -/
  | streamsBlocked (dir : Dir) (n : Nat)
  /-- WT_MAX_DATA (§5.6.4): the session's data limit. -/
  | maxData (n : Nat)
  /-- WT_DATA_BLOCKED (§5.6.5): the limit at which the sender was blocked. -/
  | dataBlocked (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Why a received capsule is rejected. -/
inductive CapsuleError where
  /-- The value does not have exactly the capsule's fields, or a WT_CLOSE_SESSION message is
  too long or not UTF-8: reset the CONNECT stream with `H3_MESSAGE_ERROR`. -/
  | malformed
  /-- A Maximum Streams value above `2^60`: close the session with `WT_FLOW_CONTROL_ERROR`. -/
  | flowControl
  /-- WT_MAX_STREAM_DATA or WT_STREAM_DATA_BLOCKED: a session error (§5.4). -/
  | prohibited
  deriving DecidableEq, Repr

namespace WtCapsule

def maxStreamsType : Dir → Nat
  | .bidi => typeMaxStreamsBidi
  | .uni => typeMaxStreamsUni

def streamsBlockedType : Dir → Nat
  | .bidi => typeStreamsBlockedBidi
  | .uni => typeStreamsBlockedUni

/-- The raw capsule. -/
def toCapsule : WtCapsule → Capsule
  | .datagram p => ⟨Capsule.typeDatagram, p⟩
  | .closeSession code msg => ⟨typeCloseSession, u32Bytes code ++ msg⟩
  | .drainSession => ⟨typeDrainSession, []⟩
  | .maxStreams d n => ⟨maxStreamsType d, VarInt.encode n⟩
  | .streamsBlocked d n => ⟨streamsBlockedType d, VarInt.encode n⟩
  | .maxData n => ⟨typeMaxData, VarInt.encode n⟩
  | .dataBlocked n => ⟨typeDataBlocked, VarInt.encode n⟩

/-- What a sender may put in a capsule. -/
def Valid : WtCapsule → Prop
  | .datagram p => VarInt.Valid p.length
  | .closeSession code msg => AppCode code ∧ msg.length ≤ maxCloseMessage ∧ validUtf8 msg = true
  | .drainSession => True
  | .maxStreams _ n | .streamsBlocked _ n => n ≤ maxStreamsLimit
  | .maxData n | .dataBlocked n => VarInt.Valid n

/-- A Maximum Streams value: one integer, at most `2^60`. -/
def streamCount (v : List UInt8) (k : Nat → WtCapsule) : Except CapsuleError (Option WtCapsule) :=
  match oneVarInt v with
  | none => .error .malformed
  | some n => if maxStreamsLimit < n then .error .flowControl else .ok (some (k n))

/-- A Maximum Data value: one integer. -/
def dataCount (v : List UInt8) (k : Nat → WtCapsule) : Except CapsuleError (Option WtCapsule) :=
  match oneVarInt v with
  | none => .error .malformed
  | some n => .ok (some (k n))

/-- The typed view of a received capsule; `none` for a type WebTransport does not know, which
is skipped (RFC 9297 §3.2). -/
def ofCapsule (c : Capsule) : Except CapsuleError (Option WtCapsule) :=
  if c.type = Capsule.typeDatagram then .ok (some (.datagram c.value))
  else if c.type = typeCloseSession then
    match u32Read c.value with
    | none => .error .malformed
    | some (code, msg) =>
      if msg.length ≤ maxCloseMessage && validUtf8 msg then .ok (some (.closeSession code msg))
      else .error .malformed
  else if c.type = typeDrainSession then
    if c.value.isEmpty then .ok (some .drainSession) else .error .malformed
  else if c.type = typeMaxStreamsBidi then streamCount c.value (.maxStreams .bidi)
  else if c.type = typeMaxStreamsUni then streamCount c.value (.maxStreams .uni)
  else if c.type = typeStreamsBlockedBidi then streamCount c.value (.streamsBlocked .bidi)
  else if c.type = typeStreamsBlockedUni then streamCount c.value (.streamsBlocked .uni)
  else if c.type = typeMaxData then dataCount c.value .maxData
  else if c.type = typeDataBlocked then dataCount c.value .dataBlocked
  else if c.type = typeMaxStreamData || c.type = typeStreamDataBlocked then .error .prohibited
  else .ok none

/-- Serialize. -/
def encode (w : WtCapsule) : List UInt8 := w.toCapsule.encode

/-- Errors reading a WebTransport capsule from the CONNECT stream. -/
inductive DecodeError where
  | read (e : ReadError)
  | capsule (e : CapsuleError)
  deriving DecidableEq, Repr

/-- Read one capsule (value at most `maxValue` bytes) and interpret it. -/
def decode (maxValue : Nat) (xs : List UInt8) :
    Except DecodeError (Option WtCapsule × List UInt8) :=
  match Capsule.read maxValue xs with
  | .error e => .error (.read e)
  | .ok (c, rest) =>
    match ofCapsule c with
    | .error e => .error (.capsule e)
    | .ok w => .ok (w, rest)

/-- "Cleanly terminating a CONNECT stream without a WT_CLOSE_SESSION capsule SHALL be
semantically equivalent to terminating it with a WT_CLOSE_SESSION capsule that has an error
code of 0 and an empty error string." (§6) -/
def closeOfFin : WtCapsule := .closeSession 0 []

end WtCapsule

end Silmaril.Net.WebTransport

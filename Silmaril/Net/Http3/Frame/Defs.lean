module

public import Silmaril.Net.Quic.VarInt.Defs

@[expose] public section

/-!
# HTTP/3 frames, settings and error codes (RFC 9114 §7, §8.1)

**Frame layout (§7.1).** Every HTTP/3 frame is

```
HTTP/3 Frame Format {
  Type (i),
  Length (i),
  Frame Payload (..),
}
```

with `Type` and `Length` QUIC variable-length integers (`Silmaril.Net.Quic.VarInt`).
`RawFrame`, `encodeRaw` and `readRaw` are this layer. Unlike HTTP/2 there is no stream
identifier: the frame belongs to the QUIC stream that carries it (§6). `readRaw maxPayload`
refuses a frame whose announced length exceeds the caller's buffering limit before taking the
payload (§10.5: an endpoint may bound what it buffers), and reports `incomplete` when the
input ends inside a frame (§7.1: a truncated last frame on a cleanly closed stream is an
`H3_FRAME_ERROR`; the caller decides, since it knows whether the stream ended).

**Frame payloads (§7.2).** `Frame` is the typed view: DATA (`0x00`), HEADERS (`0x01`),
CANCEL_PUSH (`0x03`), SETTINGS (`0x04`), PUSH_PROMISE (`0x05`), GOAWAY (`0x07`),
MAX_PUSH_ID (`0x0d`); the frame types HTTP/2 used without an HTTP/3 counterpart (`0x02`,
`0x06`, `0x08`, `0x09`), whose receipt is `H3_FRAME_UNEXPECTED` (§7.2.8); and every other
type, which is kept as `unknown` and ignored (§9) — this includes the reserved "grease"
types `0x1f * N + 0x21` (§7.2.8) and extension frames. "Each frame's payload MUST contain
exactly the fields identified in its description … MUST be treated as a connection error of
type H3_FRAME_ERROR" (§7.1): `Frame.ofRaw` checks it. The field sections inside HEADERS and
PUSH_PROMISE stay encoded here; QPACK (`Silmaril.Net.Qpack`) decodes them.

**SETTINGS (§7.2.4).** A list of `(identifier, value)` pairs of variable-length integers.
`Frame.ofRaw` rejects, with `H3_SETTINGS_ERROR`, the HTTP/2 identifiers reserved by §7.2.4.1 /
§11.2.2 (`0x00`, `0x02`–`0x05`) and duplicate identifiers ("A receiver MAY treat the presence
of duplicate setting identifiers as a connection error of type H3_SETTINGS_ERROR": this
model takes that option). `Settings` interprets the identifiers this library knows:
`SETTINGS_MAX_FIELD_SECTION_SIZE` (`0x06`, RFC 9114), `SETTINGS_QPACK_MAX_TABLE_CAPACITY`
(`0x01`) and `SETTINGS_QPACK_BLOCKED_STREAMS` (`0x07`, RFC 9204 §5),
`SETTINGS_ENABLE_CONNECT_PROTOCOL` (`0x08`, RFC 9220 §3) and `SETTINGS_H3_DATAGRAM` (`0x33`,
RFC 9297 §2.1.1); the last two are booleans whose other values are `H3_SETTINGS_ERROR`.
Unknown identifiers are ignored, as §7.2.4 requires. WebTransport's settings are interpreted by
`Silmaril.Net.WebTransport` from the same raw list.

**Error codes (§8.1).** `ErrorCode` is `0x0100`–`0x0110` plus `H3_DATAGRAM_ERROR` (`0x33`,
RFC 9297 §5.2); QPACK's are in `Silmaril.Net.Qpack`. "receipt of an unknown error code MUST
be treated as equivalent to H3_NO_ERROR" (§8): `ErrorCode.interpret`.
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Quic

/-! ## Error codes (§8.1) -/

/-- The HTTP/3 error codes of RFC 9114 §8.1, and `H3_DATAGRAM_ERROR` of RFC 9297 §5.2. -/
inductive ErrorCode where
  | noError | generalProtocolError | internalError | streamCreationError
  | closedCriticalStream | frameUnexpected | frameError | excessiveLoad | idError
  | settingsError | missingSettings | requestRejected | requestCancelled
  | requestIncomplete | messageError | connectError | versionFallback
  | datagramError
  deriving DecidableEq, Repr, Inhabited

namespace ErrorCode

def code : ErrorCode → Nat
  | noError => 0x0100 | generalProtocolError => 0x0101 | internalError => 0x0102
  | streamCreationError => 0x0103 | closedCriticalStream => 0x0104
  | frameUnexpected => 0x0105 | frameError => 0x0106 | excessiveLoad => 0x0107
  | idError => 0x0108 | settingsError => 0x0109 | missingSettings => 0x010a
  | requestRejected => 0x010b | requestCancelled => 0x010c | requestIncomplete => 0x010d
  | messageError => 0x010e | connectError => 0x010f | versionFallback => 0x0110
  | datagramError => 0x33

def all : List ErrorCode :=
  [noError, generalProtocolError, internalError, streamCreationError, closedCriticalStream,
   frameUnexpected, frameError, excessiveLoad, idError, settingsError, missingSettings,
   requestRejected, requestCancelled, requestIncomplete, messageError, connectError,
   versionFallback, datagramError]

/-- The error of a code, `none` for codes this library does not know. -/
def ofCode (n : Nat) : Option ErrorCode := all.find? (·.code == n)

/-- What a received error code means (§8): unknown codes are `H3_NO_ERROR`. -/
def interpret (n : Nat) : ErrorCode := (ofCode n).getD noError

end ErrorCode

/-- The reserved ("grease") code points `0x1f * N + 0x21` of frame types (§7.2.8), stream
types (§6.2.3), settings (§7.2.4.1) and error codes (§8.1). -/
def isGrease (n : Nat) : Bool := 0x21 ≤ n && (n - 0x21) % 0x1f == 0

/-- The `N`-th grease code point. -/
def grease (n : Nat) : Nat := 0x1f * n + 0x21

/-! ## Raw frames (§7.1) -/

/-- A frame as it is on the wire: a type and a payload. -/
structure RawFrame where
  type : Nat
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- The frame fields fit variable-length integers. -/
def RawFrame.Valid (f : RawFrame) : Prop :=
  VarInt.Valid f.type ∧ VarInt.Valid f.payload.length

/-- Serialize a frame with the shortest integer encodings. -/
def encodeRaw (f : RawFrame) : List UInt8 :=
  VarInt.encode f.type ++ VarInt.encode f.payload.length ++ f.payload

/-- What a frame reader reports. -/
inductive ReadError where
  /-- The input ends inside the frame (wait for more, or `H3_FRAME_ERROR` at a clean end). -/
  | incomplete
  /-- The announced length exceeds the reader's buffering limit. -/
  | tooLarge
  deriving DecidableEq, Repr

/-- Read one frame whose payload is at most `maxPayload` bytes. -/
def readRaw (maxPayload : Nat) (xs : List UInt8) : Except ReadError (RawFrame × List UInt8) :=
  match VarInt.decode xs with
  | none => .error .incomplete
  | some (ty, r1) =>
    match VarInt.decode r1 with
    | none => .error .incomplete
    | some (len, r2) =>
      if maxPayload < len then .error .tooLarge
      else if r2.length < len then .error .incomplete
      else .ok (⟨ty, r2.take len⟩, r2.drop len)

/-- Read frames until the input is used up; `incomplete` if it ends inside a frame. -/
def readRawAllFuel (maxPayload : Nat) : Nat → List UInt8 → Except ReadError (List RawFrame)
  | _, [] => .ok []
  | 0, _ :: _ => .error .incomplete
  | fuel + 1, xs@(_ :: _) =>
    match readRaw maxPayload xs with
    | .error e => .error e
    | .ok (f, rest) =>
      match readRawAllFuel maxPayload fuel rest with
      | .error e => .error e
      | .ok fs => .ok (f :: fs)

/-- All frames of a byte string (a frame takes at least two bytes, so the length is fuel). -/
def readRawAll (maxPayload : Nat) (xs : List UInt8) : Except ReadError (List RawFrame) :=
  readRawAllFuel maxPayload xs.length xs

/-! ## Frame types (§7.2, §11.2.1) -/

def typeData : Nat := 0x00
def typeHeaders : Nat := 0x01
def typeCancelPush : Nat := 0x03
def typeSettings : Nat := 0x04
def typePushPromise : Nat := 0x05
def typeGoaway : Nat := 0x07
def typeMaxPushId : Nat := 0x0d

/-- The HTTP/2 frame types without an HTTP/3 counterpart (PRIORITY, PING, WINDOW_UPDATE,
CONTINUATION): their receipt is `H3_FRAME_UNEXPECTED` (§7.2.8, §11.2.1). -/
def h2ReservedTypes : List Nat := [0x02, 0x06, 0x08, 0x09]

/-- The frame types this module gives a meaning to. -/
def knownTypes : List Nat :=
  [typeData, typeHeaders, typeCancelPush, typeSettings, typePushPromise, typeGoaway,
   typeMaxPushId] ++ h2ReservedTypes

/-- A typed HTTP/3 frame. -/
inductive Frame where
  | data (bytes : List UInt8)
  /-- An encoded (QPACK) field section. -/
  | headers (fieldSection : List UInt8)
  | cancelPush (pushId : Nat)
  /-- Setting identifiers and values, in order. -/
  | settings (params : List (Nat × Nat))
  | pushPromise (pushId : Nat) (fieldSection : List UInt8)
  /-- A stream ID (server to client) or push ID (client to server). -/
  | goaway (id : Nat)
  | maxPushId (pushId : Nat)
  /-- A frame type reserved from HTTP/2 (§7.2.8): `H3_FRAME_UNEXPECTED` on receipt. -/
  | h2Reserved (type : Nat) (payload : List UInt8)
  /-- Any other type: extension or grease, ignored by this layer (§9). -/
  | unknown (type : Nat) (payload : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-! ## SETTINGS (§7.2.4) -/

/-- Setting identifiers reserved from HTTP/2 (§7.2.4.1, §11.2.2): `H3_SETTINGS_ERROR`. -/
def h2ReservedSettings : List Nat := [0x00, 0x02, 0x03, 0x04, 0x05]

def settingQpackMaxTableCapacity : Nat := 0x01
def settingMaxFieldSectionSize : Nat := 0x06
def settingQpackBlockedStreams : Nat := 0x07
def settingEnableConnectProtocol : Nat := 0x08
def settingH3Datagram : Nat := 0x33

/-- The flat varint list of a SETTINGS payload. -/
def flattenParams : List (Nat × Nat) → List Nat
  | [] => []
  | (i, v) :: ps => i :: v :: flattenParams ps

/-- Pair up a flat varint list; `none` for an odd count (a truncated parameter). -/
def pairUp : List Nat → Option (List (Nat × Nat))
  | [] => some []
  | [_] => none
  | i :: v :: rest => (pairUp rest).map ((i, v) :: ·)

/-- The SETTINGS payload. -/
def encodeParams (ps : List (Nat × Nat)) : List UInt8 := (flattenParams ps).flatMap VarInt.encode

/-- A SETTINGS parameter list this model accepts: valid integers, no HTTP/2-reserved
identifier, no duplicate identifier. -/
def paramsOk (ps : List (Nat × Nat)) : Bool :=
  ps.all (fun p => !h2ReservedSettings.contains p.1) && (ps.map Prod.fst).Nodup

/-- Decode a SETTINGS payload (§7.2.4). -/
def decodeParams (payload : List UInt8) : Except ErrorCode (List (Nat × Nat)) :=
  match VarInt.decodeAll payload with
  | none => .error .frameError
  | some vs =>
    match pairUp vs with
    | none => .error .frameError
    | some ps => if paramsOk ps then .ok ps else .error .settingsError

/-! ## Typed frames ↔ raw frames -/

/-- A payload that is exactly one variable-length integer. -/
def decodeOneVarInt (payload : List UInt8) : Except ErrorCode Nat :=
  match VarInt.decode payload with
  | some (v, []) => .ok v
  | _ => .error .frameError

/-- The raw frame of a typed frame. -/
def Frame.toRaw : Frame → RawFrame
  | .data b => ⟨typeData, b⟩
  | .headers s => ⟨typeHeaders, s⟩
  | .cancelPush p => ⟨typeCancelPush, VarInt.encode p⟩
  | .settings ps => ⟨typeSettings, encodeParams ps⟩
  | .pushPromise p s => ⟨typePushPromise, VarInt.encode p ++ s⟩
  | .goaway i => ⟨typeGoaway, VarInt.encode i⟩
  | .maxPushId p => ⟨typeMaxPushId, VarInt.encode p⟩
  | .h2Reserved t b => ⟨t, b⟩
  | .unknown t b => ⟨t, b⟩

/-- The typed frame of a raw frame, checking each payload layout (§7.1, §7.2). -/
def Frame.ofRaw (f : RawFrame) : Except ErrorCode Frame :=
  if f.type = typeData then .ok (.data f.payload)
  else if f.type = typeHeaders then .ok (.headers f.payload)
  else if f.type = typeCancelPush then (decodeOneVarInt f.payload).map .cancelPush
  else if f.type = typeSettings then (decodeParams f.payload).map .settings
  else if f.type = typePushPromise then
    match VarInt.decode f.payload with
    | none => .error .frameError
    | some (p, s) => .ok (.pushPromise p s)
  else if f.type = typeGoaway then (decodeOneVarInt f.payload).map .goaway
  else if f.type = typeMaxPushId then (decodeOneVarInt f.payload).map .maxPushId
  else if h2ReservedTypes.contains f.type then .ok (.h2Reserved f.type f.payload)
  else .ok (.unknown f.type f.payload)

/-- A frame that serializes and reads back as itself: integers in range, settings accepted,
and the type of an `h2Reserved`/`unknown` frame in its class. -/
def Frame.Valid : Frame → Prop
  | .data b | .headers b => VarInt.Valid b.length
  | .cancelPush p | .goaway p | .maxPushId p => VarInt.Valid p
  | .settings ps =>
    (∀ p ∈ ps, VarInt.Valid p.1 ∧ VarInt.Valid p.2) ∧ paramsOk ps = true ∧
      VarInt.Valid (encodeParams ps).length
  | .pushPromise p s => VarInt.Valid p ∧ VarInt.Valid (VarInt.encode p ++ s).length
  | .h2Reserved t b => t ∈ h2ReservedTypes ∧ VarInt.Valid b.length
  | .unknown t b => t ∉ knownTypes ∧ VarInt.Valid t ∧ VarInt.Valid b.length

/-- Serialize a typed frame. -/
def Frame.encode (f : Frame) : List UInt8 := encodeRaw f.toRaw

/-- Errors of the typed reader: a read error or a payload error. -/
inductive DecodeError where
  | read (e : ReadError)
  | protocol (e : ErrorCode)
  deriving DecidableEq, Repr

/-- Read one typed frame. -/
def decodeFrame (maxPayload : Nat) (xs : List UInt8) : Except DecodeError (Frame × List UInt8) :=
  match readRaw maxPayload xs with
  | .error e => .error (.read e)
  | .ok (r, rest) =>
    match Frame.ofRaw r with
    | .error e => .error (.protocol e)
    | .ok f => .ok (f, rest)

/-! ## Interpreted settings (§7.2.4.1, RFC 9204 §5, RFC 9220 §3, RFC 9297 §2.1.1) -/

/-- The settings this library interprets, with their defaults. -/
structure Settings where
  /-- `SETTINGS_QPACK_MAX_TABLE_CAPACITY`, default 0. -/
  qpackMaxTableCapacity : Nat := 0
  /-- `SETTINGS_MAX_FIELD_SECTION_SIZE`, default unlimited (`none`). -/
  maxFieldSectionSize : Option Nat := none
  /-- `SETTINGS_QPACK_BLOCKED_STREAMS`, default 0. -/
  qpackBlockedStreams : Nat := 0
  /-- `SETTINGS_ENABLE_CONNECT_PROTOCOL` (RFC 9220), default off. -/
  enableConnectProtocol : Bool := false
  /-- `SETTINGS_H3_DATAGRAM` (RFC 9297), default off. -/
  h3Datagram : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A boolean setting: 0 or 1, anything else `H3_SETTINGS_ERROR`. -/
def boolSetting (v : Nat) : Except ErrorCode Bool :=
  if v = 0 then .ok false else if v = 1 then .ok true else .error .settingsError

/-- Apply one parameter; unknown identifiers (and grease) are ignored (§7.2.4). -/
def Settings.apply (s : Settings) (p : Nat × Nat) : Except ErrorCode Settings :=
  let (i, v) := p
  if i = settingQpackMaxTableCapacity then .ok { s with qpackMaxTableCapacity := v }
  else if i = settingMaxFieldSectionSize then .ok { s with maxFieldSectionSize := some v }
  else if i = settingQpackBlockedStreams then .ok { s with qpackBlockedStreams := v }
  else if i = settingEnableConnectProtocol then
    (boolSetting v).map fun b => { s with enableConnectProtocol := b }
  else if i = settingH3Datagram then (boolSetting v).map fun b => { s with h3Datagram := b }
  else .ok s

/-- The settings a peer's SETTINGS parameters announce, starting from the defaults. -/
def Settings.ofParams (ps : List (Nat × Nat)) : Except ErrorCode Settings :=
  ps.foldlM Settings.apply {}

/-- The value of a raw setting identifier, if present. -/
def lookupParam (ps : List (Nat × Nat)) (i : Nat) : Option Nat := (ps.find? (·.1 == i)).map (·.2)

end Silmaril.Net.Http3

module

@[expose] public section

/-!
# HTTP/2 frames (RFC 9113 §4, §6, §7)

**Frame header (§4.1).** Every frame starts with a fixed 9-octet header:

```
HTTP Frame {
  Length (24),
  Type (8),
  Flags (8),
  Reserved (1),
  Stream Identifier (31),
  Frame Payload (..),
}
```

`encodeHeader`/`decodeHeader` are that layout (big-endian, §1.2 / RFC 9113 "all numeric
values are in network byte order"). The reserved bit "MUST remain unset (0x0) when sending
and MUST be ignored when receiving" (§4.1): `decodeHeader` masks it off.

**Frame size (§4.2).** "An endpoint MUST send an error code of FRAME_SIZE_ERROR if a frame
exceeds the size defined in SETTINGS_MAX_FRAME_SIZE"; `readFrame maxFrameSize` checks it
before taking the payload.

**Types and errors.** The frame types of §6 (`FrameType`, codes `0x00`–`0x09`) and the error
codes of §7 (`ErrorCode`, `0x00`–`0x0d`). "Implementations MUST ignore and discard frames of
unknown types" (§4.1, §5.5): `FrameType.ofCode` returns `none` for them and the caller skips
the frame. Unknown error codes "MUST NOT trigger any special behavior" (§7): `ErrorCode.ofCode`
maps them to `none`, which callers may treat as `INTERNAL_ERROR`.

**Connection preface (§3.4).** The client preface starts with the 24 octets
`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`.

Payload layouts of the individual frame types (§6.1–§6.10: padding, priority fields, the
SETTINGS list, GOAWAY's last stream id, …) are future work, except SETTINGS parameters,
which are in `Silmaril.Net.Http2.Settings`.
-/

namespace Silmaril.Net.Http2

/-- A frame header (§4.1). -/
structure FrameHeader where
  /-- Payload length, a 24-bit unsigned integer. -/
  length : Nat
  /-- Frame type code (8 bits). -/
  type : Nat
  /-- Flags (8 bits). -/
  flags : Nat
  /-- Stream identifier, a 31-bit unsigned integer; 0 for the connection. -/
  streamId : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The fields fit their widths. -/
def FrameHeader.Valid (h : FrameHeader) : Prop :=
  h.length < 2 ^ 24 ∧ h.type < 2 ^ 8 ∧ h.flags < 2 ^ 8 ∧ h.streamId < 2 ^ 31

instance (h : FrameHeader) : Decidable h.Valid := by unfold FrameHeader.Valid; infer_instance

/-- Big-endian octets of `x` in `k` octets. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, x => (x / 256 ^ k % 256).toUInt8 :: beBytes k x

/-- The big-endian value of octets. -/
def beValue (xs : List UInt8) : Nat := xs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The 9-octet header (§4.1), reserved bit unset. -/
def encodeHeader (h : FrameHeader) : List UInt8 :=
  beBytes 3 h.length ++ [h.type.toUInt8, h.flags.toUInt8] ++ beBytes 4 h.streamId

/-- Read a frame header (§4.1), ignoring the reserved bit. -/
def decodeHeader (xs : List UInt8) : Option (FrameHeader × List UInt8) :=
  if xs.length < 9 then none
  else
    let len := beValue (xs.take 3)
    let ty := (xs.drop 3).headD 0
    let fl := (xs.drop 4).headD 0
    let sid := beValue ((xs.drop 5).take 4) % 2 ^ 31
    some (⟨len, ty.toNat, fl.toNat, sid⟩, xs.drop 9)

/-- A frame: header and payload. -/
structure Frame where
  header : FrameHeader
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- The frame errors a reader detects. -/
inductive ReadError where
  /-- Fewer octets than the header announces (wait for more input). -/
  | incomplete
  /-- The length exceeds `SETTINGS_MAX_FRAME_SIZE` (§4.2): `FRAME_SIZE_ERROR`. -/
  | frameSize
  deriving DecidableEq, Repr

/-- Read a frame whose length is at most `maxFrameSize` (§4.2). -/
def readFrame (maxFrameSize : Nat) (xs : List UInt8) : Except ReadError (Frame × List UInt8) :=
  match decodeHeader xs with
  | none => .error .incomplete
  | some (h, rest) =>
    if maxFrameSize < h.length then .error .frameSize
    else if rest.length < h.length then .error .incomplete
    else .ok (⟨h, rest.take h.length⟩, rest.drop h.length)

/-- Serialize a frame. -/
def encodeFrame (f : Frame) : List UInt8 := encodeHeader f.header ++ f.payload

/-- A frame whose header length is its payload length and whose header fits. -/
def Frame.Valid (f : Frame) : Prop := f.header.Valid ∧ f.header.length = f.payload.length

/-! ## Frame types (§6) and error codes (§7) -/

/-- The frame types of RFC 9113 (§6, §11.2). -/
inductive FrameType where
  | data | headers | priority | rstStream | settings | pushPromise | ping | goaway
  | windowUpdate | continuation
  deriving DecidableEq, Repr, Inhabited

namespace FrameType

def code : FrameType → Nat
  | data => 0x0 | headers => 0x1 | priority => 0x2 | rstStream => 0x3 | settings => 0x4
  | pushPromise => 0x5 | ping => 0x6 | goaway => 0x7 | windowUpdate => 0x8
  | continuation => 0x9

def all : List FrameType :=
  [data, headers, priority, rstStream, settings, pushPromise, ping, goaway, windowUpdate,
   continuation]

/-- The type of a code; `none` for an unknown type, which is ignored (§5.5). -/
def ofCode (n : Nat) : Option FrameType := all.find? (·.code == n)

/-- Frames that MUST be sent on a stream: stream identifier 0 is a connection error of type
`PROTOCOL_ERROR` (§6.1, §6.2, §6.3, §6.4, §6.6, §6.10). WINDOW_UPDATE may be sent on either
(§6.9). -/
def streamOnly : FrameType → Bool
  | data | headers | priority | rstStream | pushPromise | continuation => true
  | settings | ping | goaway | windowUpdate => false

/-- Frames whose stream identifier MUST be 0 (§6.5, §6.7, §6.8). -/
def connectionOnly : FrameType → Bool
  | settings | ping | goaway => true
  | _ => false

end FrameType

/-- Flags (§6). -/
def flagEndStream : Nat := 0x1
def flagAck : Nat := 0x1
def flagEndHeaders : Nat := 0x4
def flagPadded : Nat := 0x8
def flagPriority : Nat := 0x20

/-- Whether bit `f` is set in `flags`. -/
def hasFlag (flags f : Nat) : Bool := flags / f % 2 == 1

/-- The error codes of §7. -/
inductive ErrorCode where
  | noError | protocolError | internalError | flowControlError | settingsTimeout
  | streamClosed | frameSizeError | refusedStream | cancel | compressionError | connectError
  | enhanceYourCalm | inadequateSecurity | http11Required
  deriving DecidableEq, Repr, Inhabited

namespace ErrorCode

def code : ErrorCode → Nat
  | noError => 0x0 | protocolError => 0x1 | internalError => 0x2 | flowControlError => 0x3
  | settingsTimeout => 0x4 | streamClosed => 0x5 | frameSizeError => 0x6
  | refusedStream => 0x7 | cancel => 0x8 | compressionError => 0x9 | connectError => 0xa
  | enhanceYourCalm => 0xb | inadequateSecurity => 0xc | http11Required => 0xd

def all : List ErrorCode :=
  [noError, protocolError, internalError, flowControlError, settingsTimeout, streamClosed,
   frameSizeError, refusedStream, cancel, compressionError, connectError, enhanceYourCalm,
   inadequateSecurity, http11Required]

/-- The error of a code; `none` for an unknown code (§7: no special behaviour). -/
def ofCode (n : Nat) : Option ErrorCode := all.find? (·.code == n)

end ErrorCode

/-- The client connection preface (§3.4): `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`. -/
def clientPreface : List UInt8 :=
  "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".toList.map (fun c => c.toNat.toUInt8)

end Silmaril.Net.Http2

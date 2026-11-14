module

public import Silmaril.Net.Http3.Frame.Defs

@[expose] public section

/-!
# HTTP/3 streams: stream types, the control stream and request streams (RFC 9114 §4.1, §6)

HTTP/3 runs over QUIC streams (§6). This module models what HTTP/3 does with the bytes of
each stream once QUIC has delivered them in order; QUIC itself is an assumption here (the
reliable, ordered per-stream byte service of RFC 9000 §2, see `Silmaril.Net.Quic` and
`docs/projects/http3.md`). Each machine reads *typed frames* (`Frame`), so the byte level is
`readRawAll` + `Frame.ofRaw` (`decodeFrames`).

**Stream identifiers (§6.1, RFC 9000 §2.1).** The two low bits of a QUIC stream ID say who
opened it and whether it is bidirectional. Client-initiated bidirectional streams (`id % 4 =
0`) are request streams; a client receiving a server-initiated bidirectional stream treats it
as `H3_STREAM_CREATION_ERROR` (no extension negotiated).

**Unidirectional streams (§6.2).** They start with a stream type: control (`0x00`), push
(`0x01`, followed by a push ID), QPACK encoder (`0x02`) and decoder (`0x03`) (RFC 9204 §4.2).
Every other type (extensions such as WebTransport's `0x54`, and grease types) is `unknown`:
"Recipients of unknown stream types MUST either abort reading of the stream or discard
incoming data without further processing … MUST NOT consider unknown stream types to be a
connection error of any kind". `UniStreams.open_` tracks the critical streams a peer has
opened: a second control, QPACK encoder or QPACK decoder stream is
`H3_STREAM_CREATION_ERROR` (§6.2.1, RFC 9204 §4.2), so is a push stream opened by a client
(§6.2.2), and a reused push ID is `H3_ID_ERROR` (§6.2.2).

**Control stream (§6.2.1, §7.2).** `controlStep` reads the peer's control stream:

* the first frame is SETTINGS, otherwise `H3_MISSING_SETTINGS`;
* a second SETTINGS is `H3_FRAME_UNEXPECTED` (§7.2.4);
* DATA, HEADERS, PUSH_PROMISE and HTTP/2-reserved frames are `H3_FRAME_UNEXPECTED`
  (§7.2.1, §7.2.2, §7.2.5, §7.2.8);
* GOAWAY from a server carries a client-initiated bidirectional stream ID, otherwise
  `H3_ID_ERROR` (§7.2.6), and successive GOAWAY identifiers do not increase (§5.2: "An
  endpoint MUST NOT increase the value … receiving a GOAWAY containing a larger identifier
  than previously received MUST be treated as a connection error of type H3_ID_ERROR");
* MAX_PUSH_ID is only sent by clients (`H3_FRAME_UNEXPECTED` from a server) and never
  decreases (`H3_ID_ERROR`, §7.2.7);
* CANCEL_PUSH and unknown frames are accepted (push-ID bookkeeping for CANCEL_PUSH is not
  modelled);
* closing the control stream is `H3_CLOSED_CRITICAL_STREAM` (`controlClosed`).

**Request and push streams (§4.1).** `reqStep` reads one message exchange: the header
section (one HEADERS frame), content (DATA frames) and an optional trailer section (one
HEADERS frame). On a response, interim (1xx) HEADERS frames may precede the final one; which
header sections are interim depends on their decoded `:status`, so the machine takes that
classification as a parameter. "a DATA frame before any HEADERS frame, or a HEADERS or DATA
frame after the trailing HEADERS frame, is considered invalid" (`H3_FRAME_UNEXPECTED`);
PUSH_PROMISE is allowed only on a response being read by a client; unknown frames may appear
anywhere and are skipped. A stream that ends before the header section is
`H3_REQUEST_INCOMPLETE` (§4.1) for requests and `H3_FRAME_UNEXPECTED` otherwise (this model's
choice: §4.1 says only "Receipt of an invalid sequence of frames").
-/

namespace Silmaril.Net.Http3

/-! ## Roles and stream identifiers -/

/-- An HTTP/3 endpoint role. -/
inductive Role where
  | client | server
  deriving DecidableEq, Repr, Inhabited

/-- The role that opened a QUIC stream (RFC 9000 §2.1: bit 0). -/
def initiator (id : Nat) : Role := if id % 2 = 0 then .client else .server

/-- Whether a QUIC stream is bidirectional (RFC 9000 §2.1: bit 1 clear). -/
def isBidi (id : Nat) : Bool := id % 4 < 2

/-- Request streams are client-initiated bidirectional streams (§6.1). -/
def isRequestStream (id : Nat) : Bool := id % 4 == 0

/-- A bidirectional stream opened by the peer: a request stream for a server; for a client
(without extensions) a server-initiated bidirectional stream is `H3_STREAM_CREATION_ERROR`. -/
def acceptBidi (self : Role) (id : Nat) : Except ErrorCode Unit :=
  match self with
  | .server => if isRequestStream id then .ok () else .error .streamCreationError
  | .client => .error .streamCreationError

/-! ## Unidirectional stream types (§6.2) -/

def streamTypeControl : Nat := 0x00
def streamTypePush : Nat := 0x01
def streamTypeQpackEncoder : Nat := 0x02
def streamTypeQpackDecoder : Nat := 0x03

/-- What a unidirectional stream header announces. -/
inductive UniKind where
  | control
  | push (pushId : Nat)
  | qpackEncoder
  | qpackDecoder
  /-- Any other type (extension or grease): discarded, never a connection error. -/
  | unknown (type : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Read the unidirectional stream header (§6.2, §6.2.2); `none` if the input ends first. -/
def readUniHeader (xs : List UInt8) : Option (UniKind × List UInt8) :=
  match Quic.VarInt.decode xs with
  | none => none
  | some (t, rest) =>
    if t = streamTypeControl then some (.control, rest)
    else if t = streamTypePush then
      (Quic.VarInt.decode rest).map fun (p, r) => (.push p, r)
    else if t = streamTypeQpackEncoder then some (.qpackEncoder, rest)
    else if t = streamTypeQpackDecoder then some (.qpackDecoder, rest)
    else some (.unknown t, rest)

/-- The header of a unidirectional stream. -/
def encodeUniHeader : UniKind → List UInt8
  | .control => Quic.VarInt.encode streamTypeControl
  | .push p => Quic.VarInt.encode streamTypePush ++ Quic.VarInt.encode p
  | .qpackEncoder => Quic.VarInt.encode streamTypeQpackEncoder
  | .qpackDecoder => Quic.VarInt.encode streamTypeQpackDecoder
  | .unknown t => Quic.VarInt.encode t

/-- The unidirectional streams one peer has opened so far. -/
structure UniStreams where
  control : Bool := false
  qpackEncoder : Bool := false
  qpackDecoder : Bool := false
  pushIds : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- Accept a unidirectional stream opened by `peer` (§6.2.1, §6.2.2, RFC 9204 §4.2). -/
def UniStreams.open_ (peer : Role) (u : UniStreams) : UniKind → Except ErrorCode UniStreams
  | .control => if u.control then .error .streamCreationError else .ok { u with control := true }
  | .qpackEncoder =>
    if u.qpackEncoder then .error .streamCreationError else .ok { u with qpackEncoder := true }
  | .qpackDecoder =>
    if u.qpackDecoder then .error .streamCreationError else .ok { u with qpackDecoder := true }
  | .push p =>
    if peer = .client then .error .streamCreationError
    else if u.pushIds.contains p then .error .idError
    else .ok { u with pushIds := p :: u.pushIds }
  | .unknown _ => .ok u

/-- Accept a sequence of unidirectional streams. -/
def UniStreams.openAll (peer : Role) (u : UniStreams) (ks : List UniKind) :
    Except ErrorCode UniStreams :=
  ks.foldlM (UniStreams.open_ peer) u

/-! ## The control stream (§6.2.1) -/

/-- What the reader of a peer's control stream remembers. -/
structure ControlState where
  /-- The peer's SETTINGS parameters, once received. -/
  settings : Option (List (Nat × Nat)) := none
  /-- The identifier of the last GOAWAY received. -/
  lastGoaway : Option Nat := none
  /-- The last MAX_PUSH_ID received (servers only). -/
  maxPushId : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Read one frame of the control stream sent by `peer`. -/
def controlStep (peer : Role) (s : ControlState) (f : Frame) : Except ErrorCode ControlState :=
  match s.settings with
  | none =>
    match f with
    | .settings ps => .ok { s with settings := some ps }
    | _ => .error .missingSettings
  | some _ =>
    match f with
    | .settings _ | .data _ | .headers _ | .pushPromise _ _ | .h2Reserved _ _ =>
      .error .frameUnexpected
    | .goaway i =>
      if peer = .server ∧ ¬ isRequestStream i then .error .idError
      else if s.lastGoaway.any (· < i) then .error .idError
      else .ok { s with lastGoaway := some i }
    | .maxPushId p =>
      if peer = .server then .error .frameUnexpected
      else if s.maxPushId.any (p < ·) then .error .idError
      else .ok { s with maxPushId := some p }
    | .cancelPush _ | .unknown _ _ => .ok s

/-- Read a sequence of control-stream frames. -/
def controlRun (peer : Role) (s : ControlState) (fs : List Frame) : Except ErrorCode ControlState :=
  fs.foldlM (controlStep peer) s

/-- Frames that are never allowed on a control stream after SETTINGS (§7.2.1, §7.2.2, §7.2.4,
§7.2.5, §7.2.8). -/
def forbiddenAfterSettings : Frame → Bool
  | .settings _ | .data _ | .headers _ | .pushPromise _ _ | .h2Reserved _ _ => true
  | _ => false

/-- GOAWAY order: the new identifier, if the old one is set, is set and at most it (§5.2). -/
def NoIncrease (old new : Option Nat) : Prop :=
  match old with
  | none => True
  | some a => ∃ b, new = some b ∧ b ≤ a

/-- MAX_PUSH_ID order: the new value, if the old one is set, is set and at least it (§7.2.7). -/
def NoDecrease (old new : Option Nat) : Prop :=
  match old with
  | none => True
  | some a => ∃ b, new = some b ∧ a ≤ b

/-- The control stream must never close (§6.2.1). -/
def controlClosed : ErrorCode := .closedCriticalStream

/-! ## Request and push streams (§4.1) -/

/-- Which message a request or push stream carries, as seen by its reader. -/
inductive StreamKind where
  /-- A request, read by a server. -/
  | request
  /-- A response on a request stream, read by a client. -/
  | response
  /-- A pushed response on a push stream, read by a client (§6.2.2). -/
  | push
  deriving DecidableEq, Repr, Inhabited

/-- Where the reader is in the message. -/
inductive Phase where
  /-- Before the (final) header section. -/
  | awaitHeaders
  /-- After the header section: DATA frames or the trailer section may follow. -/
  | body
  /-- After the trailer section: only unknown frames may follow. -/
  | done
  deriving DecidableEq, Repr, Inhabited

/-- The parts of a message as received: still-encoded field sections, the content. -/
structure Parts where
  /-- Interim (1xx) header sections, in order (responses only). -/
  interim : List (List UInt8) := []
  /-- The final header section. -/
  header : List UInt8 := []
  /-- The content: the DATA payloads concatenated (§4.1). -/
  content : List UInt8 := []
  /-- The trailer section, if any. -/
  trailer : Option (List UInt8) := none
  /-- PUSH_PROMISE frames seen on a response (push ID, encoded request header section). -/
  promises : List (Nat × List UInt8) := []
  deriving DecidableEq, Repr, Inhabited

/-- A request/push stream reader state. -/
structure ReqState where
  phase : Phase := .awaitHeaders
  parts : Parts := {}
  deriving DecidableEq, Repr, Inhabited

/-- Read one frame of a request or push stream. `interim h` says whether the encoded header
section `h` is an interim (1xx) response; it is consulted only on responses. -/
def reqStep (k : StreamKind) (interim : List UInt8 → Bool) (s : ReqState) (f : Frame) :
    Except ErrorCode ReqState :=
  match f with
  | .headers h =>
    match s.phase with
    | .awaitHeaders =>
      if k ≠ .request ∧ interim h then
        .ok { s with parts := { s.parts with interim := s.parts.interim ++ [h] } }
      else .ok { phase := .body, parts := { s.parts with header := h } }
    | .body => .ok { phase := .done, parts := { s.parts with trailer := some h } }
    | .done => .error .frameUnexpected
  | .data d =>
    match s.phase with
    | .body => .ok { s with parts := { s.parts with content := s.parts.content ++ d } }
    | _ => .error .frameUnexpected
  | .pushPromise p h =>
    if k = .response then .ok { s with parts := { s.parts with promises := s.parts.promises ++ [(p, h)] } }
    else .error .frameUnexpected
  | .unknown _ _ => .ok s
  | .settings _ | .cancelPush _ | .goaway _ | .maxPushId _ | .h2Reserved _ _ =>
    .error .frameUnexpected

/-- Read a sequence of frames of a request or push stream. -/
def reqRun (k : StreamKind) (interim : List UInt8 → Bool) (s : ReqState) (fs : List Frame) :
    Except ErrorCode ReqState :=
  fs.foldlM (reqStep k interim) s

/-- The stream ended cleanly: the message is complete if its header section arrived. -/
def reqFinish (k : StreamKind) (s : ReqState) : Except ErrorCode Parts :=
  match s.phase with
  | .awaitHeaders => .error (if k = .request then .requestIncomplete else .frameUnexpected)
  | _ => .ok s.parts

/-- The frames a sender writes for one message: the header section, the content split into
`chunks`, and the trailer section if any (§4.1). -/
def messageFrames (header : List UInt8) (chunks : List (List UInt8))
    (trailer : Option (List UInt8)) : List Frame :=
  .headers header :: chunks.map .data ++ (trailer.map fun t => [Frame.headers t]).getD []

/-- Whether a frame is ignored by the stream machines (§9: unknown and extension types). -/
def Frame.isUnknown : Frame → Bool
  | .unknown _ _ => true
  | _ => false

/-- Read all typed frames of a stream's bytes (§7.1, §7.2). -/
def decodeFrames (maxPayload : Nat) (xs : List UInt8) : Except DecodeError (List Frame) :=
  match readRawAll maxPayload xs with
  | .error e => .error (.read e)
  | .ok rs =>
    match rs.mapM Frame.ofRaw with
    | .error e => .error (.protocol e)
    | .ok fs => .ok fs

end Silmaril.Net.Http3

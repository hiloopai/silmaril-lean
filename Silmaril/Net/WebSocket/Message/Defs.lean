module

public import Silmaril.Net.WebSocket.Frame.Defs

@[expose] public section

/-!
# WebSocket messages: fragmentation and the receiver (RFC 6455 §5.4–§5.6, §8.1)

A message is a text or binary payload; a sender may split it into frames (§5.4):

* "An unfragmented message consists of a single frame with the FIN bit set and an opcode
  other than 0";
* "A fragmented message consists of a single frame with the FIN bit clear and an opcode
  other than 0, followed by zero or more frames with the FIN bit clear and the opcode set to
  0, and terminated by a single frame with the FIN bit set and an opcode of 0";
* "Control frames … MAY be injected in the middle of a fragmented message";
* "The fragments of one message MUST NOT be interleaved between the fragments of another
  message unless an extension has been negotiated".

This module gives

* `fragments keys op chunks`: the frames a sender emits for the message `chunks.flatten` with
  opcode `op`, one frame per chunk, the `i`-th frame masked with `keys i` (§5.3);
* `Receiver`: the endpoint's reassembly state (the opcode and data of the message in
  progress), and `Receiver.step role` the processing of one received frame by an endpoint
  of role `role`, which delivers a complete message, a ping, a pong or a close, or fails the
  connection (§7.1.7) with a `Failure`. It checks, in order: the masking direction (§5.1),
  the RSV bits (§5.2: "MUST be 0 unless an extension is negotiated"; this receiver
  negotiates none), the opcode (§5.2: reserved opcodes fail the connection), the control
  frame limits (§5.5), the close body (§5.5.1, §7.4), and the fragmentation rules (§5.4).
  Text messages must be UTF-8 (§8.1), checked on the complete message so that a code point
  may span fragments ("the text … may be split across fragments", §5.6).
* `Receiver.run`: a sequence of frames.

Theorems (`Message.Thms`): any fragmentation of a message is delivered as that message, and
ping/pong frames injected between fragments do not change the data messages delivered.

Not modelled: extensions (permessage-deflate, RFC 7692, uses RSV1; it would reuse
`Silmaril.Formats.Compression.Deflate` and is owned by the compression track), the
"Fail the WebSocket Connection" side effects on TCP, and buffering limits other than the
per-frame limit of `decode`.
-/

namespace Silmaril.Net.WebSocket

/-- What a receiver passes to the application. -/
inductive Delivery where
  /-- A complete text (`opText`) or binary (`opBinary`) message. -/
  | message (opcode : Nat) (data : List UInt8)
  | ping (data : List UInt8)
  | pong (data : List UInt8)
  /-- A Close frame with its (decoded) body. -/
  | close (body : Option (Nat × List UInt8))
  deriving DecidableEq, Repr

/-- Why the connection is failed (§7.1.7), with the status code to report (§7.4.1). -/
inductive Failure where
  /-- §5.1: a masked frame from a server or an unmasked frame from a client (1002). -/
  | masking
  /-- §5.2: an RSV bit without a negotiated extension (1002). -/
  | reservedBits
  /-- §5.2: a reserved opcode (1002). -/
  | reservedOpcode
  /-- §5.5: a fragmented or oversized control frame (1002). -/
  | controlFrame
  /-- §5.5.1, §7.4: a malformed Close body (1002, or 1007 for its reason). -/
  | closeBody
  /-- §5.4: a continuation frame with no message in progress (1002). -/
  | unexpectedContinuation
  /-- §5.4: a new data frame while a message is in progress (1002). -/
  | interleaved
  /-- §8.1: a text message that is not UTF-8 (1007). -/
  | invalidUtf8
  deriving DecidableEq, Repr

/-- The status code an endpoint sends when it fails the connection for this reason (§7.4.1:
1002 protocol error, 1007 inconsistent data). -/
def Failure.code : Failure → Nat
  | .invalidUtf8 => 1007
  | _ => 1002

/-- The role of the other endpoint. -/
def Role.peer : Role → Role
  | .client => .server
  | .server => .client

/-- The reassembly state: the opcode and the data received so far of the message in
progress. -/
structure Receiver where
  current : Option (Nat × List UInt8) := none
  deriving DecidableEq, Repr, Inhabited

/-- A complete data message, after the §8.1 UTF-8 check for text. -/
def complete (op : Nat) (data : List UInt8) : Except Failure Delivery :=
  if op == opText && !isUtf8 data then .error .invalidUtf8 else .ok (.message op data)

/-- Process a control frame (§5.5). -/
def controlDelivery (f : Frame) : Except Failure Delivery :=
  if !f.controlOk then .error .controlFrame
  else if f.opcode == opPing then .ok (.ping f.payload)
  else if f.opcode == opPong then .ok (.pong f.payload)
  else match decodeClose f.payload with
    | some body => .ok (.close body)
    | none => .error .closeBody

/-- Process one frame received by an endpoint of role `role`. -/
def Receiver.step (role : Role) (r : Receiver) (f : Frame) :
    Except Failure (Receiver × Option Delivery) :=
  if !f.maskOk role.peer then .error .masking
  else if f.rsv != 0 then .error .reservedBits
  else if !isDefinedOpcode f.opcode then .error .reservedOpcode
  else if isControl f.opcode then
    match controlDelivery f with
    | .ok d => .ok (r, some d)
    | .error e => .error e
  else
    match r.current, f.opcode == opContinuation with
    | none, true => .error .unexpectedContinuation
    | some _, false => .error .interleaved
    | some (op, data), true =>
      if f.fin then
        match complete op (data ++ f.payload) with
        | .ok d => .ok (⟨none⟩, some d)
        | .error e => .error e
      else .ok (⟨some (op, data ++ f.payload)⟩, none)
    | none, false =>
      if f.fin then
        match complete f.opcode f.payload with
        | .ok d => .ok (⟨none⟩, some d)
        | .error e => .error e
      else .ok (⟨some (f.opcode, f.payload)⟩, none)

/-- Process a sequence of frames; the deliveries in order. -/
def Receiver.run (role : Role) (r : Receiver) : List Frame → Except Failure (Receiver × List Delivery)
  | [] => .ok (r, [])
  | f :: fs =>
    match r.step role f with
    | .error e => .error e
    | .ok (r', d) =>
      match r'.run role fs with
      | .error e => .error e
      | .ok (r'', ds) => .ok (r'', d.toList ++ ds)

/-! ## Sending -/

/-- The frames for the message with opcode `op` and data `chunks.flatten`, the `i`-th frame
masked with `keys i` (§5.4). The first frame carries `op`, the others are continuations, and
only the last has FIN. An empty chunk list is sent as one empty frame. -/
def fragmentsFrom (keys : Nat → Option MaskKey) (i : Nat) (op : Nat) :
    List (List UInt8) → List Frame
  | [] => [⟨true, 0, op, keys i, []⟩]
  | [c] => [⟨true, 0, op, keys i, c⟩]
  | c :: cs => ⟨false, 0, op, keys i, c⟩ :: fragmentsFrom keys (i + 1) opContinuation cs

/-- The frames of a message, numbered from 0. -/
def fragments (keys : Nat → Option MaskKey) (op : Nat) (chunks : List (List UInt8)) :
    List Frame :=
  fragmentsFrom keys 0 op chunks

/-- A key supply that respects §5.1 for a sender of role `role`: a key for every frame of a
client, none for a server. -/
def KeysFor (role : Role) (keys : Nat → Option MaskKey) : Prop :=
  ∀ i, (keys i).isSome = (role == .client)

/-- Data messages among the deliveries. -/
def dataOnly (ds : List Delivery) : List Delivery :=
  ds.filter fun | .message _ _ => true | _ => false

/-- A ping or pong frame that the receiver accepts (§5.5.2, §5.5.3). -/
def Frame.isKeepalive (role : Role) (f : Frame) : Bool :=
  f.maskOk role.peer && f.rsv == 0 && (f.opcode == opPing || f.opcode == opPong) &&
    f.controlOk

end Silmaril.Net.WebSocket

module

public import Silmaril.Net.Quic.Error.Defs

@[expose] public section

/-!
# QUIC stream states and final sizes (RFC 9000 §3.1, §3.2, §3.5, §4.5)

**Sending part (§3.1, Figure 2).**

```
       o
       | Create Stream (Sending)
       | Peer Creates Bidirectional Stream
       v
   +-------+
   | Ready | Send RESET_STREAM
   |       |-----------------------.
   +-------+                       |
       |                           |
       | Send STREAM /             |
       |      STREAM_DATA_BLOCKED  |
       v                           |
   +-------+                       |
   | Send  | Send RESET_STREAM     |
   |       |---------------------->|
   +-------+                       |
       |                           |
       | Send STREAM + FIN         |
       v                           v
   +-------+                   +-------+
   | Data  | Send RESET_STREAM | Reset |
   | Sent  |------------------>| Sent  |
   +-------+                   +-------+
       |                           |
       | Recv All ACKs             | Recv ACK
       v                           v
   +-------+                   +-------+
   | Data  |                   | Reset |
   | Recvd |                   | Recvd |
   +-------+                   +-------+
```

`sendStep s e` is the sending part after the event `e`, or `none` when §3 forbids it: "A
sender MUST NOT send any of these frames from a terminal state ("Data Recvd" or "Reset
Recvd"). A sender MUST NOT send a STREAM or STREAM_DATA_BLOCKED frame for a stream in the
"Reset Sent" state or any terminal state" (§3.3), and "An endpoint MUST NOT send data on a
stream at or beyond the final size" (§4.5). `SendStream` counts the bytes `sent` (the next
offset; retransmissions are not new data) and records the `finalSize` once the FIN or
RESET_STREAM is sent. "An endpoint that receives a STOP_SENDING frame MUST send a
RESET_STREAM frame if the stream is in the "Ready" or "Send" state" (§3.5): `recvStopSending c`
resets with the peer's code ("SHOULD copy the error code"); in "Data Sent" the RFC allows
deferring, and this model defers (the stream then completes or is reset by the application);
in other states STOP_SENDING is ignored ("A sender could receive either of these two types of
frames in any state as a result of delayed delivery").

**Receiving part (§3.2, Figure 3).**

```
       o
       | Recv STREAM / STREAM_DATA_BLOCKED / RESET_STREAM
       | Create Bidirectional Stream (Sending)
       | Recv MAX_STREAM_DATA / STOP_SENDING (Bidirectional)
       | Create Higher-Numbered Stream
       v
   +-------+
   | Recv  | Recv RESET_STREAM
   |       |-----------------------.
   +-------+                       |
       |                           |
       | Recv STREAM + FIN         |
       v                           |
   +-------+                       |
   | Size  | Recv RESET_STREAM     |
   | Known |---------------------->|
   +-------+                       |
       |                           |
       | Recv All Data             |
       v                           v
   +-------+ Recv RESET_STREAM +-------+
   | Data  |--- (optional) --->| Reset |
   | Recvd |  Recv All Data    | Recvd |
   +-------+<-- (optional) ----+-------+
       |                           |
       | App Read All Data         | App Read Reset
       v                           v
   +-------+                   +-------+
   | Data  |                   | Reset |
   | Read  |                   | Read  |
   +-------+                   +-------+
```

`recvStep s e` processes a frame received for the stream (or a local event) and reports the
FINAL_SIZE_ERRORs of §4.5 / §20.1, in every state ("even after a stream is closed"):

1. "an endpoint received a STREAM frame containing data that exceeded the previously
   established final size";
2. "an endpoint received a STREAM frame or a RESET_STREAM frame containing a final size that
   was lower than the size of stream data that was already received";
3. "an endpoint received a STREAM frame or a RESET_STREAM frame containing a different final
   size to the one already established".

`RecvStream` keeps the `highest` received offset (end of the furthest data, the quantity flow
control counts, §4.1) and the `finalSize` once known ("the sum of the Offset and Length fields
of a STREAM frame with a FIN flag … Alternatively, the Final Size field of a RESET_STREAM
frame", §4.5). The stream data itself is in `Silmaril.Net.Quic.Reassembly`; the local events
`allData` (the reassembly buffer holds every byte below the final size), `readAll` and
`readReset` (the application consumed the data / the reset signal) drive the remaining
transitions.

**Choices** where §3.2 allows latitude ("An implementation is free to manage this situation as
it chooses"): RESET_STREAM in "Data Recvd" is suppressed (the stream stays in "Data Recvd": "If
the RESET_STREAM is suppressed, the receiving part of the stream remains in "Data Recvd""),
and data completing after a reset does not leave "Reset Recvd". The first RESET_STREAM's error
code is kept. Stream creation (which frames create which parts, §3.2 first paragraphs) is the
job of `StreamId`/`Acceptor` and is not repeated here.
-/

namespace Silmaril.Net.Quic

/-- States of the sending part of a stream (§3.1). -/
inductive SendState where
  | ready
  | send
  | dataSent
  | resetSent
  | dataRecvd
  | resetRecvd
  deriving DecidableEq, Repr, Inhabited

/-- "Data Recvd" and "Reset Recvd" are terminal (§3.1). -/
def SendState.terminal : SendState → Bool
  | .dataRecvd | .resetRecvd => true
  | _ => false

/-- States of the receiving part of a stream (§3.2). -/
inductive RecvState where
  | recv
  | sizeKnown
  | dataRecvd
  | resetRecvd
  | dataRead
  | resetRead
  deriving DecidableEq, Repr, Inhabited

/-- "Data Read" and "Reset Read" are terminal (§3.2). -/
def RecvState.terminal : RecvState → Bool
  | .dataRead | .resetRead => true
  | _ => false

/-- The sending part of a stream. -/
structure SendStream where
  state : SendState := .ready
  /-- Bytes handed to STREAM frames so far: the offset of the next new byte. -/
  sent : Nat := 0
  /-- Known once a FIN or RESET_STREAM was sent (§4.5). -/
  finalSize : Option Nat := none
  /-- The application error code of the RESET_STREAM sent, if any. -/
  resetCode : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Events of the sending part. -/
inductive SendEvent where
  /-- Send a STREAM frame carrying the next `n` bytes, without FIN. -/
  | data (n : Nat)
  /-- Send a STREAM frame with the FIN bit (all data written). -/
  | fin
  /-- Send STREAM_DATA_BLOCKED. -/
  | blocked
  /-- Send RESET_STREAM with an application error code (abrupt termination, §2.4). -/
  | reset (code : Nat)
  /-- Receive STOP_SENDING with an application error code (§3.5). -/
  | recvStopSending (code : Nat)
  /-- All stream data and the FIN were acknowledged. -/
  | allAcked
  /-- The RESET_STREAM was acknowledged. -/
  | resetAcked
  deriving DecidableEq, Repr

/-- Send RESET_STREAM: the final size is what was sent. -/
def SendStream.doReset (s : SendStream) (code : Nat) : SendStream :=
  { s with state := .resetSent, finalSize := some s.sent, resetCode := some code }

/-- The sending part after an event; `none` for a send §3.3 / §4.5 forbid. -/
def sendStep (s : SendStream) : SendEvent → Option SendStream
  | .data n =>
    match s.state with
    | .ready | .send => some { s with state := .send, sent := s.sent + n }
    | _ => none
  | .blocked =>
    match s.state with
    | .ready | .send => some { s with state := .send }
    | _ => none
  | .fin =>
    match s.state with
    | .ready | .send => some { s with state := .dataSent, finalSize := some s.sent }
    | _ => none
  | .reset c =>
    match s.state with
    | .ready | .send | .dataSent => some (s.doReset c)
    | _ => none
  | .recvStopSending c =>
    match s.state with
    | .ready | .send => some (s.doReset c)
    | _ => some s
  | .allAcked =>
    match s.state with
    | .dataSent => some { s with state := .dataRecvd }
    | _ => none
  | .resetAcked =>
    match s.state with
    | .resetSent => some { s with state := .resetRecvd }
    | _ => none

/-- Run a list of sending events. -/
def sendSteps (s : SendStream) : List SendEvent → Option SendStream
  | [] => some s
  | e :: es => (sendStep s e).bind (sendSteps · es)

/-- The sending invariant: the final size is known exactly outside "Ready"/"Send", and then it
is the number of bytes sent. -/
def SendStream.Ok (s : SendStream) : Prop :=
  (s.finalSize = none ↔ (s.state = .ready ∨ s.state = .send)) ∧
    ∀ n, s.finalSize = some n → n = s.sent

/-- The receiving part of a stream. -/
structure RecvStream where
  state : RecvState := .recv
  /-- The largest offset received: the end of the furthest STREAM data (or 0). -/
  highest : Nat := 0
  /-- The final size, once known (§4.5). -/
  finalSize : Option Nat := none
  /-- The application error code of the first RESET_STREAM received, if any. -/
  resetCode : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Events of the receiving part. -/
inductive RecvEvent where
  /-- A STREAM frame with this offset, data length and FIN bit. -/
  | stream (offset len : Nat) (fin : Bool)
  /-- A STREAM_DATA_BLOCKED frame. -/
  | dataBlocked
  /-- A RESET_STREAM frame with an application error code and final size. -/
  | resetStream (code finalSize : Nat)
  /-- Local: every byte below the final size has been received. -/
  | allData
  /-- Local: the application read all data. -/
  | readAll
  /-- Local: the application was told of the reset. -/
  | readReset
  deriving DecidableEq, Repr

/-- Where RESET_STREAM leads (§3.2): from "Recv" and "Size Known" to "Reset Recvd"; it is
suppressed in "Data Recvd" and ignored afterwards. -/
def RecvState.afterReset : RecvState → RecvState
  | .recv | .sizeKnown => .resetRecvd
  | s => s

/-- The receiving part after an event, or the FINAL_SIZE_ERROR of §4.5. -/
def recvStep (s : RecvStream) : RecvEvent → Except TransportError RecvStream
  | .stream off len fin =>
    let e := off + len
    match s.finalSize with
    | some n =>
      if n < e then .error .finalSizeError
      else if fin ∧ e ≠ n then .error .finalSizeError
      else .ok { s with highest := max s.highest e }
    | none =>
      if fin then
        if e < s.highest then .error .finalSizeError
        else .ok { s with highest := e, finalSize := some e,
                          state := if s.state = .recv then .sizeKnown else s.state }
      else .ok { s with highest := max s.highest e }
  | .dataBlocked => .ok s
  | .resetStream c n =>
    match s.finalSize with
    | some m =>
      if m ≠ n then .error .finalSizeError
      else .ok { s with state := s.state.afterReset, resetCode := s.resetCode.or (some c) }
    | none =>
      if n < s.highest then .error .finalSizeError
      else .ok { s with state := s.state.afterReset, finalSize := some n,
                        resetCode := s.resetCode.or (some c) }
  | .allData =>
    match s.state with
    | .sizeKnown => .ok { s with state := .dataRecvd }
    | _ => .ok s
  | .readAll =>
    match s.state with
    | .dataRecvd => .ok { s with state := .dataRead }
    | _ => .ok s
  | .readReset =>
    match s.state with
    | .resetRecvd => .ok { s with state := .resetRead }
    | _ => .ok s

/-- Run a list of receiving events, stopping at the first error. -/
def recvSteps (s : RecvStream) : List RecvEvent → Except TransportError RecvStream
  | [] => .ok s
  | e :: es => (recvStep s e).bind (recvSteps · es)

/-- The receiving invariant: the final size is known exactly outside "Recv", and nothing was
received beyond it. -/
def RecvStream.Ok (s : RecvStream) : Prop :=
  (s.finalSize = none ↔ s.state = .recv) ∧ ∀ n, s.finalSize = some n → s.highest ≤ n

end Silmaril.Net.Quic

module

public import Silmaril.Net.Http2.Frame.Defs
public import Silmaril.Automata.Named.Derive
public import Silmaril.Automata.Machine.Defs

@[expose] public section

/-!
# HTTP/2 stream states (RFC 9113 §5.1, §5.1.1)

The lifecycle of a stream (§5.1, Figure 2) from the point of view of one endpoint:

```
                         +--------+
                 send PP |        | recv PP
                ,--------+  idle  +--------.
               /         |        |         \
              v          +--------+          v
       +----------+          |           +----------+
       |          |          | send H /  |          |
,------+ reserved |          | recv H    | reserved +------.
|      | (local)  |          |           | (remote) |      |
|      +---+------+          v           +------+---+      |
|          |             +--------+             |          |
|          |     recv ES |        | send ES     |          |
|   send H |     ,-------+  open  +-------.     | recv H   |
|          |    /        |        |        \    |          |
|          v   v         +---+----+         v   v          |
|      +----------+          |           +----------+      |
|      |   half-  |          |           |   half-  |      |
|      |  closed  |          | send R /  |  closed  |      |
|      | (remote) |          | recv R    | (local)  |      |
|      +----+-----+          |           +-----+----+      |
|           |                |                 |           |
|           | send ES /      |       recv ES / |           |
|           | send R /       v        send R / |           |
|           | recv R     +--------+   recv R   |           |
| send R /  `----------->|        |<-----------'  send R / |
| recv R                 | closed |               recv R   |
`----------------------->|        |<-----------------------'
                         +--------+
```

`step s e` is the next state after the event `e` (a frame sent or received on the stream), or
the error the RFC prescribes:

* `connection c`: a connection error (§5.4.1), e.g. a DATA frame received on an idle stream
  is a `PROTOCOL_ERROR` (§5.1 "idle");
* `stream c`: a stream error (§5.4.2), e.g. DATA received in half-closed (remote) is
  `STREAM_CLOSED` (§5.1 "half-closed (remote)");
* `illegalSend`: the local endpoint attempted a send that §5.1 forbids ("MUST NOT send").

The events are HEADERS (with any CONTINUATION frames, carrying END_STREAM or not), DATA,
RST_STREAM, PRIORITY, WINDOW_UPDATE, and the PUSH_PROMISE that *reserves this stream* (it is
sent on another stream, §6.6). PUSH_PROMISE is only legal on an idle promised stream.

**Choices** where §5.1 leaves latitude:

* In *closed*, every received frame other than a reserving PUSH_PROMISE is ignored for the
  purpose of the stream state. The RFC says an endpoint "MAY treat receipt of any other type
  of frame on a closed stream as a connection error … of type STREAM_CLOSED", and after
  sending RST_STREAM "MUST minimally process and then discard any frames it receives";
  discarding is allowed in both cases. The minimal processing (HPACK state for HEADERS, the
  connection window for DATA) is connection-level and not part of this machine.
* The machine does not know the endpoint's role. The rule that a server-initiated idle stream
  receiving HEADERS is a connection error (§5.1 "idle") is a stream-identifier rule, and lives
  with `openRemote` (§5.1.1), as does the implicit idle → closed transition of lower
  identifiers.
* END_STREAM is processed together with the frame that carries it ("a HEADERS frame with the
  END_STREAM flag set can cause two state transitions", §5.1): `headers true` moves idle to
  half-closed directly.

**As a finite machine.** `StreamState`, `Signal`, `Dir` and `Event` are finite named types
(`silmaril_finite`, `Silmaril.Automata.FinNamed`): an event is named `(send,headers(true))`.
`machine` is `step` as a `Silmaril.Automata.DMachine`, with the marks `marks` (initial idle,
accepting closed); its JSON document is `silmaril/machines/http2-stream.toml`, and the
binding in the project self-test proves that the document is exactly this machine.

Stream identifiers (§5.1.1): client-initiated streams are odd, server-initiated even, and a new
stream's identifier is larger than every identifier its initiator opened before
(`openRemote`).
-/

namespace Silmaril.Net.Http2

/-- The stream states of §5.1. -/
inductive StreamState where
  | idle | reservedLocal | reservedRemote | «open» | halfClosedLocal | halfClosedRemote | closed
  deriving DecidableEq, Repr, Inhabited

silmaril_finite StreamState

/-- The frames that drive the state machine. -/
inductive Signal where
  /-- HEADERS (and its CONTINUATION frames), with or without END_STREAM. -/
  | headers (endStream : Bool)
  /-- The PUSH_PROMISE that reserves this stream. -/
  | pushPromise
  /-- DATA, with or without END_STREAM. -/
  | data (endStream : Bool)
  | rstStream
  | priority
  | windowUpdate
  deriving DecidableEq, Repr, Inhabited

silmaril_finite Signal

/-- Sent by this endpoint, or received from the peer. -/
inductive Dir where
  | send | recv
  deriving DecidableEq, Repr, Inhabited

silmaril_finite Dir

/-- An event on a stream. -/
structure Event where
  dir : Dir
  signal : Signal
  deriving DecidableEq, Repr, Inhabited

silmaril_finite Event

/-- What goes wrong (§5.4). -/
inductive StreamError where
  | connection (code : ErrorCode)
  | stream (code : ErrorCode)
  | illegalSend
  deriving DecidableEq, Repr, Inhabited

namespace StreamState

/-- The state the peer sees: local and remote exchange roles. -/
def dual : StreamState → StreamState
  | reservedLocal => reservedRemote | reservedRemote => reservedLocal
  | halfClosedLocal => halfClosedRemote | halfClosedRemote => halfClosedLocal
  | s => s

/-- How far the stream has progressed towards closed. -/
def rank : StreamState → Nat
  | idle => 0 | reservedLocal => 1 | reservedRemote => 1 | «open» => 1
  | halfClosedLocal => 2 | halfClosedRemote => 2 | closed => 3

end StreamState

open StreamState Signal Dir in
/-- One step of the stream state machine (§5.1). -/
def step : StreamState → Event → Except StreamError StreamState
  -- PRIORITY may be sent and received in every state and changes nothing (§5.1, §6.3).
  | s, ⟨_, priority⟩ => .ok s
  -- idle
  | idle, ⟨send, headers es⟩ => .ok (if es then halfClosedLocal else «open»)
  | idle, ⟨recv, headers es⟩ => .ok (if es then halfClosedRemote else «open»)
  | idle, ⟨send, pushPromise⟩ => .ok reservedLocal
  | idle, ⟨recv, pushPromise⟩ => .ok reservedRemote
  | idle, ⟨send, _⟩ => .error .illegalSend
  | idle, ⟨recv, _⟩ => .error (.connection .protocolError)
  -- a stream is reserved only while idle (§6.6)
  | _, ⟨send, pushPromise⟩ => .error .illegalSend
  | _, ⟨recv, pushPromise⟩ => .error (.connection .protocolError)
  -- RST_STREAM closes any non-idle stream (§6.4); nothing but PRIORITY is sent when closed
  | closed, ⟨send, _⟩ => .error .illegalSend
  | closed, ⟨recv, _⟩ => .ok closed
  | _, ⟨_, rstStream⟩ => .ok closed
  -- reserved (local): send HEADERS; receive WINDOW_UPDATE
  | reservedLocal, ⟨send, headers es⟩ => .ok (if es then closed else halfClosedRemote)
  | reservedLocal, ⟨recv, windowUpdate⟩ => .ok reservedLocal
  | reservedLocal, ⟨send, _⟩ => .error .illegalSend
  | reservedLocal, ⟨recv, _⟩ => .error (.connection .protocolError)
  -- reserved (remote): receive HEADERS; send WINDOW_UPDATE
  | reservedRemote, ⟨recv, headers es⟩ => .ok (if es then closed else halfClosedLocal)
  | reservedRemote, ⟨send, windowUpdate⟩ => .ok reservedRemote
  | reservedRemote, ⟨send, _⟩ => .error .illegalSend
  | reservedRemote, ⟨recv, _⟩ => .error (.connection .protocolError)
  -- open
  | «open», ⟨send, headers es⟩ | «open», ⟨send, data es⟩ =>
    .ok (if es then halfClosedLocal else «open»)
  | «open», ⟨recv, headers es⟩ | «open», ⟨recv, data es⟩ =>
    .ok (if es then halfClosedRemote else «open»)
  | «open», ⟨_, windowUpdate⟩ => .ok «open»
  -- half-closed (local): send only WINDOW_UPDATE, PRIORITY, RST_STREAM; receive anything
  | halfClosedLocal, ⟨send, windowUpdate⟩ => .ok halfClosedLocal
  | halfClosedLocal, ⟨send, _⟩ => .error .illegalSend
  | halfClosedLocal, ⟨recv, headers es⟩ | halfClosedLocal, ⟨recv, data es⟩ =>
    .ok (if es then closed else halfClosedLocal)
  | halfClosedLocal, ⟨recv, windowUpdate⟩ => .ok halfClosedLocal
  -- half-closed (remote): send anything; receive only WINDOW_UPDATE, PRIORITY, RST_STREAM
  | halfClosedRemote, ⟨send, headers es⟩ | halfClosedRemote, ⟨send, data es⟩ =>
    .ok (if es then closed else halfClosedRemote)
  | halfClosedRemote, ⟨send, windowUpdate⟩ => .ok halfClosedRemote
  | halfClosedRemote, ⟨recv, windowUpdate⟩ => .ok halfClosedRemote
  | halfClosedRemote, ⟨recv, _⟩ => .error (.stream .streamClosed)

/-- **The stream machine** (`Silmaril.Automata`): the step function as a deterministic
machine over the finite types of states and events; an error rejects. Its document is
`silmaril/machines/http2-stream.toml`, bound by `ProjectSelfTest.Machines`. -/
def machine : Silmaril.Automata.DMachine StreamState Event := .ofExcept step

/-- The marking layer: streams start idle and end closed. -/
def marks : Silmaril.Automata.Marks StreamState where
  initial s := s == .idle
  accepting s := s == .closed

/-- Run a sequence of events. -/
def run (s : StreamState) : List Event → Except StreamError StreamState
  | [] => .ok s
  | e :: es => match step s e with
    | .ok s' => run s' es
    | .error err => .error err

/-! ## Stream identifiers (§5.1.1) -/

/-- Which endpoint initiates a stream identifier: odd for the client, even (non-zero) for the
server; 0 is the connection. -/
def clientInitiated (id : Nat) : Bool := id % 2 == 1

/-- The largest stream identifier the peer has opened so far (0 if none). A new identifier from
the peer must have the peer's parity and exceed it, else "the endpoint MUST respond with a
connection error … of type PROTOCOL_ERROR" (§5.1.1). Opening it implicitly closes the smaller
idle ones. -/
def openRemote (peerIsClient : Bool) (last id : Nat) : Except StreamError Nat :=
  if id ≠ 0 && clientInitiated id == peerIsClient && last < id then .ok id
  else .error (.connection .protocolError)

end Silmaril.Net.Http2

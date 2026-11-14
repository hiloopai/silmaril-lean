module

public import Silmaril.Automata.Named.Derive
public import Silmaril.Automata.Machine.Defs

@[expose] public section

/-!
# The WebSocket connection lifecycle and closing handshake (RFC 6455 §4, §5.5.1, §7)

One endpoint's view of a connection, as a finite machine (`Silmaril.Automata`):

* `connecting`: the opening handshake (§4) is in progress; the readyState `CONNECTING`;
* `open`: data and control frames flow in both directions (§4.1: "the WebSocket Connection
  is established and in the OPEN state");
* `closeSent`: this endpoint has sent a Close frame (§5.5.1: "the application MUST NOT
  send any more data frames after sending a Close frame"); it keeps receiving until the
  peer's Close arrives;
* `closeReceived`: the peer's Close arrived first; this endpoint "MUST send a Close frame in
  response … It SHOULD do so as soon as practical. An endpoint MAY delay sending a Close
  frame until its current message is sent" (§5.5.1). The peer sends no more data;
* `closed`: both Close frames were exchanged ("The WebSocket Closing Handshake is
  Started"/"The WebSocket Connection is Closed", §7.1.3, §7.1.4), or the transport closed.

Events: sending or receiving a data frame, a ping or pong, or a Close frame; the handshake
succeeding or failing (§4.1: "If the server's response is not valid, the client MUST _Fail the
WebSocket Connection_"); and the underlying TCP connection closing, which is abnormal
(status 1006, §7.1.5) unless both Close frames were exchanged.

Choices recorded here: a frame received in `closeReceived` other than a ping or pong is a
protocol error (the peer has closed its side); sending a ping or pong in `closeSent` is
allowed (§5.5.1 forbids only data frames); a second Close in either direction is an error.
Which endpoint closes the TCP connection first (§7.1.1: "the server … SHOULD close it first")
is not modelled.
-/

namespace Silmaril.Net.WebSocket

/-- The connection states of one endpoint. -/
inductive ConnState where
  | connecting | «open» | closeSent | closeReceived | closed
  deriving DecidableEq, Repr, Inhabited

silmaril_finite ConnState

/-- The kinds of frames that matter to the lifecycle. -/
inductive FrameKind where
  | data | keepalive | close
  deriving DecidableEq, Repr, Inhabited

silmaril_finite FrameKind

/-- Sent by this endpoint, or received from the peer. -/
inductive Dir where
  | send | recv
  deriving DecidableEq, Repr, Inhabited

silmaril_finite Dir

/-- A lifecycle event. -/
inductive ConnEvent where
  | frame (dir : Dir) (kind : FrameKind)
  | handshakeOk
  | handshakeFail
  | tcpClose
  deriving DecidableEq, Repr, Inhabited

silmaril_finite ConnEvent

/-- Lifecycle errors. -/
inductive ConnError where
  /-- This endpoint would break a rule (for example, send data after its Close). -/
  | illegalSend
  /-- The peer broke a rule: fail the connection with 1002 (§7.4.1). -/
  | protocol
  deriving DecidableEq, Repr, Inhabited

open ConnState ConnEvent Dir FrameKind in
/-- One step of the lifecycle. -/
def connStep : ConnState → ConnEvent → Except ConnError ConnState
  | _, tcpClose => .ok closed
  | connecting, handshakeOk => .ok «open»
  | connecting, handshakeFail => .ok closed
  | connecting, frame send _ => .error .illegalSend
  | connecting, frame recv _ => .error .protocol
  | _, handshakeOk | _, handshakeFail => .error .protocol
  | «open», frame send close => .ok closeSent
  | «open», frame recv close => .ok closeReceived
  | «open», frame _ _ => .ok «open»
  | closeSent, frame send data | closeSent, frame send close => .error .illegalSend
  | closeSent, frame send keepalive => .ok closeSent
  | closeSent, frame recv close => .ok closed
  | closeSent, frame recv _ => .ok closeSent
  | closeReceived, frame send close => .ok closed
  | closeReceived, frame send _ => .ok closeReceived
  | closeReceived, frame recv keepalive => .ok closeReceived
  | closeReceived, frame recv _ => .error .protocol
  | closed, frame send _ => .error .illegalSend
  | closed, frame recv _ => .error .protocol

/-- **The lifecycle machine** (`Silmaril.Automata`): `connStep` as a deterministic machine. -/
def connMachine : Silmaril.Automata.DMachine ConnState ConnEvent := .ofExcept connStep

/-- Marks: connections start connecting and end closed. -/
def connMarks : Silmaril.Automata.Marks ConnState where
  initial s := s == .connecting
  accepting s := s == .closed

/-- Events other than a transport close: the closing handshake proper. -/
def ConnEvent.clean : ConnEvent → Bool
  | .tcpClose => false
  | _ => true

end Silmaril.Net.WebSocket

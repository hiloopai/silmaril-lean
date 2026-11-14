module

public import Silmaril.Net.WebTransport.Capsule.Defs
public import Silmaril.Net.WebTransport.Stream.Defs
public import Silmaril.Net.WebTransport.Establish.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: the session state machine (draft-ietf-webtrans-http3-17 §3.2, §4,
§4.6, §4.7, §6)

Rules are those of draft -17 (in WG Last Call, not an RFC) and may change before RFC
publication.

A session is identified by the stream ID of its CONNECT stream (§4: "Session IDs are derived
from the stream ID of the CONNECT stream that established the session"; `Session.ofConnect`).
One endpoint's view of it moves through

```
establishing ──2xx──▶ established ──WT_DRAIN_SESSION / GOAWAY──▶ draining
     │                    │                                         │
     └── non-2xx ─────────┴──── WT_CLOSE_SESSION, FIN, reset ───────┴──▶ closed
```

* **establishing**: the CONNECT request is sent (client) or received (server). Streams and
  datagrams may already be opened and sent ("The client MAY optimistically open unidirectional
  and bidirectional streams, as well as send datagrams … On the server side, opening streams and
  sending datagrams is possible as soon as the CONNECT request has been received", §4), but the
  CONNECT stream's bytes are not yet processed as capsules ("A server MUST NOT process these
  bytes as capsules until it sends a 2xx response", §3.2).
* **established**: after a 2xx response (§3.2). A 3xx or other status ends the attempt.
* **draining**: after a WT_DRAIN_SESSION capsule or an HTTP/3 GOAWAY, sent or received (§4.7):
  "an endpoint MAY continue using the session: it MAY open new WebTransport streams and MAY send
  new datagrams".
* **closed**: "A WebTransport session over HTTP/3 is terminated when either of the following
  conditions is met: the CONNECT stream is closed, either cleanly or abruptly, on either side;
  or a WT_CLOSE_SESSION capsule is either sent or received." (§6) "Upon learning that the
  session has been terminated, the endpoint MUST reset the send side and abort reading on the
  receive side of all unidirectional and bidirectional streams associated with the session …
  using the WT_SESSION_GONE error code; it MUST NOT send any new datagrams or open any new
  streams." "An endpoint that sends a WT_CLOSE_SESSION capsule MUST immediately send a FIN on
  the CONNECT Stream." "If any additional stream data is received on the CONNECT stream after
  receiving a WT_CLOSE_SESSION capsule, the stream MUST be reset with code H3_MESSAGE_ERROR."
  "Cleanly terminating a CONNECT stream without a WT_CLOSE_SESSION capsule SHALL be semantically
  equivalent to terminating it with a WT_CLOSE_SESSION capsule that has an error code of 0 and
  an empty error string."

`step` returns the next state and the actions the endpoint must take. `incomingStream` and
`incomingDatagram` are the §4.6 buffering rules for data that names a session.

**Assumed (abstract).** The streams being reset, the FIN and the CONNECT stream itself belong to
the QUIC stream service; `Action` names what must happen to them.
-/

namespace Silmaril.Net.WebTransport

/-- Why a session ended. -/
inductive CloseReason where
  /-- WT_CLOSE_SESSION sent or received, or a clean FIN (code 0, empty message). -/
  | closed (code : Nat) (message : List UInt8)
  /-- The CONNECT stream was reset. -/
  | aborted
  /-- The server answered the CONNECT with a non-2xx status. -/
  | rejected (status : Nat)
  deriving DecidableEq, Repr

/-- One endpoint's view of a session. -/
inductive SessionState where
  | establishing
  | established
  | draining
  | closed (reason : CloseReason)
  deriving DecidableEq, Repr

/-- What happens to a session. -/
inductive SessionEvent where
  /-- The response to the CONNECT request (received by the client, sent by the server). -/
  | response (status : Nat)
  /-- WT_DRAIN_SESSION sent or received, or an HTTP/3 GOAWAY (§4.7). -/
  | drain
  /-- This endpoint sends WT_CLOSE_SESSION. -/
  | closeSent (code : Nat) (message : List UInt8)
  /-- This endpoint receives WT_CLOSE_SESSION. -/
  | closeReceived (code : Nat) (message : List UInt8)
  /-- The peer cleanly finishes the CONNECT stream (FIN) without WT_CLOSE_SESSION. -/
  | finReceived
  /-- The CONNECT stream is reset (either side). -/
  | connectReset
  /-- More bytes arrive on the CONNECT stream. -/
  | connectData
  deriving DecidableEq, Repr

/-- What the endpoint must do. -/
inductive Action where
  /-- Reset the send side and abort reading of every stream of the session with
  WT_SESSION_GONE (§6). -/
  | resetStreams (e : ErrorCode)
  /-- Send a FIN on the CONNECT stream (after sending WT_CLOSE_SESSION, §6). -/
  | finConnect
  /-- Close or reset the CONNECT stream in response to a received WT_CLOSE_SESSION (§6). -/
  | closeConnect
  /-- Reset the CONNECT stream with this HTTP/3 error code. -/
  | resetConnect (e : Http3.ErrorCode)
  deriving DecidableEq, Repr

namespace SessionState

/-- Terminated (§6). -/
def isClosed : SessionState → Bool
  | .closed _ => true
  | _ => false

/-- New streams may be opened and datagrams sent (§4, §4.7, §6). -/
def canOpenStream (s : SessionState) : Bool := !s.isClosed

def canSendDatagram (s : SessionState) : Bool := !s.isClosed

/-- The CONNECT stream's bytes are processed as capsules (§3.2). -/
def processesCapsules : SessionState → Bool
  | .established | .draining => true
  | _ => false

/-- The actions of learning that the session has terminated (§6). -/
def terminate : List Action := [.resetStreams .sessionGone]

/-- One transition. -/
def step : SessionState → SessionEvent → SessionState × List Action
  | .closed r, .connectData => (.closed r, [.resetConnect .messageError])
  | .closed r, _ => (.closed r, [])
  | .establishing, .response status =>
    if 200 ≤ status && status < 300 then (.established, [])
    else (.closed (.rejected status), terminate)
  | s, .response _ => (s, [])
  | .established, .drain => (.draining, [])
  | s, .drain => (s, [])
  | _, .closeSent code msg => (.closed (.closed code msg), .finConnect :: terminate)
  | _, .closeReceived code msg => (.closed (.closed code msg), .closeConnect :: terminate)
  | _, .finReceived => (.closed (.closed 0 []), .closeConnect :: terminate)
  | _, .connectReset => (.closed .aborted, terminate)
  | s, .connectData => (s, [])

/-- Run a sequence of events, collecting the actions. -/
def run : SessionState → List SessionEvent → SessionState × List Action
  | s, [] => (s, [])
  | s, e :: es =>
    let (s', as) := s.step e
    let (s'', bs) := s'.run es
    (s'', as ++ bs)

/-- The order of the phases: establishing < established < draining < closed. -/
def rank : SessionState → Nat
  | .establishing => 0
  | .established => 1
  | .draining => 2
  | .closed _ => 3

end SessionState

/-- A session: its ID (the CONNECT stream's) and state. -/
structure Session where
  id : Nat
  state : SessionState
  deriving DecidableEq, Repr

/-- The session a CONNECT stream starts, if the stream can carry one (§4). -/
def Session.ofConnect (connectStreamId : Nat) : Option Session :=
  if validSessionId connectStreamId then some ⟨connectStreamId, .establishing⟩ else none

/-! ## Data for a session (§4.6, §6) -/

/-- What to do with an incoming WebTransport stream whose header names a session. -/
inductive StreamDisposition where
  | accept
  /-- Hold it until the session is established (§4.6, SHOULD buffer). -/
  | buffer
  /-- Reset / STOP_SENDING with this code. -/
  | reject (e : ErrorCode)
  deriving DecidableEq, Repr

/-- An incoming stream for session state `s` (`none`: no such session yet), with `full` telling
whether the buffering limit is reached. Streams of a closed session are reset with
WT_SESSION_GONE (§6); streams that cannot be associated yet are buffered, and "When the number
of buffered streams is exceeded, a stream MUST be closed by sending a RESET_STREAM and/or
STOP_SENDING with the WT_BUFFERED_STREAM_REJECTED error code" (§4.6). -/
def incomingStream (s : Option SessionState) (full : Bool) : StreamDisposition :=
  match s with
  | some (.closed _) => .reject .sessionGone
  | some .established | some .draining => .accept
  | some .establishing | none => if full then .reject .bufferedStreamRejected else .buffer

/-- An incoming datagram for session state `s`: delivered, buffered, or dropped ("When the
number of buffered datagrams is exceeded, a datagram MUST be dropped", §4.6). `none` means
dropped. -/
def incomingDatagram (s : Option SessionState) (full : Bool) : Option StreamDisposition :=
  match s with
  | some (.closed _) => none
  | some .established | some .draining => some .accept
  | some .establishing | none => if full then none else some .buffer

end Silmaril.Net.WebTransport

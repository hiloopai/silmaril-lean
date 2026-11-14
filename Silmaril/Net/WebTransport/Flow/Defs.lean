module

public import Silmaril.Net.WebTransport.Capsule.Defs
public import Silmaril.Net.WebTransport.Establish.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: session-level flow control (draft-ietf-webtrans-http3-17 §5.3–§5.6)

Codepoints and rules are those of draft -17 (in WG Last Call, not an RFC).

A session has three limits, set by the receiving endpoint for its peer: the cumulative number
of bidirectional and of unidirectional streams the peer may open (WT_MAX_STREAMS, §5.6.2;
initially `SETTINGS_WT_INITIAL_MAX_STREAMS_BIDI/UNI`, §5.5.1–§5.5.2) and the total Stream Body
bytes it may send on all the session's streams (WT_MAX_DATA, §5.6.4; initially
`SETTINGS_WT_INITIAL_MAX_DATA`, §5.5.3). Stream headers and capsules do not count (§5.4).

* **Sender** (`SendState`): "An endpoint MUST NOT open more streams than permitted by the current
  stream limit set by its peer"; "The sum of the lengths of Stream Body data sent on all streams
  associated with this session MUST NOT exceed the Maximum Data value advertised by a receiver."
  `SendState.tryOpen` and `SendState.trySend` are the compliant sender: they act only within the
  limits (otherwise the sender is blocked, and may say so with WT_STREAMS_BLOCKED /
  WT_DATA_BLOCKED, `SendState.blockedStreams`, `SendState.blockedData`). On receipt of
  WT_MAX_STREAMS or WT_MAX_DATA: "If an endpoint receives a WT_MAX_STREAMS capsule that does not
  increase the Maximum Streams value previously received, or the corresponding initial value …
  it MUST close the WebTransport session with a WT_FLOW_CONTROL_ERROR error code" (and likewise
  for WT_MAX_DATA): `SendState.onCapsule`.
* **Receiver** (`RecvState`): "If an endpoint receives an incoming stream for a session that would
  exceed the advertised Maximum Streams value, it MUST close the WebTransport session with a
  WT_FLOW_CONTROL_ERROR error code"; "If an endpoint receives Stream Body data in excess of this
  limit, it MUST close the WebTransport session with a WT_FLOW_CONTROL_ERROR error code."
  (`RecvState.onOpen`, `RecvState.onData`.) It raises its limits only upward
  (`RecvState.raiseStreams`, `RecvState.raiseData`), and never above `2^60` streams.
* "If flow control is not enabled, an endpoint MUST ignore receipt of any flow control capsules"
  (§5.1): `SendState.onCapsuleIf`.

`System` is a lockstep model of one direction of a session: each stream opening, each byte of
Stream Body and each limit capsule is applied at both ends in the same step (WT_MAX_* capsules
travel in order on the CONNECT stream; the model abstracts away their delay). The single-step
theorems in `Thms` state acceptance for any sender view *below* the receiver's limits, which is
what remains true while capsules are in flight.

**Assumed (abstract).** QUIC's own stream and connection flow control (RFC 9000 §4), final sizes
of reset streams (§5.4 relies on RFC 9000 §4.5), and the closing of streams.
-/

namespace Silmaril.Net.WebTransport

/-- The session limits one endpoint grants its peer. -/
structure Limits where
  maxStreamsBidi : Nat
  maxStreamsUni : Nat
  maxData : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Limits

/-- The initial limits announced by an endpoint's SETTINGS (§5.5). -/
def ofSettings (s : WtSettings) : Limits :=
  ⟨s.initialMaxStreamsBidi, s.initialMaxStreamsUni, s.initialMaxData⟩

def streams (l : Limits) : Dir → Nat
  | .bidi => l.maxStreamsBidi
  | .uni => l.maxStreamsUni

def setStreams (l : Limits) : Dir → Nat → Limits
  | .bidi, n => { l with maxStreamsBidi := n }
  | .uni, n => { l with maxStreamsUni := n }

/-- Every limit of `a` is at most that of `b`. -/
def Le (a b : Limits) : Prop :=
  a.maxStreamsBidi ≤ b.maxStreamsBidi ∧ a.maxStreamsUni ≤ b.maxStreamsUni ∧ a.maxData ≤ b.maxData

end Limits

/-- What a sender has used: streams opened (including closed ones) and Stream Body bytes. -/
structure Usage where
  openedBidi : Nat := 0
  openedUni : Nat := 0
  dataBytes : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Usage

def opened (u : Usage) : Dir → Nat
  | .bidi => u.openedBidi
  | .uni => u.openedUni

def openOne (u : Usage) : Dir → Usage
  | .bidi => { u with openedBidi := u.openedBidi + 1 }
  | .uni => { u with openedUni := u.openedUni + 1 }

def addData (u : Usage) (n : Nat) : Usage := { u with dataBytes := u.dataBytes + n }

/-- Usage within limits. -/
def Within (u : Usage) (l : Limits) : Prop :=
  u.openedBidi ≤ l.maxStreamsBidi ∧ u.openedUni ≤ l.maxStreamsUni ∧ u.dataBytes ≤ l.maxData

end Usage

/-! ## The sender -/

/-- The sender's state: the limits its peer has granted and what it has used. -/
structure SendState where
  limits : Limits
  used : Usage := {}
  deriving DecidableEq, Repr, Inhabited

namespace SendState

/-- Open a stream if the limit allows it (`none`: blocked). -/
def tryOpen (s : SendState) (d : Dir) : Option SendState :=
  if s.used.opened d < s.limits.streams d then some { s with used := s.used.openOne d } else none

/-- Send `n` Stream Body bytes if the limit allows it (`none`: blocked). -/
def trySend (s : SendState) (n : Nat) : Option SendState :=
  if s.used.dataBytes + n ≤ s.limits.maxData then some { s with used := s.used.addData n }
  else none

/-- WT_STREAMS_BLOCKED, carrying the limit at which the sender is blocked (§5.6.3). -/
def blockedStreams (s : SendState) (d : Dir) : WtCapsule := .streamsBlocked d (s.limits.streams d)

/-- WT_DATA_BLOCKED, carrying the limit at which the sender is blocked (§5.6.5). -/
def blockedData (s : SendState) : WtCapsule := .dataBlocked s.limits.maxData

/-- Apply a capsule received on the CONNECT stream. Limits must strictly increase (§5.6.2,
§5.6.4); other capsules do not concern the sender's limits. -/
def onCapsule (s : SendState) : WtCapsule → Except ErrorCode SendState
  | .maxStreams d n =>
    if maxStreamsLimit < n || n ≤ s.limits.streams d then .error .flowControlError
    else .ok { s with limits := s.limits.setStreams d n }
  | .maxData n =>
    if n ≤ s.limits.maxData then .error .flowControlError
    else .ok { s with limits := { s.limits with maxData := n } }
  | _ => .ok s

/-- §5.1: without flow control, flow control capsules are ignored. -/
def onCapsuleIf (enabled : Bool) (s : SendState) (c : WtCapsule) : Except ErrorCode SendState :=
  if enabled then s.onCapsule c else .ok s

end SendState

/-! ## The receiver -/

/-- The receiver's state: the limits it has granted and what its peer has used. -/
structure RecvState where
  limits : Limits
  used : Usage := {}
  deriving DecidableEq, Repr, Inhabited

namespace RecvState

/-- An incoming stream of the session. -/
def onOpen (r : RecvState) (d : Dir) : Except ErrorCode RecvState :=
  if r.limits.streams d < r.used.opened d + 1 then .error .flowControlError
  else .ok { r with used := r.used.openOne d }

/-- `n` incoming Stream Body bytes. -/
def onData (r : RecvState) (n : Nat) : Except ErrorCode RecvState :=
  if r.limits.maxData < r.used.dataBytes + n then .error .flowControlError
  else .ok { r with used := r.used.addData n }

/-- Raise the stream limit to `n` and send WT_MAX_STREAMS; `none` if that would not increase it
or would exceed `2^60`. -/
def raiseStreams (r : RecvState) (d : Dir) (n : Nat) : Option (RecvState × WtCapsule) :=
  if r.limits.streams d < n && n ≤ maxStreamsLimit then
    some ({ r with limits := r.limits.setStreams d n }, .maxStreams d n)
  else none

/-- Raise the data limit to `n` and send WT_MAX_DATA; `none` if that would not increase it. -/
def raiseData (r : RecvState) (n : Nat) : Option (RecvState × WtCapsule) :=
  if r.limits.maxData < n then some ({ r with limits := { r.limits with maxData := n } }, .maxData n)
  else none

end RecvState

/-! ## Lockstep model of one direction -/

/-- A sender (the peer that opens streams and sends data) and the receiver that grants limits. -/
structure System where
  send : SendState
  recv : RecvState
  deriving DecidableEq, Repr

/-- The events of a session direction. -/
inductive Event where
  /-- The sender wants to open a stream. -/
  | open_ (d : Dir)
  /-- The sender wants to send `n` Stream Body bytes. -/
  | data (n : Nat)
  /-- The receiver raises a stream limit. -/
  | raiseStreams (d : Dir) (n : Nat)
  /-- The receiver raises the data limit. -/
  | raiseData (n : Nat)
  deriving DecidableEq, Repr

/-- One step with compliant endpoints: a blocked sender, or a receiver that cannot raise, does
nothing; otherwise both ends apply the step. -/
def System.step (S : System) : Event → Except ErrorCode System
  | .open_ d =>
    match S.send.tryOpen d with
    | none => .ok S
    | some s' => (S.recv.onOpen d).map fun r' => ⟨s', r'⟩
  | .data n =>
    match S.send.trySend n with
    | none => .ok S
    | some s' => (S.recv.onData n).map fun r' => ⟨s', r'⟩
  | .raiseStreams d n =>
    match S.recv.raiseStreams d n with
    | none => .ok S
    | some (r', c) => (S.send.onCapsule c).map fun s' => ⟨s', r'⟩
  | .raiseData n =>
    match S.recv.raiseData n with
    | none => .ok S
    | some (r', c) => (S.send.onCapsule c).map fun s' => ⟨s', r'⟩

/-- Run events in order, stopping at the first error. -/
def System.run (S : System) : List Event → Except ErrorCode System
  | [] => .ok S
  | e :: es =>
    match S.step e with
    | .error err => .error err
    | .ok S' => S'.run es

/-- The ends agree, and usage is within limits. -/
def System.Inv (S : System) : Prop :=
  S.send.limits = S.recv.limits ∧ S.send.used = S.recv.used ∧ S.send.used.Within S.send.limits

/-- The start of a session: both ends know the initial limits from the receiver's SETTINGS. -/
def System.init (receiverSettings : WtSettings) : System :=
  ⟨{ limits := Limits.ofSettings receiverSettings }, { limits := Limits.ofSettings receiverSettings }⟩

end Silmaril.Net.WebTransport

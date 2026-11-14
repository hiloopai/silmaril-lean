module

public import Silmaril.Net.Quic.StreamId.Defs
public import Silmaril.Net.Quic.Reassembly.Defs

@[expose] public section

/-!
# The QUIC stream service (RFC 9000 §2, §2.4, §3.5; RFC 9221 §5)

What an application protocol such as HTTP/3 may rely on from QUIC. RFC 9000 §2.4: "This
document does not define an API for QUIC; it instead defines a set of functions on streams
that application protocols can rely upon":

* "On the sending part of a stream, an application protocol can: write data …; end the
  stream (clean termination), resulting in a STREAM frame with the FIN bit set; and reset the
  stream (abrupt termination), resulting in a RESET_STREAM frame";
* "On the receiving part of a stream, an application protocol can: read data; and abort
  reading of the stream and request closure, possibly resulting in a STOP_SENDING frame";
* "An application protocol can also request to be informed of state changes on streams,
  including when the peer has opened or reset a stream, when a peer aborts reading on a
  stream, when new data is available".

**The specification.** `Half` is one direction of one stream as both applications see it: the
bytes `written` by the sending application, whether it ended (`fin`) or reset the stream
(`reset`, with an application error code, §20.2), the bytes `read` by the receiving
application, whether it saw the end (`eof`) or was told of the reset (`resetSeen`), and the
STOP_SENDING request (`stop`) and whether the sender was told of it (`stopSeen`). `HalfStep`
is the service: the receiver reads a nonempty continuation of what it read that is still a
prefix of what was written (*ordered, no loss before the read point, no duplication, no
invention*; how reads are chunked is free, §2.2 "STREAM frame boundaries are not expected to be
preserved"), end of stream only after FIN and everything read (*reliable*), and a reset or
stop signal only with the code the other side used.

`Conn` is a whole connection: a `Half` per stream id and sending role, the streams opened per
type (§2.1: ids in order, `StreamId.nth`), the peer's stream limits (§4.6), and datagrams
(RFC 9221). `ConnStep` admits an event on a half only if the stream is open and the role may
send on it (unidirectional streams only carry data from their initiator, §2.1). Datagrams are
*unreliable* (RFC 9221 §5): each received datagram was sent, and no datagram is received more
often than it was sent (`List.count`); loss and reordering are allowed.

**The assumption.** `StreamService` packages an implementation: a state space, an invariant,
the application-visible `view` into `Conn`, the operations `step`, and internal (network)
steps that the applications cannot see. Its fields `step_sound` and `internal_view` *are the
assumption* that the implementation provides the service: HTTP/3 developments take a
`StreamService` as a parameter, so every theorem about them is explicitly conditional on it.
Nothing here is an axiom. `Silmaril.Net.Quic.Service.Thms` proves that every reachable view
satisfies `Conn.Ok` (the safety properties above) and builds `reference`, an instance where
each half is a sender buffer plus a `RecvBuffer` (`Silmaril.Net.Quic.Reassembly`) fed by
internal `transmit` steps that deliver arbitrary slices of the written data, in any order and
any number of times, and where datagrams pass through a lossy, reordering network.

**Not modelled** (the reference instance abstracts them into the internal steps; real QUIC
implements them below this interface):

* packets, packet number spaces and packet number encoding (§12.3, §17.1), coalescing (§12.2),
  ACK generation and processing (§13.2), frame packetization (§13): the frame codec is in
  `Silmaril.Net.Quic.Frame`, but which frames go into which packet is not modelled;
* packet protection and header protection, the TLS handshake and key updates (RFC 9001);
* loss detection, retransmission timers, congestion control (RFC 9002), PMTU (§14);
* connection IDs, NEW_CONNECTION_ID/RETIRE_CONNECTION_ID semantics, address validation,
  path validation and migration (§5.1, §8, §9), stateless reset (§10.3);
* 0-RTT (§4.6.1 of RFC 9001, §7.4.1), version negotiation (§6), Retry (§17.2.5),
  transport parameters (§7.4, §18) other than as the initial `limit`s;
* connection termination: idle timeout, CONNECTION_CLOSE, draining (§10), and liveness in
  general: the service is a *safety* specification (nothing is promised to arrive).
  Flow-control credit (`Silmaril.Net.Quic.Flow`) and STOP_SENDING's obligation to reset
  (§3.5) are liveness-relevant and are not part of the service.
-/

namespace Silmaril.Net.Quic.Service

/-- Update a function at one point. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ## One direction of a stream -/

/-- One direction of one stream, as the two applications see it. -/
structure Half where
  written : List UInt8 := []
  fin : Bool := false
  reset : Option Nat := none
  read : List UInt8 := []
  eof : Bool := false
  resetSeen : Option Nat := none
  stop : Option Nat := none
  stopSeen : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Application-visible events on one direction. -/
inductive HalfEv where
  /-- The sender writes bytes. -/
  | write (bs : List UInt8)
  /-- The sender ends the stream (FIN). -/
  | finish
  /-- The sender resets the stream (RESET_STREAM) with an application error code. -/
  | reset (code : Nat)
  /-- The receiver reads bytes. -/
  | read (bs : List UInt8)
  /-- The receiver learns that the stream ended. -/
  | eof
  /-- The receiver learns that the stream was reset, with the sender's code. -/
  | resetSeen (code : Nat)
  /-- The receiver aborts reading (STOP_SENDING) with an application error code. -/
  | stopSending (code : Nat)
  /-- The sender learns of the STOP_SENDING, with the receiver's code. -/
  | stopSeen (code : Nat)
  deriving DecidableEq, Repr

/-- **The service on one direction of a stream.** -/
inductive HalfStep : Half → HalfEv → Half → Prop where
  | write {h : Half} (bs : List UInt8) : h.fin = false → h.reset = none →
      HalfStep h (.write bs) { h with written := h.written ++ bs }
  | finish {h : Half} : h.fin = false → h.reset = none → HalfStep h .finish { h with fin := true }
  | reset {h : Half} (c : Nat) : h.reset = none → HalfStep h (.reset c) { h with reset := some c }
  | read {h : Half} (bs : List UInt8) : bs ≠ [] → h.read ++ bs <+: h.written →
      HalfStep h (.read bs) { h with read := h.read ++ bs }
  | eof {h : Half} : h.fin = true → h.read = h.written → h.eof = false → h.resetSeen = none →
      HalfStep h .eof { h with eof := true }
  | resetSeen {h : Half} (c : Nat) : h.reset = some c → h.resetSeen = none → h.eof = false →
      HalfStep h (.resetSeen c) { h with resetSeen := some c }
  | stopSending {h : Half} (c : Nat) : h.stop = none →
      HalfStep h (.stopSending c) { h with stop := some c }
  | stopSeen {h : Half} (c : Nat) : h.stop = some c → h.stopSeen = none →
      HalfStep h (.stopSeen c) { h with stopSeen := some c }

/-- The safety invariant of one direction: what was read is a prefix of what was written; end
of stream means FIN and everything read; signals carry the other side's codes; a stream does
not both end and report a reset. -/
def Half.Ok (h : Half) : Prop :=
  h.read <+: h.written ∧ (h.eof = true → h.fin = true ∧ h.read = h.written) ∧
    (∀ c, h.resetSeen = some c → h.reset = some c) ∧
    (∀ c, h.stopSeen = some c → h.stop = some c) ∧ ¬ (h.eof = true ∧ h.resetSeen.isSome)

/-! ## A connection -/

/-- A connection as its two applications see it. -/
structure Conn where
  /-- `halves id r`: the direction of stream `id` in which endpoint `r` sends. -/
  halves : Nat → Role → Half := fun _ _ => {}
  /-- Streams opened per type (by the type's initiator). -/
  opened : StreamType → Nat := fun _ => 0
  /-- The stream limits granted by the peer of each type's initiator (§4.6). -/
  limit : StreamType → Nat
  /-- DATAGRAM support was negotiated (RFC 9221 §3). -/
  datagrams : Bool := false
  /-- Datagrams sent by each endpoint. -/
  dgSent : Role → List (List UInt8) := fun _ => []
  /-- Datagrams received by each endpoint. -/
  dgRecv : Role → List (List UInt8) := fun _ => []

/-- Stream `id` was opened. -/
def Conn.IsOpen (c : Conn) (id : Nat) : Prop := StreamId.index id < c.opened (StreamId.type id)

/-- Application-visible events of a connection. -/
inductive ConnEv where
  /-- The initiator of type `t` opens its next stream, `StreamId.nth t (opened t)`. -/
  | openStream (t : StreamType)
  /-- The peer raises the limit of type `t` (MAX_STREAMS). -/
  | raiseLimit (t : StreamType) (m : Nat)
  /-- An event on the direction of stream `id` in which `sender` sends. -/
  | half (id : Nat) (sender : Role) (e : HalfEv)
  /-- `sender` sends a datagram. -/
  | sendDatagram (sender : Role) (d : List UInt8)
  /-- `receiver` receives a datagram. -/
  | recvDatagram (receiver : Role) (d : List UInt8)
  deriving DecidableEq, Repr

/-- **The connection service.** -/
inductive ConnStep : Conn → ConnEv → Conn → Prop where
  | openStream {c : Conn} (t : StreamType) : c.opened t < c.limit t →
      ConnStep c (.openStream t) { c with opened := upd c.opened t (c.opened t + 1) }
  | raiseLimit {c : Conn} (t : StreamType) (m : Nat) : m ≤ maxStreamsLimit →
      ConnStep c (.raiseLimit t m) { c with limit := upd c.limit t (max (c.limit t) m) }
  | half {c : Conn} {h' : Half} (id : Nat) (r : Role) (e : HalfEv) : c.IsOpen id →
      StreamId.canSend r id = true → HalfStep (c.halves id r) e h' →
      ConnStep c (.half id r e) { c with halves := upd c.halves id (upd (c.halves id) r h') }
  | sendDatagram {c : Conn} (r : Role) (d : List UInt8) : c.datagrams = true →
      ConnStep c (.sendDatagram r d) { c with dgSent := upd c.dgSent r (c.dgSent r ++ [d]) }
  | recvDatagram {c : Conn} (r : Role) (d : List UInt8) :
      (c.dgRecv r ++ [d]).count d ≤ (c.dgSent r.peer).count d →
      ConnStep c (.recvDatagram r d) { c with dgRecv := upd c.dgRecv r (c.dgRecv r ++ [d]) }

/-- Runs of the connection service. -/
inductive ConnSteps : Conn → List ConnEv → Conn → Prop where
  | refl (c : Conn) : ConnSteps c [] c
  | cons {c c' c'' : Conn} {e : ConnEv} {es : List ConnEv} :
      ConnStep c e c' → ConnSteps c' es c'' → ConnSteps c (e :: es) c''

/-- The connection-level safety invariant. -/
def Conn.Ok (c : Conn) : Prop :=
  (∀ id r, (c.halves id r).Ok) ∧
    (∀ id r, (¬ c.IsOpen id ∨ StreamId.canSend r id = false) → c.halves id r = {}) ∧
    (∀ t, c.opened t ≤ c.limit t) ∧
    (∀ r d, (c.dgRecv r).count d ≤ (c.dgSent r.peer).count d)

/-- A fresh connection with the initial stream limits (transport parameters
`initial_max_streams_bidi/uni`, §18.2) and datagram support. -/
def Conn.initial (limit : StreamType → Nat) (datagrams : Bool) : Conn :=
  { limit := limit, datagrams := datagrams }

/-! ## The assumption: an implementation of the service -/

/-- **A QUIC implementation that provides the stream service.** The fields `step_sound` and
`internal_view` are the assumption HTTP/3 makes about QUIC: every application-visible step is
a `ConnStep`, and internal steps (packets, acknowledgements, retransmissions, …) are invisible.
-/
structure StreamService where
  State : Type
  init : State
  Inv : State → Prop
  view : State → Conn
  step : State → ConnEv → Option State
  internal : State → State → Prop
  init_inv : Inv init
  init_ok : (view init).Ok
  step_inv : ∀ {s e s'}, Inv s → step s e = some s' → Inv s'
  step_sound : ∀ {s e s'}, Inv s → step s e = some s' → ConnStep (view s) e (view s')
  internal_inv : ∀ {s s'}, Inv s → internal s s' → Inv s'
  internal_view : ∀ {s s'}, Inv s → internal s s' → view s' = view s

/-- The states an implementation reaches from its initial state. -/
inductive StreamService.Reachable (S : StreamService) : S.State → Prop where
  | init : S.Reachable S.init
  | step {s s' : S.State} {e : ConnEv} : S.Reachable s → S.step s e = some s' → S.Reachable s'
  | internal {s s' : S.State} : S.Reachable s → S.internal s s' → S.Reachable s'

/-! ## The reference implementation -/

/-- One direction implemented by a sender buffer and a reassembly buffer (`RecvBuffer`). -/
structure HalfImpl where
  written : List UInt8 := []
  fin : Bool := false
  reset : Option Nat := none
  buf : RecvBuffer := {}
  eof : Bool := false
  resetSeen : Option Nat := none
  stop : Option Nat := none
  stopSeen : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

namespace HalfImpl

/-- What the applications see: the receiver has read the delivered prefix. -/
def view (h : HalfImpl) : Half :=
  { written := h.written, fin := h.fin, reset := h.reset,
    read := (contiguous h.buf.segs).take h.buf.delivered, eof := h.eof,
    resetSeen := h.resetSeen, stop := h.stop, stopSeen := h.stopSeen }

/-- Application operations; `read bs` succeeds when `bs` is exactly the newly deliverable data. -/
def step (h : HalfImpl) : HalfEv → Option HalfImpl
  | .write bs => if h.fin = false ∧ h.reset = none then some { h with written := h.written ++ bs }
      else none
  | .finish => if h.fin = false ∧ h.reset = none then some { h with fin := true } else none
  | .reset c => if h.reset = none then some { h with reset := some c } else none
  | .read bs => if bs ≠ [] ∧ h.buf.read.1 = bs then some { h with buf := h.buf.read.2 } else none
  | .eof =>
    if h.fin = true ∧ h.buf.delivered = h.written.length ∧ h.eof = false ∧ h.resetSeen = none
    then some { h with eof := true } else none
  | .resetSeen c =>
    if h.reset = some c ∧ h.resetSeen = none ∧ h.eof = false then
      some { h with resetSeen := some c }
    else none
  | .stopSending c => if h.stop = none then some { h with stop := some c } else none
  | .stopSeen c =>
    if h.stop = some c ∧ h.stopSeen = none then some { h with stopSeen := some c } else none

/-- The network delivers a STREAM frame with the written bytes `[off, off + len)` (in any order,
any number of times; lost frames are simply never delivered). -/
def transmit (h : HalfImpl) (off len : Nat) : Option HalfImpl :=
  if off ≤ h.written.length then
    match h.buf.insert false ⟨off, (h.written.drop off).take len⟩ with
    | .ok b => some { h with buf := b }
    | .error _ => none
  else none

/-- The implementation invariant: the receiver holds slices of what was written. -/
def Inv (h : HalfImpl) : Prop :=
  h.buf.SlicesOf h.written ∧ h.buf.delivered ≤ (contiguous h.buf.segs).length ∧
    (∀ c, h.resetSeen = some c → h.reset = some c) ∧
    (∀ c, h.stopSeen = some c → h.stop = some c) ∧
    (h.eof = true → h.fin = true ∧ h.buf.delivered = h.written.length) ∧
    ¬ (h.eof = true ∧ h.resetSeen.isSome)

end HalfImpl

/-- The reference connection: `HalfImpl` per direction, and a lossy, reordering datagram network
(`inFlight r`: datagrams sent by `r` not yet delivered or lost). -/
structure ConnImpl where
  halves : Nat → Role → HalfImpl := fun _ _ => {}
  opened : StreamType → Nat := fun _ => 0
  limit : StreamType → Nat
  datagrams : Bool := false
  dgSent : Role → List (List UInt8) := fun _ => []
  dgRecv : Role → List (List UInt8) := fun _ => []
  inFlight : Role → List (List UInt8) := fun _ => []

namespace ConnImpl

/-- What the applications see. -/
def view (c : ConnImpl) : Conn :=
  { halves := fun id r => (c.halves id r).view, opened := c.opened, limit := c.limit,
    datagrams := c.datagrams, dgSent := c.dgSent, dgRecv := c.dgRecv }

/-- Stream `id` was opened. -/
def IsOpen (c : ConnImpl) (id : Nat) : Prop := StreamId.index id < c.opened (StreamId.type id)

instance (c : ConnImpl) (id : Nat) : Decidable (c.IsOpen id) := by
  unfold IsOpen; infer_instance

/-- Application operations. -/
def step (c : ConnImpl) : ConnEv → Option ConnImpl
  | .openStream t =>
    if c.opened t < c.limit t then some { c with opened := upd c.opened t (c.opened t + 1) }
    else none
  | .raiseLimit t m =>
    if m ≤ maxStreamsLimit then some { c with limit := upd c.limit t (max (c.limit t) m) }
    else none
  | .half id r e =>
    if c.IsOpen id ∧ StreamId.canSend r id = true then
      ((c.halves id r).step e).map fun h' =>
        { c with halves := upd c.halves id (upd (c.halves id) r h') }
    else none
  | .sendDatagram r d =>
    if c.datagrams = true then
      some { c with dgSent := upd c.dgSent r (c.dgSent r ++ [d]),
                    inFlight := upd c.inFlight r (c.inFlight r ++ [d]) }
    else none
  | .recvDatagram r d =>
    if d ∈ c.inFlight r.peer then
      some { c with dgRecv := upd c.dgRecv r (c.dgRecv r ++ [d]),
                    inFlight := upd c.inFlight r.peer ((c.inFlight r.peer).erase d) }
    else none

/-- Internal steps: the network delivers stream data, or loses a datagram. -/
inductive Internal : ConnImpl → ConnImpl → Prop where
  | transmit {c : ConnImpl} {h' : HalfImpl} (id : Nat) (r : Role) (off len : Nat) :
      (c.halves id r).transmit off len = some h' →
      Internal c { c with halves := upd c.halves id (upd (c.halves id) r h') }
  | lose {c : ConnImpl} (r : Role) (d : List UInt8) :
      Internal c { c with inFlight := upd c.inFlight r ((c.inFlight r).erase d) }

/-- The implementation invariant. -/
def Inv (c : ConnImpl) : Prop :=
  (∀ id r, (c.halves id r).Inv) ∧
    (∀ id r, (¬ c.IsOpen id ∨ StreamId.canSend r id = false) → (c.halves id r).view = {}) ∧
    (∀ t, c.opened t ≤ c.limit t) ∧
    (∀ r d, (c.dgRecv r).count d + (c.inFlight r.peer).count d ≤ (c.dgSent r.peer).count d)

/-- A fresh connection. -/
def initial (limit : StreamType → Nat) (datagrams : Bool) : ConnImpl :=
  { limit := limit, datagrams := datagrams }

end ConnImpl

end Silmaril.Net.Quic.Service

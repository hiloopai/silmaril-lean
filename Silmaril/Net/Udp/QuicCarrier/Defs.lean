module

public import Silmaril.Net.Udp.Network.Defs
public import Silmaril.Net.Quic.Service.Defs
public import Silmaril.Net.Http3.Datagram.Defs

/-!
# QUIC DATAGRAM frames over UDP: a conditional carrier and what it does not cover

The QUIC stream service (`Silmaril.Net.Quic.Service`) is the interface HTTP/3 relies on; its
reference implementation abstracts packets, packet protection, the TLS handshake and loss
recovery into internal steps. So main has **no** refinement from UDP to the QUIC stream service,
and this module does not claim one. It does three bounded things.

**1. The datagram slice, concretely.** RFC 9221 DATAGRAM frames are the part of QUIC whose
delivery guarantee is weak enough to state directly over UDP: "DATAGRAM frames are not
retransmitted" (§5), and the QUIC service (`ConnStep.recvDatagram`) promises only that no
datagram is received more often than it was sent. Two mechanisms give this over a network that
duplicates, reorders, loses, and lets anyone inject datagrams:

* *packet numbers*: the sender numbers packets in order (`St.next`); the receiver discards a
  packet whose number it has already processed (RFC 9000 §12.3: "A receiver MUST discard a newly
  unprotected packet unless it is certain that it has not processed another packet with the same
  packet number"). This removes the network's duplicates.
* *packet protection*: the receiver accepts only what opens under the connection's key
  (RFC 9001 §5). This removes forgeries, **if** the protection has integrity.

The carrier (`appTrace`) is a deterministic transducer from the client application's sends
(`Ev.appSend d`) and whatever the server's UDP socket returns (`Ev.udpRecv m`, any message: a
copy, a duplicate, a forgery, garbage) to the application-visible events of the QUIC service
(`ConnEv.sendDatagram .client d`, `ConnEv.recvDatagram .server d`). The sender's UDP output is
`wireTrace`. Unrecognized and malformed datagrams (`unprotect` fails), forged packets and duplicates
produce no application event.

**2. Cryptography as a parameter.** `Protection` is an abstract protect/unprotect pair: QUIC packet
protection (an AEAD with header protection, keys from the TLS handshake carried inside QUIC's
CRYPTO frames, RFC 9001), DTLS records (RFC 9147), or nothing. Two separate hypotheses are
named, never assumed: `Protection.Correct` (functional: unprotect inverts protect) and `Hon` (the
integrity of one run: every received payload that unprotects opens to a packet the sender protected
earlier). `Hon` is the idealized, per-run reading of INT-CTXT; it is a hypothesis of the
theorems, and no computational claim (probabilities, adversary resources) is made. Without
off-path packets `Hon` follows from `Correct` (`QuicCarrier.Thms.hon_of_replay`); with them, it
is exactly what the cryptography must supply, and `Protection.none` (no protection, as plain
UDP) fails it (`QuicCarrier.Thms.none_forgery`).

**3. HTTP/3 datagrams on top.** RFC 9297 HTTP/3 datagrams are QUIC datagrams whose payload is
`Http3.Datagram.encode`. `QuicCarrier.Thms.h3_received_subperm` composes: under `Hon`, the HTTP/3
datagrams the server decodes are a sub-multiset of those the client sent.

**Inclusion directions.** `QuicCarrier.Thms.carrier_sound` is *at most* (soundness, trace
inclusion of the implementation into the abstraction): every application trace of the carrier
under `Hon` is a run of the QUIC connection service. *At least* (every service run is produced
by some network behaviour) is not proved here.

**Missing bridges** (not stated, not assumed):

* QUIC streams over UDP: STREAM frames, ACKs, retransmission and loss recovery (RFC 9002), flow
  control. A theorem "a QUIC implementation over `Udp.Network` provides `StreamService`" needs
  these; HTTP/3 developments keep taking `StreamService` as a parameter.
* Packets proper: packet number spaces, encoding and truncation, long/short headers,
  coalescing, connection IDs and demultiplexing by connection ID, version negotiation, Retry,
  stateless reset, migration; the source address is not checked here, as QUIC permits migration.
* The handshake: `Protection`'s key is given, not derived; 0-RTT replay is not modelled.
* Server-to-client datagrams: the mirror image of this slice, not instantiated.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Net.Udp.QuicCarrier

open Silmaril.Net.Ip
open Silmaril.Net.Quic Silmaril.Net.Quic.Service Silmaril.Net.Udp.Network

/-- A protected packet as this slice sees it: a packet number and one DATAGRAM frame's
payload. -/
structure Pkt where
  pn : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

/-- **Packet protection, as a parameter**: protect a packet under a key, unprotect a UDP payload. -/
structure Protection where
  Key : Type
  protect : Key → Pkt → List UInt8
  unprotect : Key → List UInt8 → Option Pkt

/-- Functional correctness: unprotection a protected packet gives it back. -/
def Protection.Correct (P : Protection) : Prop := ∀ k p, P.unprotect k (P.protect k p) = some p

/-- Integrity for one payload: if it unprotects under `k`, it opens to a packet in `sent`. -/
def Protection.OpensTo (P : Protection) (k : P.Key) (sent : List Pkt) (c : List UInt8) : Prop :=
  ∀ p, P.unprotect k c = some p → p ∈ sent

/-- **No protection**, as plain UDP: one octet of packet number, then the payload. Anyone can
produce a payload that unprotects. -/
def Protection.none : Protection where
  Key := Unit
  protect _ p := p.pn.toUInt8 :: p.payload
  unprotect _ c := match c with
    | b :: rest => some ⟨b.toNat, rest⟩
    | [] => Option.none

/-- Carrier inputs: the client application sends a datagram, or the server's UDP socket returns
a message. -/
inductive Ev where
  | appSend (d : List UInt8)
  | udpRecv (m : Msg)
  deriving DecidableEq, Repr

/-- The carrier's state: the sender's next packet number and the packets it protected, the
receiver's processed packet numbers and the packets it accepted. -/
structure St where
  next : Nat := 0
  sent : List Pkt := []
  seen : List Nat := []
  accepted : List Pkt := []
  deriving DecidableEq, Repr

/-- The sender protects the next packet. -/
def St.send (s : St) (d : List UInt8) : St :=
  { s with next := s.next + 1, sent := s.sent ++ [⟨s.next, d⟩] }

/-- What the receiver accepts from a UDP payload: a packet that unprotects and whose number it has
not processed. -/
def St.accept? (P : Protection) (k : P.Key) (s : St) (c : List UInt8) : Option Pkt :=
  match P.unprotect k c with
  | some p => if p.pn ∈ s.seen then Option.none else some p
  | Option.none => Option.none

/-- The receiver records an accepted packet. -/
def St.deliver (s : St) (p : Pkt) : St :=
  { s with seen := s.seen ++ [p.pn], accepted := s.accepted ++ [p] }

/-- The state after one input. -/
def St.step (P : Protection) (k : P.Key) (s : St) : Ev → St
  | .appSend d => s.send d
  | .udpRecv m => match s.accept? P k m.data with
    | some p => s.deliver p
    | Option.none => s

/-- The state after a run. -/
def St.run (P : Protection) (k : P.Key) (s : St) (es : List Ev) : St := es.foldl (St.step P k) s

/-- **The application-visible trace** of a run: QUIC service events. -/
def appTrace (P : Protection) (k : P.Key) : St → List Ev → List ConnEv
  | _, [] => []
  | s, .appSend d :: es => .sendDatagram .client d :: appTrace P k (s.send d) es
  | s, .udpRecv m :: es => match s.accept? P k m.data with
    | some p => .recvDatagram .server p.payload :: appTrace P k (s.deliver p) es
    | Option.none => appTrace P k s es

/-- **The sender's UDP output** of a run, from the client endpoint `cli` to the server endpoint
`srv`. -/
def wireTrace (P : Protection) (k : P.Key) (cli srv : Endpoint) : St → List Ev → List Obs
  | _, [] => []
  | s, .appSend d :: es =>
      .send (Msg.mk' cli srv (P.protect k ⟨s.next, d⟩)) :: wireTrace P k cli srv (s.send d) es
  | s, .udpRecv m :: es => wireTrace P k cli srv (s.step P k (.udpRecv m)) es

/-- **Integrity of a run** (the cryptographic hypothesis): every UDP payload the server
receives opens, if at all, to a packet the sender protected before. -/
def Hon (P : Protection) (k : P.Key) : St → List Ev → Prop
  | _, [] => True
  | s, .appSend d :: es => Hon P k (s.send d) es
  | s, .udpRecv m :: es => P.OpensTo k s.sent m.data ∧ Hon P k (s.step P k (.udpRecv m)) es

/-- **No off-path packets** in a run: every UDP payload the server receives is the protection of
a packet the sender protected before (a copy the network delivered, possibly duplicated or out of
order). -/
def Replay (P : Protection) (k : P.Key) : St → List Ev → Prop
  | _, [] => True
  | s, .appSend d :: es => Replay P k (s.send d) es
  | s, .udpRecv m :: es => (∃ p ∈ s.sent, m.data = P.protect k p) ∧
      Replay P k (s.step P k (.udpRecv m)) es

/-- The datagrams the client application sent in a run. -/
def sentPayloads : List Ev → List (List UInt8)
  | [] => []
  | .appSend d :: es => d :: sentPayloads es
  | .udpRecv _ :: es => sentPayloads es

/-- The QUIC connection the carrier runs in: datagrams negotiated (RFC 9221 §3). -/
def conn0 (limit : StreamType → Nat) : Conn := Conn.initial limit true

/-! ## HTTP/3 datagrams -/

/-- The HTTP/3 datagrams a server decodes from QUIC datagram payloads (RFC 9297 §2.1); those
that fail to decode are connection errors (`H3_DATAGRAM_ERROR`) and yield no datagram. -/
def h3Decode (ds : List (List UInt8)) : List Http3.Datagram :=
  ds.filterMap fun d => (Http3.Datagram.decode d).toOption

end Silmaril.Net.Udp.QuicCarrier

module

public import Silmaril.Net.Udp.QuicCarrier.Defs
public import Silmaril.Net.Quic.Service.Thms
public import Batteries.Data.List.Perm
import Silmaril.Proofs.Net.Udp.QuicCarrier

/-!
# QUIC DATAGRAM frames over UDP: theorems

Proofs in `Silmaril/Proofs/Net/Udp/QuicCarrier.lean`, using only the standard axioms. Every
theorem that concludes something about received datagrams has the integrity of the run (`Hon`)
as an explicit hypothesis.

* **`carrier_sound`** (*at most*, conditional on `Hon`): the application-visible trace of the
  carrier is a run of the QUIC connection service (`Quic.Service.ConnSteps`) from a connection
  with datagrams negotiated, *whatever the UDP layer delivered* (duplicates, reorderings,
  losses, garbage, forgeries that do not unprotect). With `Quic.Service.Thms.connSteps_ok`, its
  final connection satisfies `Conn.Ok`: no datagram received more often than sent.
* `accepted_subperm`: under `Hon`, the payloads delivered are a sub-multiset of those sent.
* `hon_of_replay`: without off-path packets (every received payload is a copy of a protected
  packet sent earlier), `Hon` follows from functional correctness of the protection alone.
* **`none_forgery`**: without packet protection, a single off-path datagram makes the carrier
  deliver a datagram nobody sent, and that trace is *not* a run of the QUIC service. So
  `carrier_sound` cannot drop its hypothesis: the guarantee comes from cryptography, not UDP.
* `h3_received_subperm`: HTTP/3 datagrams (RFC 9297) composed on top: under `Hon`, the HTTP/3
  datagrams the server decodes are a sub-multiset of the valid ones the client sent.
* `malformed_silent`: a UDP payload that does not unprotect (unrecognized, malformed, wrong
  key) produces no application event and leaves the carrier's state unchanged.
-/

@[expose] public section

namespace Silmaril.Net.Udp.QuicCarrier

open Silmaril.Net.Quic Silmaril.Net.Quic.Service Silmaril.Net.Udp.Network

theorem carrier_sound (P : Protection) (k : P.Key) (limit : StreamType → Nat) (es : List Ev)
    (h : Hon P k {} es) : ∃ c', ConnSteps (conn0 limit) (appTrace P k {} es) c' :=
  Proofs.QuicCarrier.carrier_sound P k limit es h

/-- The connection after a carrier run satisfies the QUIC service's safety invariant. -/
theorem carrier_ok (P : Protection) (k : P.Key) (limit : StreamType → Nat) (es : List Ev)
    (h : Hon P k {} es) : ∃ c', ConnSteps (conn0 limit) (appTrace P k {} es) c' ∧ c'.Ok := by
  obtain ⟨c', hs⟩ := carrier_sound P k limit es h
  exact ⟨c', hs, connSteps_ok (Conn.initial_ok limit true) hs⟩

theorem accepted_subperm (P : Protection) (k : P.Key) (es : List Ev) (h : Hon P k {} es) :
    List.Subperm ((St.run P k {} es).accepted.map Pkt.payload)
      ((St.run P k {} es).sent.map Pkt.payload) :=
  Proofs.QuicCarrier.accepted_subperm P k es h

theorem run_sent (P : Protection) (k : P.Key) (es : List Ev) :
    (St.run P k {} es).sent.map Pkt.payload = sentPayloads es := by
  simpa using Proofs.QuicCarrier.run_sent P k es {}

theorem hon_of_replay (P : Protection) (k : P.Key) (hP : P.Correct) {s : St} {es : List Ev}
    (h : Replay P k s es) : Hon P k s es := Proofs.QuicCarrier.hon_of_replay P k hP es s h

theorem none_forgery (limit : StreamType → Nat) (cli srv : Endpoint) :
    appTrace Protection.none () {} [.udpRecv (Msg.mk' cli srv [0, 0x61])] =
        [.recvDatagram .server [0x61]] ∧
      ¬ ∃ c', ConnSteps (conn0 limit) [.recvDatagram .server [0x61]] c' :=
  Proofs.QuicCarrier.none_forgery limit cli srv

theorem h3_received_subperm (P : Protection) (k : P.Key) (es : List Ev) (h : Hon P k {} es)
    (hs : List Http3.Datagram) (hv : ∀ x ∈ hs, x.Valid)
    (hsent : sentPayloads es = hs.map Http3.Datagram.encode) :
    List.Subperm (h3Decode ((St.run P k {} es).accepted.map Pkt.payload)) hs :=
  Proofs.QuicCarrier.h3_received_subperm P k es h hs hv hsent

theorem malformed_silent (P : Protection) (k : P.Key) (s : St) (m : Msg) (es : List Ev)
    (hm : P.unprotect k m.data = none) :
    appTrace P k s (.udpRecv m :: es) = appTrace P k s es ∧ s.step P k (.udpRecv m) = s := by
  simp [appTrace, St.step, St.accept?, hm]

end Silmaril.Net.Udp.QuicCarrier

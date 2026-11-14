module

public import Silmaril.Servers.UdpTransport.Defs
public import Silmaril.Servers.Transport.Thms
public import Silmaril.Net.Udp.Network.Thms
import Silmaril.Proofs.Servers.UdpTransport.Basic

/-!
# UDP sockets read as transport traces: theorems

Proofs in `Silmaril/Proofs/Servers/UdpTransport/Basic.lean`, using only the standard axioms.

* **`unitsIn_flow`**: datagram boundaries are kept. The units received on the flow of peer `b`
  are exactly the data of the datagrams the socket received from `b`, one unit per datagram,
  in order. `stream_forgets` shows why `streamIn` is not a reading of UDP: two observation
  traces with different datagrams have the same `streamIn`.
* **`read_own`**: port isolation carries over. The reading depends only on the socket's own
  observations, so datagrams to other sockets cannot change what this server is seen doing
  (with `Net.Udp.Network.isolation` on the network side).
* **`flow_authentic`**: without off-path packets, every unit received on the flow of peer `b`
  is the data of a datagram that `b` actually sent to this socket. With off-path packets this
  fails (`Net.Udp.Inst.net_not_authentic`).
* `reading_total`, `model_mono`: the reading is total, so existential properties are reflected
  (`PMap.may_reflect_of_total`), and refinement of host configurations carries over to the
  transport models.
* `err_kept`: a refused send becomes `TEv.err` with the reading's code.
-/

@[expose] public section

namespace Silmaril.Servers.UdpTransport

open Silmaril.Net.Ip Silmaril.Net.Udp Silmaril.Net.Udp.Network Silmaril.Servers.Transport

theorem unitsIn_flow {a : Endpoint} (t : List Obs) (b : Endpoint)
    (hb : b ∈ peersFrom a [] none t) :
    unitsIn (flowOf a t b) (UdpTransport.read a t) = recvFrom a b t :=
  Proofs.UdpTransport.unitsIn_flow t b hb

theorem read_own (a : Endpoint) (t : List Obs) :
    UdpTransport.read a (t.filter (Obs.atSock a)) = UdpTransport.read a t :=
  Proofs.UdpTransport.read_own t

theorem flow_authentic {C : Config} (hC : C.offPath = false) {a : Endpoint} {t : List Obs}
    (ht : t ∈ traces C) (b : Endpoint) (hb : b ∈ peersFrom a [] none t) :
    ∀ bs ∈ unitsIn (flowOf a t b) (UdpTransport.read a t),
      ∃ m, Obs.send m ∈ t ∧ m.src = b ∧ m.dst = a ∧ m.data = bs :=
  Proofs.UdpTransport.flow_authentic hC ht b hb

theorem reading_total (a : Endpoint) (M : Set (List Obs)) : (reading a).Total M :=
  fun _ _ => rfl

theorem model_mono {C C' : Config} (a : Endpoint) (h : traces C ⊆ traces C') :
    (model C a).Refines (model C' a) := PMap.image_mono _ h

/-! ## Examples (kernel-checked) -/

/-- A client, `192.0.2.1:50000`, and the server socket, `192.0.2.2:443`. -/
def cli : Endpoint := ⟨.v4 ⟨192, 0, 2, 1⟩, 50000⟩
def srv : Endpoint := ⟨.v4 ⟨192, 0, 2, 2⟩, 443⟩

/-- Two datagrams `"A"`, `"B"` from the client: two units on flow 0. -/
theorem two_datagrams :
    UdpTransport.read srv [.recv srv (Msg.mk' cli srv [0x41]), .recv srv (Msg.mk' cli srv [0x42])] =
      [.bind 443, .open_ 443 0 cli, .recv 0 [0x41], .recv 0 [0x42]] := by decide

/-- `streamIn` forgets boundaries: one datagram `"AB"` reads as the same stream. -/
theorem stream_forgets :
    streamIn 0 (UdpTransport.read srv [.recv srv (Msg.mk' cli srv [0x41]),
        .recv srv (Msg.mk' cli srv [0x42])]) =
      streamIn 0 (UdpTransport.read srv [.recv srv (Msg.mk' cli srv [0x41, 0x42])]) ∧
    unitsIn 0 (UdpTransport.read srv [.recv srv (Msg.mk' cli srv [0x41]),
        .recv srv (Msg.mk' cli srv [0x42])]) ≠
      unitsIn 0 (UdpTransport.read srv [.recv srv (Msg.mk' cli srv [0x41, 0x42])]) := by decide

/-- A refused send (`ENOBUFS`) and a later ICMP refusal are both kept, on the flow of the send. -/
theorem err_kept :
    UdpTransport.read srv [.sendErr (Msg.mk' srv cli [0x41]) .noBufs,
        .send (Msg.mk' srv cli [0x42]), .err srv .refused] =
      [.bind 443, .open_ 443 0 cli, .err 0 105, .send 0 [0x42], .err 0 111] := by decide

end Silmaril.Servers.UdpTransport

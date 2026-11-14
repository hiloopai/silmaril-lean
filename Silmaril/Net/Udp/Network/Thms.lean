module

public import Silmaril.Net.Udp.Network.Defs
public import Silmaril.Net.Udp.Service.Thms
import Silmaril.Proofs.Net.Udp.Network

/-!
# UDP sockets over a packet network: theorems

Proofs in `Silmaril/Proofs/Net/Udp/Network.lean`, using only the standard axioms.

* **`traces_iff`** (exact, no off-path packets): the observable traces of the network are
  exactly the traces that keep the host rules (`Local`) and form a loose channel (`Spec`).
  *At most*: every run's observations satisfy `Spec` (loss, duplication and reordering never
  create a datagram). *At least*: every `Spec` trace is the observation of some run, so the
  specification asserts nothing the network does not deliver.
* **`traces_offPath_iff`** (exact, with off-path packets): the traces are exactly those that
  keep the host rules; the channel law is gone, because any well-formed datagram can arrive.
* `traces_service`: without off-path packets, the datagram events form the UDP service
  (`Udp.Service`).
* **`isolation`**, `recvAt_onlyTo`: port isolation as noninterference. Removing from a trace
  every datagram addressed to another endpoint leaves a trace, and the socket at `a` receives
  the same datagrams in it.
* `wire_malformed`: a packet that is not a valid UDP datagram (wrong protocol, truncated, bad
  checksum) is discarded with no effect on the network.
-/

@[expose] public section

namespace Silmaril.Net.Udp.Network

open Silmaril.Net.Ip Silmaril.Net.Channel

theorem traces_iff {C : Config} (hC : C.offPath = false) (t : List Obs) :
    t ∈ traces C ↔ Spec C t := Proofs.Network.traces_iff hC t

theorem traces_offPath_iff {C : Config} (hC : C.offPath = true) (t : List Obs) :
    t ∈ traces C ↔ ∀ o ∈ t, Local C o := Proofs.Network.traces_offPath_iff hC t

/-- Every trace keeps the host rules. -/
theorem traces_local {C : Config} {t : List Obs} (h : t ∈ traces C) : ∀ o ∈ t, Local C o :=
  Proofs.Network.traces_local h

/-- A trace that meets the specification is a trace, with or without off-path packets. -/
theorem mem_traces_of_spec {C : Config} {t : List Obs} (h : Spec C t) : t ∈ traces C :=
  Proofs.Network.mem_traces_of_spec h

theorem traces_service {C : Config} (hC : C.offPath = false) {t : List Obs}
    (h : t ∈ traces C) : Service (toChan t) := ((traces_iff hC t).mp h).2

theorem isolation {C : Config} {t : List Obs} (a : Endpoint) (h : t ∈ traces C) :
    onlyTo a t ∈ traces C := Proofs.Network.isolation a h

theorem recvAt_onlyTo {C : Config} {t : List Obs} (a : Endpoint) (h : t ∈ traces C) :
    recvAt a (onlyTo a t) = recvAt a t :=
  Proofs.Network.recvAt_onlyTo a t (traces_local h)

theorem wire_malformed {C : Config} {s s' : State} {p : Packet} (h : Step C s (.wire p) s')
    (hp : Msg.ofPacket p = none) : s' = s := Proofs.Network.wire_malformed h hp

/-- What a receiver accepts from the wire is a well-formed message. -/
theorem ofPacket_wf {p : Packet} {m : Msg} (h : Msg.ofPacket p = some m) : m.WF :=
  Proofs.Network.ofPacket_wf h

end Silmaril.Net.Udp.Network

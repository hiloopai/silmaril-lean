module

public import Silmaril.Net.Udp.Service.Defs
public import Silmaril.Net.Udp.Header.Thms
public import Silmaril.Net.Channel.Thms

/-!
# UDP datagram service: theorems

PROVED (standard axioms):

* **`ofPacket_toPacket`**: the receiver accepts the packet a sender emits for a well-formed
  message, and recovers the message (header round trip, length, checksum test).
* **`udp_over_ip`**: UDP over a loose IP channel is the UDP service (`Service`); together with
  `overIp_sends`: a trace of sends of well-formed messages is seen by UDP as exactly those
  sends.
* `deliveredTo_sent`: what a socket receives was sent to its address, whole.
-/

@[expose] public section

namespace Silmaril.Net.Udp

open Silmaril.Net.Ip Silmaril.Net.Channel

/-- **The receiver accepts what the sender emits**, and recovers the message. -/
theorem ofPacket_toPacket (m : Msg) (hm : m.WF) : Msg.ofPacket m.toPacket = some m := by
  have hsome : (Datagram.seal m.srcIp m.dstIp m.datagram).isSome = true := by
    rw [Datagram.seal_some]
    simp [hm.1]
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp hsome
  have hf : d'.srcPort = m.srcPort ∧ d'.dstPort = m.dstPort ∧ d'.payload = m.data :=
    Datagram.seal_fields hd'
  have hwf : d'.WF := by
    show 8 + d'.payload.length < 65536
    rw [hf.2.2]; exact hm.2
  have hdec : Datagram.decode d'.encode = some d' := by
    have h := Datagram.decode_encode d' hwf []
    rwa [List.append_nil] at h
  have hok : Datagram.checksumOk m.srcIp m.dstIp d' = true := Datagram.seal_checksumOk hd'
  have hpkt : m.toPacket = ⟨m.srcIp, m.dstIp, protoUdp, d'.encode⟩ := by
    simp [Msg.toPacket, hd']
  rw [hpkt, Msg.ofPacket]
  simp only [↓reduceIte, hdec, hok]
  rw [hf.1, hf.2.1, hf.2.2]

/-- **UDP over a loose IP channel is the UDP service.** -/
theorem udp_over_ip {tr : List (Ev Packet)} (h : Loose tr) : Service (overIp tr) :=
  loose_liftT Msg.ofPacket h

/-- Sends of well-formed messages, emitted as packets, are seen by UDP as those sends. -/
theorem overIp_sends (ms : List Msg) (hm : ∀ m ∈ ms, m.WF) :
    overIp (ms.map fun m => Ev.send m.toPacket) = ms.map Ev.send := by
  induction ms with
  | nil => rfl
  | cons m t ih =>
    have h1 : Msg.ofPacket m.toPacket = some m := ofPacket_toPacket m (hm m List.mem_cons_self)
    have h2 := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
    simp only [overIp, liftT, List.map_cons, List.filterMap_cons, Ev.lift, h1,
      Option.map_some] at h2 ⊢
    rw [h2]

/-- What a socket receives was sent to its address, whole. -/
theorem deliveredTo_sent {tr : List (Ev Msg)} (h : Service tr) (ip : IpAddr) (port : Port) :
    ∀ m ∈ deliveredTo ip port tr, m ∈ sent tr ∧ m.dstIp = ip ∧ m.dstPort = port := by
  intro m hm
  have hm' := List.mem_filter.mp hm
  have hd : m.dstIp = ip ∧ m.dstPort = port := by simpa using hm'.2
  exact ⟨loose_recv_sent h m hm'.1, hd⟩

end Silmaril.Net.Udp

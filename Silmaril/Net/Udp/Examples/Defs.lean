module

public import Silmaril.Net.Udp.Institution.Thms
public import Silmaril.Net.Udp.QuicCarrier.Thms
public meta import Silmaril.Net.Udp.QuicCarrier.Defs

/-!
# UDP, the UDP institution and the QUIC datagram carrier: examples

Three kinds of evidence, kept apart:

* **proofs** (`theorem`, checked by the kernel): concrete traces that are, or are not, traces of
  the network model; a concrete carrier run that satisfies the integrity hypothesis, hence is a
  run of the QUIC service;
* **computations** (`#guard`, evaluated by the compiled evaluator when the module is built, not
  by the kernel): what the carrier delivers and what it puts on the wire for a run where the
  network duplicates, reorders and injects garbage;
* **no runtime evidence on real sockets**: nothing here sends a packet. A host's UDP stack is
  a model of the institution's signature only if its traces are shown to be in `Network.traces`,
  which is not attempted.

Addresses are from the documentation ranges (RFC 5737).
-/

@[expose] public section

namespace Silmaril.Net.Udp.Examples

open Silmaril.Net.Ip Silmaril.Net.Udp.Network Silmaril.Net.Udp.QuicCarrier
open Silmaril.Net.Quic Silmaril.Net.Quic.Service

/-- A client socket, `192.0.2.1:50000`. -/
def cli : Endpoint := ⟨.v4 ⟨192, 0, 2, 1⟩, 50000⟩

/-- The server's QUIC socket, `192.0.2.2:443`. -/
def srv : Endpoint := ⟨.v4 ⟨192, 0, 2, 2⟩, 443⟩

/-- Another socket on the server host, `192.0.2.2:53`. -/
def dns : Endpoint := ⟨.v4 ⟨192, 0, 2, 2⟩, 53⟩

/-- The host configuration: the three sockets are bound; no off-path packets. -/
def C0 : Config := ⟨fun a => a == cli || a == srv || a == dns, false⟩

def m₁ : Msg := Msg.mk' cli srv [0x41]
def m₂ : Msg := Msg.mk' cli srv [0x42]
def mDns : Msg := Msg.mk' cli dns [0x00]

/-! ## Proofs: the network model -/

/-- The network may reorder and duplicate: `m₂` arrives before `m₁`, and `m₁` twice. -/
theorem reorder_dup_trace :
    [.send m₁, .send m₂, .recv srv m₂, .recv srv m₁, .recv srv m₁] ∈ traces C0 := by
  refine mem_traces_of_spec ⟨?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩
  · show Channel.okFrom [] [.send m₁, .send m₂, .recv m₂, .recv m₁, .recv m₁]
    simp [Channel.okFrom]

/-- The network may lose everything: sends and no receives. -/
theorem loss_trace : [.send m₁, .send m₂, .send mDns] ∈ traces C0 := by
  refine mem_traces_of_spec ⟨?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩
  · show Channel.okFrom [] [.send m₁, .send m₂, .send mDns]
    simp [Channel.okFrom]

/-- Port isolation: a datagram for port 53 is never received on the socket at port 443. -/
theorem isolated : [.send mDns, .recv srv mDns] ∉ traces C0 := by
  intro h
  have := (traces_local h) (.recv srv mDns) (by simp)
  exact absurd this.1 (by decide)

/-- Without off-path packets, nothing is received that was not sent. -/
theorem no_forgery : [.recv srv m₁] ∉ traces C0 := by
  intro h
  have := ((traces_iff rfl _).mp h).2
  simp [toChan, Obs.chan, Channel.Loose, Channel.okFrom] at this

/-- Removing the traffic to other ports keeps a trace (`isolation`). -/
theorem only_srv :
    onlyTo srv [.send m₁, .send mDns, .recv srv m₁] = [.send m₁, .recv srv m₁] := by decide

/-! ## Computations: the carrier over a misbehaving network -/

/-- The UDP payload of the client's packet number `pn` carrying `d`, without protection. -/
def wire (pn : Nat) (d : List UInt8) : List UInt8 := Protection.none.protect () ⟨pn, d⟩

/-- The client sends `"a"` and `"b"`; the network delivers `b`, then `a`, then `b` again, then
garbage (an empty payload, which does not unprotect). -/
def run1 : List QuicCarrier.Ev :=
  [.appSend [0x61], .appSend [0x62],
   .udpRecv (Msg.mk' cli srv (wire 1 [0x62])), .udpRecv (Msg.mk' cli srv (wire 0 [0x61])),
   .udpRecv (Msg.mk' cli srv (wire 1 [0x62])), .udpRecv (Msg.mk' cli srv [])]

-- The duplicate and the garbage produce nothing; the reordering is visible.
#guard appTrace Protection.none () {} run1 ==
  [.sendDatagram .client [0x61], .sendDatagram .client [0x62],
   .recvDatagram .server [0x62], .recvDatagram .server [0x61]]

-- The sender's UDP output: one datagram per application send, numbered in order.
#guard wireTrace Protection.none () cli srv {} run1 ==
  [.send (Msg.mk' cli srv [0, 0x61]), .send (Msg.mk' cli srv [1, 0x62])]

-- An off-path forgery is delivered when there is no protection (`none_forgery`).
#guard appTrace Protection.none () {} [.udpRecv (Msg.mk' dns srv [7, 0x7a])] ==
  [.recvDatagram .server [0x7a]]

/-! ## Proofs: the carrier run is a run of the QUIC service -/

/-- `run1` meets the integrity hypothesis: every payload received is a copy of one sent. -/
theorem run1_hon : Hon Protection.none () {} run1 := by
  simp [run1, Hon, Protection.OpensTo, Protection.none, wire, St.send, St.step, St.accept?,
    St.deliver, Msg.mk']

theorem run1_sound : ∃ c', ConnSteps (conn0 fun _ => 0) (appTrace Protection.none () {} run1) c' :=
  carrier_sound _ _ _ _ run1_hon

/-- HTTP/3 datagrams on request stream 4 (RFC 9297): the encoding is a Quarter Stream ID. -/
theorem h3_example : (Http3.Datagram.ofStream 4 [0x61]).encode = [0x01, 0x61] := by decide

end Silmaril.Net.Udp.Examples

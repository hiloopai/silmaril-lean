module

public import Silmaril.Net.Udp.Header.Defs
public import Silmaril.Net.Channel.Defs

/-!
# UDP: the datagram service

RFC 768 ("Introduction", "User Interface"): UDP provides "a procedure for application programs
to send messages to other programs with a minimum of protocol mechanism"; "delivery and
duplicate protection are not guaranteed". A receive returns "the data octets and an indication
of source port and source address".

* `Msg`: a UDP message as the service sees it: source and destination IP addresses and ports,
  and the data. `Msg.WF`: both addresses of one family, and the datagram length fits in 16
  bits (RFC 768 "Length").
* **`Service tr`**: the UDP service is the loose channel of `Channel` over messages: every
  datagram received was sent, whole (datagram boundaries are kept), and datagrams may be lost,
  duplicated and reordered.
* **UDP over IP**: `Msg.toPacket` is what a sender puts into an IP packet (protocol 17, the
  datagram sealed with its checksum), `Msg.ofPacket` what a receiver accepts: protocol 17, a
  datagram that decodes and passes the checksum test. `overIp tr` is the UDP view of an IP
  trace. `Udp.Service.Thms` proves that UDP over a loose IP channel is the UDP service, and that
  sent messages are received unchanged.
* `deliveredTo ip port tr`: the messages received at a local address, as a socket bound to it
  sees them.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md` and `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Udp

open Silmaril.Net.Ip Silmaril.Net.Channel

/-- **A UDP message**: addresses, ports and data (RFC 768 "User Interface"). -/
structure Msg where
  srcIp : IpAddr
  dstIp : IpAddr
  srcPort : Port
  dstPort : Port
  data : List UInt8
  deriving DecidableEq, Repr

/-- A message UDP can carry: one address family, and a length that fits in 16 bits. -/
def Msg.WF (m : Msg) : Prop := m.srcIp.family = m.dstIp.family ∧ 8 + m.data.length < 65536

/-- The datagram of a message, before its checksum is filled in. -/
def Msg.datagram (m : Msg) : Datagram := ⟨m.srcPort, m.dstPort, 0, m.data⟩

/-- **The IP packet a sender emits** for a message: protocol 17 and the sealed datagram. -/
def Msg.toPacket (m : Msg) : Packet :=
  ⟨m.srcIp, m.dstIp, protoUdp,
    ((Datagram.seal m.srcIp m.dstIp m.datagram).map Datagram.encode).getD []⟩

/-- **The message a receiver accepts** from an IP packet: protocol 17, a datagram that decodes
and passes the checksum test. Other packets are dropped. -/
def Msg.ofPacket (p : Packet) : Option Msg :=
  if p.proto = protoUdp then
    match Datagram.decode p.payload with
    | some d =>
        if Datagram.checksumOk p.src p.dst d then
          some ⟨p.src, p.dst, d.srcPort, d.dstPort, d.payload⟩
        else none
    | none => none
  else none

/-- **The UDP service**: the loose channel over messages. -/
def Service (tr : List (Ev Msg)) : Prop := Loose tr

/-- The UDP view of an IP trace: packets that are not valid UDP datagrams are dropped. -/
def overIp (tr : List (Ev Packet)) : List (Ev Msg) := liftT Msg.ofPacket tr

/-- The messages received at the local address `ip`, port `port`. -/
def deliveredTo (ip : IpAddr) (port : Port) (tr : List (Ev Msg)) : List Msg :=
  (received tr).filter fun m => m.dstIp == ip && m.dstPort == port

end Silmaril.Net.Udp

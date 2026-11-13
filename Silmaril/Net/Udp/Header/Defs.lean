module

public import Silmaril.Net.Ip.Addr.Defs
public import Silmaril.Net.Ip.Checksum.Defs

/-!
# UDP: header and datagram format (RFC 768)

RFC 768, "Format": a UDP datagram is an 8-octet header followed by data octets. The header has
four 16-bit fields in network byte order: Source Port, Destination Port, Length ("the length in
octets of this user datagram including this header and the data", so at least 8) and Checksum.

* `Header`, `Header.encode`, `Header.decode`: the four fields and their 8 octets.
* `Datagram`: ports, checksum field and payload; the Length field is not stored but computed
  (`Datagram.header`), so a `Datagram` cannot disagree with its own length. `Datagram.WF`:
  the length fits in 16 bits.
* `Datagram.decode l`: read a datagram from the octets `l` of an IP payload. It reads the
  header, requires `8 ≤ Length ≤ |l|` and takes `Length - 8` data octets; octets after
  `Length` are ignored (RFC 768 does not say what they are; they are not part of the datagram).
* **Checksum** (RFC 768 "Fields", RFC 8200 §8.1): computed over the pseudo-header
  (`Ip.pseudo`, protocol 17, the UDP length), the header with a zero checksum field and the
  data. `Datagram.seal src dst d` fills it in, transmitting a computed zero as `0xFFFF`.
  `Datagram.checksumOk src dst d`: the receiver's check; a zero field means "no checksum" and
  is accepted for IPv4 only (RFC 768; RFC 8200 §8.1: "IPv6 receivers must discard UDP packets
  containing a zero checksum").

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md` and `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Udp

open Silmaril.Net.Wire Silmaril.Net.Ip Silmaril.Net.Ip.Checksum

/-- **The UDP header** (RFC 768, "Format"). -/
structure Header where
  srcPort : Port
  dstPort : Port
  length : UInt16
  checksum : UInt16
  deriving DecidableEq, Repr, Inhabited

/-- The 8 octets of a header, in network byte order. -/
def Header.encode (h : Header) : List UInt8 :=
  be16 h.srcPort ++ be16 h.dstPort ++ be16 h.length ++ be16 h.checksum

/-- Read a header from the front of a list of octets. -/
def Header.decode : List UInt8 → Option (Header × List UInt8)
  | a :: b :: c :: d :: e :: f :: g :: h :: r =>
      some (⟨rd16 a b, rd16 c d, rd16 e f, rd16 g h⟩, r)
  | _ => none

/-- **A UDP datagram**: ports, the checksum field and the data. The Length field is computed. -/
structure Datagram where
  srcPort : Port
  dstPort : Port
  checksum : UInt16
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- The value of the Length field: header and data (RFC 768). -/
def Datagram.len (d : Datagram) : Nat := 8 + d.payload.length

/-- A datagram whose length fits in the 16-bit Length field. -/
def Datagram.WF (d : Datagram) : Prop := d.len < 65536

/-- The header of a datagram. -/
def Datagram.header (d : Datagram) : Header :=
  ⟨d.srcPort, d.dstPort, UInt16.ofNat d.len, d.checksum⟩

/-- The octets of a datagram. -/
def Datagram.encode (d : Datagram) : List UInt8 := d.header.encode ++ d.payload

/-- **Read a datagram** from the octets of an IP payload: a header, then `Length - 8` data
octets; later octets are ignored. -/
def Datagram.decode (l : List UInt8) : Option Datagram :=
  match Header.decode l with
  | some (h, r) =>
      if 8 ≤ h.length.toNat ∧ h.length.toNat - 8 ≤ r.length then
        some ⟨h.srcPort, h.dstPort, h.checksum, r.take (h.length.toNat - 8)⟩
      else none
  | none => none

/-- The octets the checksum covers: the pseudo-header, then the datagram with its checksum
field as given. `none` when the addresses are of different families. -/
def Datagram.covered (src dst : IpAddr) (d : Datagram) : Option (List UInt8) :=
  (pseudo src dst protoUdp d.len).map (· ++ d.encode)

/-- **Fill in the checksum** (RFC 768): computed with the field zeroed, a zero result sent as
`0xFFFF`. `none` when the addresses are of different families. -/
def Datagram.seal (src dst : IpAddr) (d : Datagram) : Option Datagram :=
  (Datagram.covered src dst { d with checksum := 0 }).map fun l =>
    { d with checksum := txUdp (Checksum.checksum l) }

/-- **The receiver's checksum test**: a zero field ("no checksum") is accepted over IPv4 only;
otherwise the covered octets must verify. -/
def Datagram.checksumOk (src dst : IpAddr) (d : Datagram) : Bool :=
  if d.checksum = 0 then src.family == .ipv4 && dst.family == .ipv4
  else match Datagram.covered src dst d with
    | some l => verify l
    | none => false

end Silmaril.Net.Udp

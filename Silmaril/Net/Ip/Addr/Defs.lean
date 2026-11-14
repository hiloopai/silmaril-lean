module

public import Silmaril.Net.Wire.Defs

/-!
# IP addresses, ports, socket addresses and the transport pseudo-header

Minimal Internet-layer addressing, as the transport protocols and WASI sockets use it:

* `Ipv4Addr`: four octets (RFC 791 §3.1, "Addressing": 32-bit addresses), the shape of WASI's
  `ipv4-address = tuple<u8, u8, u8, u8>` (`wasi:sockets/types`);
* `Ipv6Addr`: eight 16-bit pieces (RFC 4291 §2.2, the text form `x:x:x:x:x:x:x:x`; RFC 8200 §3
  for the 128-bit fields), the shape of WASI's `ipv6-address = tuple<u16 × 8>`;
* `IpAddr`, `Family`: either version, and its address family;
* `Port`: a 16-bit port (RFC 768 "Fields", RFC 9293 §3.1);
* `Endpoint`: a transport endpoint, an IP address and a port, without WASI's IPv6 flow and
  scope fields (shared by the UDP and TCP models and usable as `Servers.Transport`'s `Addr`);
* `SockAddr`: a socket address. Its IPv6 case carries the flow label and scope identifier as
  WASI's `ipv6-socket-address` record does (`flow-info`, `scope-id`); they are not on the wire
  of the transport protocols;
* special addresses: unspecified (`0.0.0.0`, RFC 1122 §3.2.1.3 (a); `::`, RFC 4291 §2.5.2),
  loopback (`127.0.0.0/8`, RFC 1122 §3.2.1.3 (g); `::1`, RFC 4291 §2.5.3) and IPv4-mapped IPv6
  addresses (`::ffff:a.b.c.d`, RFC 4291 §2.5.5.2);
* the octets of addresses in network byte order, and the **pseudo-headers** that the UDP and
  TCP checksums cover (RFC 768 "Fields", RFC 9293 §3.1 Figure 2 for IPv4; RFC 8200 §8.1 for
  IPv6).

Protocol numbers: TCP is 6 (RFC 9293 §3.1, the PTCL field), UDP is 17 (RFC 768, "Protocol
Number").

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`). Not modelled yet: the IP header itself,
fragmentation, routing, prefixes and the full special-purpose address registry.
-/

@[expose] public section

namespace Silmaril.Net.Ip

open Silmaril.Net.Wire

/-- An IPv4 address: four octets, most significant first (RFC 791 §3.1, "Addressing"). -/
structure Ipv4Addr where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- An IPv6 address: eight 16-bit pieces, most significant first (RFC 4291 §2.2). -/
structure Ipv6Addr where
  w0 : UInt16
  w1 : UInt16
  w2 : UInt16
  w3 : UInt16
  w4 : UInt16
  w5 : UInt16
  w6 : UInt16
  w7 : UInt16
  deriving DecidableEq, Repr, Inhabited

/-- An IP address of either version. -/
inductive IpAddr where
  | v4 (a : Ipv4Addr)
  | v6 (a : Ipv6Addr)
  deriving DecidableEq, Repr

/-- Address families (WASI's `ip-address-family`). -/
inductive Family where
  | ipv4
  | ipv6
  deriving DecidableEq, Repr

/-- A 16-bit transport port (RFC 768 "Fields", RFC 9293 §3.1). -/
abbrev Port : Type := UInt16

/-- **A transport endpoint**: an IP address and a port (RFC 768 "User Interface", RFC 9293
§3.1: a connection is named by a pair of these). -/
structure Endpoint where
  ip : IpAddr
  port : Port
  deriving DecidableEq, Repr

/-- A socket address: an IP address and a port; the IPv6 case also carries the flow
information and the scope identifier, as WASI's `ipv6-socket-address` does. -/
inductive SockAddr where
  | v4 (port : Port) (addr : Ipv4Addr)
  | v6 (port : Port) (flowInfo : UInt32) (addr : Ipv6Addr) (scopeId : UInt32)
  deriving DecidableEq, Repr

/-- The family of an address. -/
def IpAddr.family : IpAddr → Family
  | .v4 _ => .ipv4
  | .v6 _ => .ipv6

/-- The IP address of a socket address. -/
def SockAddr.ip : SockAddr → IpAddr
  | .v4 _ a => .v4 a
  | .v6 _ _ a _ => .v6 a

/-- The port of a socket address. -/
def SockAddr.port : SockAddr → Port
  | .v4 p _ => p
  | .v6 p _ _ _ => p

/-- The family of a socket address. -/
def SockAddr.family (s : SockAddr) : Family := s.ip.family

/-! ## Octets -/

/-- The four octets of an IPv4 address, in network byte order. -/
def Ipv4Addr.bytes (x : Ipv4Addr) : List UInt8 := [x.a, x.b, x.c, x.d]

/-- The sixteen octets of an IPv6 address, in network byte order. -/
def Ipv6Addr.bytes (x : Ipv6Addr) : List UInt8 :=
  be16 x.w0 ++ be16 x.w1 ++ be16 x.w2 ++ be16 x.w3 ++
  be16 x.w4 ++ be16 x.w5 ++ be16 x.w6 ++ be16 x.w7

/-- Read an IPv4 address from the front of a list of octets. -/
def Ipv4Addr.decode : List UInt8 → Option (Ipv4Addr × List UInt8)
  | a :: b :: c :: d :: r => some (⟨a, b, c, d⟩, r)
  | _ => none

/-- Read an IPv6 address from the front of a list of octets. -/
def Ipv6Addr.decode : List UInt8 → Option (Ipv6Addr × List UInt8)
  | a0 :: b0 :: a1 :: b1 :: a2 :: b2 :: a3 :: b3 ::
    a4 :: b4 :: a5 :: b5 :: a6 :: b6 :: a7 :: b7 :: r =>
      some (⟨rd16 a0 b0, rd16 a1 b1, rd16 a2 b2, rd16 a3 b3,
             rd16 a4 b4, rd16 a5 b5, rd16 a6 b6, rd16 a7 b7⟩, r)
  | _ => none

/-- The octets of an IP address. -/
def IpAddr.bytes : IpAddr → List UInt8
  | .v4 a => a.bytes
  | .v6 a => a.bytes

/-! ## Special addresses -/

/-- `0.0.0.0`: "this host on this network", used as an unspecified source
(RFC 1122 §3.2.1.3 (a)). -/
def Ipv4Addr.unspecified : Ipv4Addr := ⟨0, 0, 0, 0⟩

/-- `127.0.0.1`, the usual IPv4 loopback address. -/
def Ipv4Addr.localhost : Ipv4Addr := ⟨127, 0, 0, 1⟩

/-- An IPv4 loopback address: `127.0.0.0/8` (RFC 1122 §3.2.1.3 (g)). -/
def Ipv4Addr.isLoopback (x : Ipv4Addr) : Bool := x.a == 127

/-- `::`, the unspecified address (RFC 4291 §2.5.2). -/
def Ipv6Addr.unspecified : Ipv6Addr := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `::1`, the loopback address (RFC 4291 §2.5.3). -/
def Ipv6Addr.loopback : Ipv6Addr := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

/-- The IPv6 loopback test (RFC 4291 §2.5.3: exactly `::1`). -/
def Ipv6Addr.isLoopback (x : Ipv6Addr) : Bool := x == Ipv6Addr.loopback

/-- The unspecified address test of either version. -/
def IpAddr.isUnspecified : IpAddr → Bool
  | .v4 a => a == Ipv4Addr.unspecified
  | .v6 a => a == Ipv6Addr.unspecified

/-- The loopback test of either version. -/
def IpAddr.isLoopback : IpAddr → Bool
  | .v4 a => a.isLoopback
  | .v6 a => a.isLoopback

/-- **The IPv4-mapped IPv6 address** `::ffff:a.b.c.d` (RFC 4291 §2.5.5.2). -/
def Ipv4Addr.toMapped (x : Ipv4Addr) : Ipv6Addr :=
  ⟨0, 0, 0, 0, 0, 0xffff, rd16 x.a x.b, rd16 x.c x.d⟩

/-- The IPv4 address an IPv4-mapped IPv6 address carries, if it is one. -/
def Ipv6Addr.toMapped? (x : Ipv6Addr) : Option Ipv4Addr :=
  if x.w0 = 0 ∧ x.w1 = 0 ∧ x.w2 = 0 ∧ x.w3 = 0 ∧ x.w4 = 0 ∧ x.w5 = 0xffff then
    some ⟨UInt8.ofNat (x.w6.toNat / 256), UInt8.ofNat (x.w6.toNat % 256),
          UInt8.ofNat (x.w7.toNat / 256), UInt8.ofNat (x.w7.toNat % 256)⟩
  else none

/-! ## Pseudo-headers -/

/-- Protocol number of TCP (RFC 9293 §3.1, the PTCL field). -/
def protoTcp : UInt8 := 6

/-- Protocol number of UDP (RFC 768, "Protocol Number"). -/
def protoUdp : UInt8 := 17

/-- **The IPv4 pseudo-header** (RFC 768 "Fields"; RFC 9293 §3.1, Figure 2): source address,
destination address, a zero octet, the protocol and the transport length (12 octets). -/
def pseudo4 (src dst : Ipv4Addr) (proto : UInt8) (len : UInt16) : List UInt8 :=
  src.bytes ++ dst.bytes ++ [0, proto] ++ be16 len

/-- **The IPv6 pseudo-header** (RFC 8200 §8.1): source address, destination address, the
32-bit upper-layer packet length, three zero octets and the next-header value (40 octets). -/
def pseudo6 (src dst : Ipv6Addr) (nh : UInt8) (len : UInt32) : List UInt8 :=
  src.bytes ++ dst.bytes ++ be32 len ++ [0, 0, 0, nh]

/-- The pseudo-header of a pair of addresses of the same family; `none` for mixed families. -/
def pseudo (src dst : IpAddr) (proto : UInt8) (len : Nat) : Option (List UInt8) :=
  match src, dst with
  | .v4 s, .v4 d => some (pseudo4 s d proto (UInt16.ofNat len))
  | .v6 s, .v6 d => some (pseudo6 s d proto (UInt32.ofNat len))
  | _, _ => none

/-! ## Packets -/

/-- **An IP packet** as the transport layer sees it (RFC 791 §3.1 / RFC 8200 §3 abstracted):
source and destination addresses, the protocol number (IPv4 "Protocol", IPv6 "Next Header" of
the upper-layer header) and the upper-layer octets. Header fields that the transport layer does
not read (TTL, fragmentation, options, extension headers) are not modelled. -/
structure Packet where
  src : IpAddr
  dst : IpAddr
  proto : UInt8
  payload : List UInt8
  deriving DecidableEq, Repr

end Silmaril.Net.Ip

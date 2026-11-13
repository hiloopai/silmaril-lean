module

public import Silmaril.Wasi.Versions.Udp3Conn.Defs

@[expose] public section

/-!
# IP addresses and socket addresses, and their WASI encoding

A **pass-1 stand-in** for the minimal IP addressing of the `Net` region's transport layer
(`Silmaril.Net.Ip.*`, being written concurrently): when that lands, `IpAddr` and `SockAddr` are
replaced by its types and the decoding below is restated over them.

* IPv4 addresses (RFC 791 §3.1, 32 bits) as four octets in network order; IPv6 addresses
  (RFC 4291 §2.2, 128 bits) as eight 16-bit pieces in network order. This is the shape of
  the WASI `ipv4-address = tuple<u8, u8, u8, u8>` and `ipv6-address = tuple<u16 × 8>`
  (`specs/wasi/0.3.2/sockets/types.wit`; the same records in 0.2.12 `network.wit`).
* A socket address: an IP address and a port (RFC 768, RFC 9293 §3.1: 16-bit ports), plus
  for IPv6 the flow information and scope (RFC 3493 §3.3 `sin6_flowinfo`, `sin6_scope_id`),
  as in WASI `ipv4-socket-address`, `ipv6-socket-address`.
* `sockAddrOf` decodes a WASI `ip-socket-address` value, `sockAddrV` encodes one
  (round trip in `NetAddr.Thms`); `SockAddr.key` gives the numbers `Udp3Conn.akey` compares
  (`akey_eq`), so comparing decoded addresses is comparing `akey`s.
* The unspecified address (RFC 791 `0.0.0.0`, RFC 4291 §2.5.2 `::`) and a fully specified
  address (`full`: a nonzero address and port), which WASI `bind` and `connect` distinguish.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.NetAddr

open Silmaril.Wasm.Component (Val)

/-- An IP address. -/
inductive IpAddr where
  /-- IPv4 (RFC 791): four octets, most significant first. -/
  | v4 (a b c d : BitVec 8)
  /-- IPv6 (RFC 4291 §2.2): eight 16-bit pieces, most significant first. -/
  | v6 (a b c d e f g h : BitVec 16)
  deriving DecidableEq, Repr

/-- A socket address. -/
inductive SockAddr where
  /-- An IPv4 socket address. -/
  | v4 (port : BitVec 16) (ip : IpAddr)
  /-- An IPv6 socket address with flow information and scope. -/
  | v6 (port : BitVec 16) (flowInfo : BitVec 32) (ip : IpAddr) (scopeId : BitVec 32)
  deriving DecidableEq, Repr

/-- The pieces of an address as numbers. -/
def IpAddr.nums : IpAddr → List Nat
  | .v4 a b c d => [a.toNat, b.toNat, c.toNat, d.toNat]
  | .v6 a b c d e f g h =>
    [a.toNat, b.toNat, c.toNat, d.toNat, e.toNat, f.toNat, g.toNat, h.toNat]

/-- The unspecified address (`0.0.0.0`, `::`). -/
def IpAddr.isAny (ip : IpAddr) : Bool := ip.nums.all (· == 0)

/-- The family number of WASI `ip-address-family` (`ipv4 = 0`, `ipv6 = 1`). -/
def SockAddr.fam : SockAddr → Nat
  | .v4 .. => 0
  | .v6 .. => 1

/-- The port. -/
def SockAddr.port : SockAddr → BitVec 16
  | .v4 p _ => p
  | .v6 p _ _ _ => p

/-- The IP address. -/
def SockAddr.ip : SockAddr → IpAddr
  | .v4 _ ip => ip
  | .v6 _ _ ip _ => ip

/-- **A fully specified address**: a nonzero port and not the unspecified address. -/
def SockAddr.full (s : SockAddr) : Bool := s.port != 0 && !s.ip.isAny

/-! ## The WASI encoding -/

/-- A `u8` field. -/
def u8F : Val → Option (BitVec 8)
  | .u8 x => some x
  | _ => none

/-- A `u16` field. -/
def u16F : Val → Option (BitVec 16)
  | .u16 x => some x
  | _ => none

/-- Decode `ipv4-address`. -/
def ipv4Of : Val → Option IpAddr
  | .record [.u8 a, .u8 b, .u8 c, .u8 d] => some (.v4 a b c d)
  | _ => none

/-- Decode `ipv6-address`. -/
def ipv6Of : Val → Option IpAddr
  | .record [.u16 a, .u16 b, .u16 c, .u16 d, .u16 e, .u16 f, .u16 g, .u16 h] =>
    some (.v6 a b c d e f g h)
  | _ => none

/-- **Decode a WASI `ip-socket-address`.** An IPv4 socket address carries an IPv4 address and
an IPv6 one an IPv6 address. -/
def sockAddrOf : Val → Option SockAddr
  | .variant 0 (some (.record [.u16 port, ip])) => (ipv4Of ip).map (.v4 port)
  | .variant 1 (some (.record [.u16 port, .u32 fi, ip, .u32 sid])) =>
    (ipv6Of ip).map fun a => .v6 port fi a sid
  | _ => none

/-- Encode an IP address. -/
def ipV : IpAddr → Val
  | .v4 a b c d => .record [.u8 a, .u8 b, .u8 c, .u8 d]
  | .v6 a b c d e f g h => .record [.u16 a, .u16 b, .u16 c, .u16 d, .u16 e, .u16 f, .u16 g, .u16 h]

/-- **Encode a socket address** as a WASI `ip-socket-address`. Only the well-formed ones (an
IPv4 address in a `v4` socket address, IPv6 in `v6`) decode back. -/
def sockAddrV : SockAddr → Val
  | .v4 port ip => .variant 0 (some (.record [.u16 port, ipV ip]))
  | .v6 port fi ip sid => .variant 1 (some (.record [.u16 port, .u32 fi, ipV ip, .u32 sid]))

/-- The family matches the address. -/
def SockAddr.WF : SockAddr → Prop
  | .v4 _ (.v4 ..) => True
  | .v6 _ _ (.v6 ..) _ => True
  | _ => False

/-- The numbers `Udp3Conn.akey` compares. -/
def SockAddr.key : SockAddr → Udp3Conn.AKey
  | .v4 port ip => ⟨0, port.toNat, ip.nums, []⟩
  | .v6 port fi ip sid => ⟨1, port.toNat, ip.nums, [fi.toNat, sid.toNat]⟩

end Silmaril.Wasi.Versions.NetAddr

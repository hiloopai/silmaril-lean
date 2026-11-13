module

public import Silmaril.Net.Wire.Defs

/-!
# The Internet checksum

The UDP checksum (RFC 768, "Fields") and the TCP checksum (RFC 9293 §3.1, "Checksum") are
"the 16-bit one's complement of the one's complement sum" of the 16-bit words of a
pseudo-header, the transport header and the data, "padded with zero octets at the end (if
necessary) to make a multiple of two octets". RFC 1071 explains the computation.

Specification and algorithm:

* `wsum l`: the plain natural-number sum of the 16-bit big-endian words of `l` (an odd last
  octet is padded with a zero octet on its right, RFC 9293 §3.1).
* `fold s`: the 16-bit ones' complement value of a natural sum `s` (end-around carry):
  `0` for `0`, else `(s - 1) % 65535 + 1`. Ones' complement addition is addition modulo
  `2^16 - 1` in which `0x0000` and `0xFFFF` both represent zero; `fold` picks `0xFFFF` for a
  nonzero multiple of `65535`.
* `ocAdd`, `ocSum`: the incremental algorithm of RFC 1071 §1 ("adjacent octets ... are paired
  to form 16-bit integers, and the 1's complement sum of these 16-bit integers is formed"),
  one end-around carry per word. `Checksum.Thms.ocSum_eq` proves it computes `fold` of the
  plain sum, so the checksum depends only on `wsum` (the order of the words does not matter,
  RFC 1071 §2(B)).
* `checksum l`: the ones' complement of `fold (wsum l)`, computed over the octets with the
  checksum field set to zero; `txUdp c`: the UDP rule "if the computed checksum is zero, it is
  transmitted as all ones" (RFC 768; RFC 8200 §8.1 for IPv6).
* `verify l`: the receiver's check, that the ones' complement sum over all octets (checksum
  field included) is `0xFFFF` ("all ones", RFC 1071 §1 (3)).

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Ip.Checksum

/-- The plain sum of the 16-bit big-endian words of `l`; an odd last octet is padded with a
zero octet on its right (RFC 768 "Fields", RFC 9293 §3.1). -/
def wsum : List UInt8 → Nat
  | [] => 0
  | [a] => a.toNat * 256
  | a :: b :: r => (a.toNat * 256 + b.toNat) + wsum r

/-- The 16-bit words of `l`, padded as in `wsum`. -/
def words : List UInt8 → List Nat
  | [] => []
  | [a] => [a.toNat * 256]
  | a :: b :: r => (a.toNat * 256 + b.toNat) :: words r

/-- The ones' complement value of a natural sum (end-around carry): `0` stays `0`, a nonzero
sum is folded into `1 … 0xFFFF`. -/
def fold (s : Nat) : Nat := if s = 0 then 0 else (s - 1) % 65535 + 1

/-- Ones' complement addition of two 16-bit values, with the end-around carry (RFC 1071 §1). -/
def ocAdd (a b : Nat) : Nat := if 65536 ≤ a + b then a + b - 65535 else a + b

/-- The incremental ones' complement sum of 16-bit values (RFC 1071 §1, step (2)). -/
def ocSum (ws : List Nat) : Nat := ws.foldl ocAdd 0

/-- **The checksum** of the octets `l` (with the checksum field set to zero): the ones'
complement of the ones' complement sum (RFC 768, RFC 9293 §3.1). -/
def checksum (l : List UInt8) : UInt16 := UInt16.ofNat (65535 - fold (wsum l))

/-- The UDP transmission rule: a computed checksum of zero is transmitted as all ones, since an
all-zero field means "no checksum" (RFC 768; RFC 8200 §8.1). -/
def txUdp (c : UInt16) : UInt16 := if c = 0 then 0xFFFF else c

/-- **The receiver's check**: the ones' complement sum of all octets, checksum field included,
is all ones (RFC 1071 §1, step (3)). -/
def verify (l : List UInt8) : Bool := fold (wsum l) == 65535

end Silmaril.Net.Ip.Checksum

module

/-!
# Network byte order

Multi-octet fields of the Internet protocols are transmitted most significant octet first
("big-endian", RFC 791 Appendix B, "Data Transmission Order"; RFC 9293 §3.1 and RFC 768 use
the same convention). This module fixes the encodings of 16- and 32-bit fields used by the
transport headers:

* `be16 x`, `be32 x`: the two and four octets of `x`, most significant first;
* `rd16 a b`, `rd32 a b c d`: the inverse readers.

`Silmaril.Net.Wire.Thms` proves that they are mutually inverse (`rd16_be16`, `be16_rd16`,
`rd32_be32`, `be32_rd32`). Everything is stated through `toNat`, so proofs are `omega`
arithmetic on natural numbers.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Wire

/-- The two octets of a 16-bit field, most significant first (RFC 791 Appendix B). -/
def be16 (x : UInt16) : List UInt8 :=
  [UInt8.ofNat (x.toNat / 256), UInt8.ofNat (x.toNat % 256)]

/-- Read a 16-bit field from two octets, most significant first. -/
def rd16 (a b : UInt8) : UInt16 := UInt16.ofNat (a.toNat * 256 + b.toNat)

/-- The four octets of a 32-bit field, most significant first (RFC 791 Appendix B). -/
def be32 (x : UInt32) : List UInt8 :=
  [UInt8.ofNat (x.toNat / 16777216), UInt8.ofNat (x.toNat / 65536 % 256),
   UInt8.ofNat (x.toNat / 256 % 256), UInt8.ofNat (x.toNat % 256)]

/-- Read a 32-bit field from four octets, most significant first. -/
def rd32 (a b c d : UInt8) : UInt32 :=
  UInt32.ofNat (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat)

/-- `n` zero octets (header padding, RFC 9293 §3.1 MUST-69). -/
def zeros (n : Nat) : List UInt8 := List.replicate n 0

end Silmaril.Net.Wire

module

public import Silmaril.Formats.Compression.Checksum.GF2Poly

/-!
# Declarative CRC-32 specification

ISO 3309 / ITU-T V.42, as referenced by RFC 1952 §8, define the
32-bit frame check sequence of a `k`-bit message `M(x)` as the ones' complement
of the GF(2) sum of

1. the remainder of `xᵏ · (x³¹ + … + x + 1)` divided by `G(x)`, and
2. the remainder of `x³² · M(x)` divided by `G(x)`,

where `G(x) = x³² + x²⁶ + x²³ + x²² + x¹⁶ + x¹² + x¹¹ + x¹⁰ + x⁸ + x⁷ + x⁵ + x⁴ + x² + x + 1`.
(The first term is the effect of presetting the register to all ones, i.e. of
complementing the first 32 message bits; stated this way it also covers messages
shorter than 32 bits.) Bytes are transmitted least significant bit first and the
first transmitted bit is the highest-order coefficient of `M(x)`. The check
sequence is transmitted highest-order coefficient first and also read least
significant bit first, so the 32-bit value is the bit reversal of the
complemented remainder.

`crc32Spec` writes this down with the polynomial model of `GF2Poly`; it does not
mention the reflected shift register of `crc32Byte`. That `crc32` computes it is
`crc32_eq_spec` in `Silmaril.Formats.Compression.Checksum.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

open GF2Poly

/-- The CRC-32 generator polynomial `G(x)`, coefficient of `xⁱ` at bit `i`
(`0x04C11DB7` with the `x³²` term). -/
def crc32Generator : Nat := 0x104C11DB7

/-- The bits of a byte in transmission order, least significant first. -/
def byteBits (b : UInt8) : List Bool := (List.range 8).map b.toNat.testBit

/-- The bits of a message in transmission order. -/
def messageBits (bytes : List UInt8) : List Bool := bytes.flatMap byteBits

/-- The message polynomial `M(x)`: the first transmitted bit is its
highest-order coefficient. -/
def messagePoly (bytes : List UInt8) : Nat := ofBits (messageBits bytes)

/-- The CRC remainder before the final complement:
`(xᵏ · (x³¹ + … + 1)) mod G + (x³² · M(x)) mod G`, for a `k`-bit message. -/
def crc32Remainder (bytes : List UInt8) : Nat :=
  add (mod (mulXPow (messageBits bytes).length (ones 32)) crc32Generator)
    (mod (mulXPow 32 (messagePoly bytes)) crc32Generator)

/-- CRC-32 as specified: the ones' complement of the remainder, its `x³¹`
coefficient first, read into a 32-bit value least significant bit first. -/
def crc32Spec (bytes : List UInt8) : UInt32 :=
  UInt32.ofNat (reflect 32 (add (crc32Remainder bytes) (ones 32)))

end Silmaril.Formats.Compression

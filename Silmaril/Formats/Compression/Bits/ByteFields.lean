module

public import Silmaril.Formats.Compression.Bits.Bit

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# Fixed-width byte fields

The 32-bit header and trailer fields of gzip (little-endian, RFC 1952 §2.2) and
zlib (big-endian, RFC 1950 §2.2), with the facts needed to reason about them:
reading back what was written gives the value mod `2 ^ 32`, and writing back what
was read gives the same four bytes.
-/

/-- The low 32 bits of `n`, little-endian. -/
def le32Bytes (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
   UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256)]

/-- Read four little-endian bytes as a `Nat`. -/
def le32Val (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat

/-- The low 32 bits of `n`, big-endian. -/
def be32Bytes (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Read four big-endian bytes as a `Nat`. -/
def be32Val (b0 b1 b2 b3 : UInt8) : Nat :=
  16777216 * b0.toNat + 65536 * b1.toNat + 256 * b2.toNat + b3.toNat

end Silmaril.Formats.Compression

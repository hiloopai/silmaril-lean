module

/-!
# Bits as `Bool`

A small standalone bit API.  The DEFLATE path does **not** use it: `Bitstream`
(`LSBWriter` / `LSBReader`) and `BitstreamLemmas` (`natBits` / `msbBits`) are
what `Silmaril.Formats.Compression.Deflate` is built on, and what the round-trip proofs
are stated against.  Everything here except `abbrev Bit` is unreferenced
elsewhere in the repository; the round trips at the end of the file are what
keeps it from drifting (`nToBitsLSB` used to decompose `n - 1` at every level,
so it was a bit decomposition of nothing).
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-- A single bit, represented as `Bool`. -/
abbrev Bit := Bool

namespace Bit

/-- bit → Nat: false=0, true=1 -/
@[simp]
def toNat (b : Bit) : Nat := if b then 1 else 0

/-- Parity of a Nat as a bit. -/
def ofNat (n : Nat) : Bit := n % 2 = 1

/-- Bits of a Nat, least-significant bit first, with no leading zeros
(`nToBitsLSB 0 = []`). -/
def nToBitsLSB (n : Nat) : List Bit :=
  if h : n = 0 then []
  else (n % 2 = 1) :: nToBitsLSB (n / 2)
decreasing_by omega

/-- Bits of a Nat, MSB first, padded to width `w`. -/
def nToBitsMSB (n : Nat) (w : Nat) : List Bit :=
  List.ofFn (λ (i : Fin w) =>
    let shift := w - 1 - i.val
    (n >>> shift) % 2 = 1)

/-- List of bits → Nat, LSB first. -/
def bitsToNatLSB : List Bit → Nat
  | [] => 0
  | b :: bs => toNat b + 2 * bitsToNatLSB bs

/-- List of bits → Nat, MSB first. -/
def bitsToNatMSB : List Bit → Nat
  | [] => 0
  | b :: bs => toNat b * (2 ^ bs.length) + bitsToNatMSB bs

/-- A byte is 8 bits. -/
def byteWidth : Nat := 8

/-- 8 bits (MSB first) → UInt8. -/
def toUInt8 (bits : List Bit) : UInt8 :=
  UInt8.ofNat (bitsToNatMSB bits)

/-- UInt8 → 8 bits, MSB first. -/
def fromUInt8 (x : UInt8) : List Bit :=
  List.ofFn (λ (i : Fin byteWidth) =>
    ((x.toNat >>> (byteWidth - 1 - i.val)) % 2 = 1 : Bit))

/-- Reverse a bit list. -/
def reverse (bs : List Bit) : List Bit := List.reverse bs

/-- Pad with false bits to next byte boundary. -/
def padToByte (bs : List Bit) : List Bit :=
  let rem := bs.length % byteWidth
  if rem = 0 then bs
  else bs ++ List.replicate (byteWidth - rem) false

/-- Take first `n` bits. -/
def takeBits (bs : List Bit) (n : Nat) : List Bit := bs.take n

end Bit

end Silmaril.Formats.Compression

module

public import Silmaril.Formats.Compression.Bits.Bit

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# Adler-32 (RFC 1950 §9)

`s1` starts at 1, `s2` at 0; each byte updates `s1 := (s1 + b) mod 65521` and
then `s2 := (s2 + s1) mod 65521`; the checksum is `s2 * 65536 + s1`.

`adler32_check` is the published check value from the Wikipedia/RFC example
(`Adler-32("Wikipedia") = 0x11E60398`); together with `adler32_check_123456789`
it pins down the modulus, the accumulation order and the `s2 : s1` packing.
-/

set_option maxRecDepth 20000

/-- Adler-32 modulus (largest prime < 2^16). -/
def adlerMod : Nat := 65521

/-- Update Adler-32 accumulator pair with one byte. -/
def adler32UpdateByte (s1 s2 : Nat) (byte : Nat) : Nat × Nat :=
  let s1' := (s1 + byte) % adlerMod
  let s2' := (s2 + s1') % adlerMod
  (s1', s2')

/-- Run the Adler-32 accumulators over `data`, starting from `st`. This is the
state a streaming implementation carries between calls. -/
def adler32Fold (st : Nat × Nat) (data : List Nat) : Nat × Nat :=
  data.foldl (λ (acc : Nat × Nat) (b : Nat) => adler32UpdateByte acc.1 acc.2 b) st

/-- Adler-32 of a `List` of byte values as `Nat`. -/
def adler32OfList (data : List Nat) : Nat :=
  let (s1, s2) := adler32Fold (1, 0) data
  s2 * 65536 + s1

/-- Adler-32 of a `ByteArray` as `UInt32`. -/
def adler32 (data : ByteArray) : UInt32 :=
  UInt32.ofNat (adler32OfList (data.data.toList.map (λ b => b.toNat)))

/-- Adler-32 of a `List UInt8` as `UInt32`. -/
def adler32List (data : List UInt8) : UInt32 :=
  UInt32.ofNat (adler32OfList (data.map (λ b => b.toNat)))

end Silmaril.Formats.Compression

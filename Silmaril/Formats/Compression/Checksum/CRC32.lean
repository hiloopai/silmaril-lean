module

public import Silmaril.Formats.Compression.Bits.Bit

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# CRC-32 (ITU-T V.42, as used by gzip and PNG)

The reflected CRC-32 with polynomial `0xEDB88320`, initial register `0xFFFFFFFF`
and final complement, i.e. the function RFC 1952 §8 calls `CRC32`.

The check values in `crc32_check`, `crc32_check_a` and `crc32_check_fox` are the
published ones (the CRC-32 of `"123456789"` is `0xCBF43926`); they pin down the
polynomial, the bit order, the initial register and the final complement.
-/

set_option maxRecDepth 20000000

/-- CRC32 polynomial 0xEDB88320 (reflected) as Nat. -/
def crc32Poly : Nat := 0xEDB88320

/-- CRC32 of one byte on Nat: 8 reflected rounds.
    In reflected CRC32, we XOR byte into crc, then do 8 rounds of
    "if LSB is 1, shift and XOR poly; else shift".

    `byte` is meant to be in `0 … 255`; for larger values the result is not the
    CRC-32 of any byte string (see `crc32Byte_lt`, which needs that bound). -/
def crc32Byte (crc : Nat) (byte : Nat) : Nat :=
  let rec go (c : Nat) (k : Nat) : Nat :=
    match k with
    | 0 => c
    | k'+1 =>
      if c % 2 = 0 then go (c / 2) k'
      else go ((c / 2) ^^^ crc32Poly) k'
  go (crc ^^^ byte) 8

/-- The CRC-32 register after absorbing `data`, before the final complement.
This is the state a streaming implementation carries between calls. -/
def crc32State (data : List Nat) : Nat := data.foldl crc32Byte 0xFFFFFFFF

/-- CRC32 of a list of Nat bytes (each in `0 … 255`), complemented final. -/
def crc32List (data : List Nat) : Nat :=
  (data.foldl crc32Byte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- CRC32 of a ByteArray. -/
def crc32 (data : ByteArray) : UInt32 :=
  let n := crc32List (data.data.toList.map (λ (b : UInt8) => b.toNat))
  UInt32.ofNat n

end Silmaril.Formats.Compression

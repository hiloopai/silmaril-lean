module

public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Formats.Compression.Thms
import Silmaril.Proofs.Formats.Compression.Checksum
import Silmaril.Raw.Formats.Compression.Checksum.Adler32
import Silmaril.Raw.Formats.Compression.Checksum.CRC32

/-!
# Checksums: facts

Proved (standard axioms):

* `adler32_digest`, `adler32_digest_byteArray`, `crc32_digest`: the incremental
  checksums compute the format modules' check values;
* the published check values: Adler-32 of `"Wikipedia"` is `0x11E60398`
  (RFC 1950 §9's example) and of `"123456789"` is `0x091E01DE`; CRC-32 of
  `"123456789"` is `0xCBF43926`;
* `adler32_lt`, `crc32List_append`: range and incremental laws.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Checksum

theorem adler32_digest (bytes : List UInt8) : adler32.digest bytes = adler32List bytes :=
  Proofs.Formats.Compression.adler32_digest bytes

theorem adler32_digest_byteArray (bytes : ByteArray) :
    adler32.digest bytes.data.toList = Compression.adler32 bytes :=
  Proofs.Formats.Compression.adler32_digest_byteArray bytes

theorem crc32_digest (bytes : ByteArray) : crc32.digest bytes.data.toList = Compression.crc32 bytes :=
  Proofs.Formats.Compression.crc32_digest bytes

/-- RFC 1950 §9's example: the Adler-32 of `"Wikipedia"` is `0x11E60398`. -/
theorem adler32_check_wikipedia :
    adler32.digest [0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61] = 0x11E60398 := by
  rw [adler32_digest]; decide

/-- The Adler-32 of `"123456789"` is `0x091E01DE`. -/
theorem adler32_check_123456789 :
    adler32.digest [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0x091E01DE := by
  rw [adler32_digest]; decide

/-- The standard CRC-32 check value: the CRC-32 of `"123456789"` is `0xCBF43926`. -/
theorem crc32_check_123456789 :
    crc32.digest [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926 :=
  (crc32_digest ⟨#[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]⟩).trans
    Compression.crc32_check

theorem adler32_lt (data : List Nat) : adler32OfList data < 2 ^ 32 :=
  adler32OfList_lt data

theorem crc32List_append (a b : List Nat) :
    crc32List (a ++ b) = b.foldl crc32Byte (crc32List a ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF :=
  Compression.crc32List_append a b

end Silmaril.Formats.Compression.Checksum

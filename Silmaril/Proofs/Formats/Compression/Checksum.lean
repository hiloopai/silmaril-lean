module

public import Silmaril.Formats.Compression.Checksum.Defs

/-! Proofs for `Silmaril.Formats.Compression.Checksum.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression

open Silmaril.Formats.Compression

theorem adler32_digest (bytes : List UInt8) :
    Checksum.adler32.digest bytes = adler32List bytes := by
  simp only [Checksum.digest, Checksum.adler32, adler32List, adler32OfList, adler32Fold,
    List.foldl_map]

theorem adler32_digest_byteArray (bytes : ByteArray) :
    Checksum.adler32.digest bytes.data.toList = adler32 bytes := by
  rw [adler32_digest]; rfl

theorem crc32_digest (bytes : ByteArray) :
    Checksum.crc32.digest bytes.data.toList = crc32 bytes := by
  simp only [Checksum.digest, Checksum.crc32, crc32, crc32List, List.foldl_map]

end Silmaril.Proofs.Formats.Compression

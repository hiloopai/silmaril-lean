module

public import Silmaril.Formats.Compression.Vectors
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Vectors`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

theorem helloBytes_eq_toUTF8 : "hello".toUTF8 = helloBytes := by
  -- `String.toUTF8` of a literal does not reduce in the kernel; go through `String.ofList`.
  have h : "hello" = String.ofList ['h', 'e', 'l', 'l', 'o'] := by rfl
  rw [String.toUTF8_eq_toByteArray, h, String.toByteArray_ofList]
  decide +kernel

theorem zlibDecompress_cpython_fixed : zlibDecompress zlibCpythonFixed = some helloBytes := by
  decide +kernel

theorem zlibDecompress_cpython_stored : zlibDecompress zlibCpythonStored = some helloBytes := by
  decide +kernel

/-- Our compressor agrees with CPython's `zlib.compress(b"hello", 0)` byte for byte. -/
theorem zlibCompress_hello_eq_cpython : zlibCompress helloBytes = zlibCpythonStored := by
  decide +kernel

theorem gzipDecompress_gnu : gzipDecompress gzipGnu = some helloBytes := by
  decide +kernel

theorem gzipDecompress_cpython : gzipDecompress gzipCpython = some helloBytes := by
  decide +kernel

/-- The fixed-Huffman zlib vector with its last Adler-32 byte changed (`15` → `16`). -/
theorem zlibDecompress_bad_adler :
    zlibDecompress ⟨#[0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c, 0x02,
      0x16]⟩ = none := by
  decide +kernel

/-- The GNU gzip vector with its first CRC-32 byte changed (`86` → `87`). -/
theorem gzipDecompress_bad_crc :
    gzipDecompress ⟨#[0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48,
      0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x87, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00]⟩ = none := by
  decide +kernel

end Silmaril.Formats.Compression

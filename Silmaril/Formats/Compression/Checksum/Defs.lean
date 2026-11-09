module

public import Silmaril.Formats.Compression.Defs
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Bits.ByteFields

/-!
# Checksums of the DEFLATE containers

The two `Checksum`s used by zlib and gzip, as incremental folds, and the 32-bit
serialisations their trailers use:

* `Checksum.adler32`: Adler-32 (RFC 1950 §9), state `(s1, s2)` modulo 65521;
* `Checksum.crc32`: the reflected CRC-32 with polynomial `0xEDB88320`
  (RFC 1952 §8), state the CRC register before the final complement;
* `be32`, `le32`: four bytes, big-endian (zlib) or little-endian (gzip).

The whole-input functions `adler32List`, `adler32` and `crc32` of the format
modules are the `digest`s of these (`Checksum.Thms`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace Checksum

/-- Adler-32 (RFC 1950 §9). -/
def adler32 : Checksum where
  State := Nat × Nat
  init := (1, 0)
  update st byte := adler32UpdateByte st.1 st.2 byte.toNat
  finish st := UInt32.ofNat (st.2 * 65536 + st.1)

/-- CRC-32 (ITU-T V.42; RFC 1952 §8). -/
def crc32 : Checksum where
  State := Nat
  init := 0xFFFFFFFF
  update crc byte := crc32Byte crc byte.toNat
  finish crc := UInt32.ofNat (crc ^^^ 0xFFFFFFFF)

end Checksum

/-- A 32-bit value as four big-endian bytes. -/
abbrev be32 (value : UInt32) : List UInt8 := be32Bytes value.toNat

/-- A 32-bit value as four little-endian bytes. -/
abbrev le32 (value : UInt32) : List UInt8 := le32Bytes value.toNat

end Silmaril.Formats.Compression

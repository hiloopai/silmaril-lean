module

public import Silmaril.Formats.Compression.Zstd.Defs
public import Silmaril.Formats.Compression.Thms

/-!
# Zstandard frames (RFC 8878), uncompressed subset: checked facts

Everything here is a known answer checked by `decide` (kernel evaluation); there
are no general theorems about `Zstd.frame` yet.

* XXH64: the published values for `""`, `"a"`, `"abc"` (xxHash's reference
  values) and for the 39-byte `"Nobody inspects the spammish repetition"` (the
  python-xxhash documentation's example, which exercises the 32-byte stripe
  path);
* `windowSize`: 1 KiB minimum, and the RFC 9659 8 MiB limit;
* frames hand-constructed from RFC 8878 §3.1 (not cross-checked against
  libzstd): a raw block with content checksum (`rawFrame`), an RLE block, a
  frame of three blocks with a window descriptor, a skippable frame before a
  frame, and RFC 9842's `dcz` header, which is a skippable frame; rejections of
  a compressed block (not implemented), a reserved block type, a wrong checksum,
  the reserved header bit, a `Dictionary_ID`, a `Frame_Content_Size` mismatch and
  a 16 MiB window under the 8 MiB HTTP limit.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd

theorem xxh64_empty : xxh64 0 [] = 0xEF46DB3751D8E999 := by decide

theorem xxh64_a : xxh64 0 [0x61] = 0xD24EC4F1A98C6E5B := by decide

theorem xxh64_abc : xxh64 0 [0x61, 0x62, 0x63] = 0x44BC2CF5AD770999 := by decide

/-- `"Nobody inspects the spammish repetition"` (39 bytes: one stripe and a tail). -/
theorem xxh64_spammish :
    xxh64 0 [0x4E, 0x6F, 0x62, 0x6F, 0x64, 0x79, 0x20, 0x69, 0x6E, 0x73, 0x70, 0x65, 0x63,
      0x74, 0x73, 0x20, 0x74, 0x68, 0x65, 0x20, 0x73, 0x70, 0x61, 0x6D, 0x6D, 0x69, 0x73, 0x68,
      0x20, 0x72, 0x65, 0x70, 0x65, 0x74, 0x69, 0x74, 0x69, 0x6F, 0x6E] = 0xFBCEA83C8A378BF1 := by
  decide

theorem windowSize_min : windowSize 0 = 1024 := by decide

/-- Exponent 13, mantissa 0: 8 MiB, the RFC 9659 limit. -/
theorem windowSize_8MiB : windowSize 0x68 = 8388608 := by decide

theorem windowSize_16MiB : windowSize 0x70 = 16777216 := by decide

/-- The 8 MiB HTTP window limit (RFC 9659). -/
abbrev httpWindow : Nat := 8388608

/-- `hello`. -/
def hello : List UInt8 := [0x68, 0x65, 0x6c, 0x6c, 0x6f]

/-- `rawFrame hello`, byte for byte: single segment with content checksum
(`FHD = 0x24`), `Frame_Content_Size = 5`, one last raw block of 5 bytes
(`Block_Header = 0x000029`), then the low 32 bits of `XXH64(hello)`
(`0x889F6DA3`) little-endian. -/
theorem rawFrame_hello :
    rawFrame hello = [0x28, 0xB5, 0x2F, 0xFD, 0x24, 0x05, 0x29, 0x00, 0x00, 0x68, 0x65, 0x6c,
      0x6c, 0x6f, 0xa3, 0x6d, 0x9f, 0x88] := by decide

theorem decode_rawFrame_hello : decode httpWindow (rawFrame hello) = some hello := by decide

/-- One RLE block: `a` ten times. -/
theorem decode_rle :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x0A, 0x53, 0x00, 0x00, 0x61] =
      some (List.replicate 10 0x61) := by decide

/-- A 1 KiB window and three blocks: raw `he`, RLE `ll`, last raw `o`. -/
theorem decode_blocks :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x00, 0x10, 0x00, 0x00, 0x68, 0x65,
      0x12, 0x00, 0x00, 0x6c, 0x09, 0x00, 0x00, 0x6f] = some hello := by decide

/-- A skippable frame (magic `0x184D2A50`, three bytes) before a frame. -/
theorem decode_skippable :
    decode httpWindow ([0x50, 0x2A, 0x4D, 0x18, 0x03, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03] ++
      rawFrame hello) = some hello := by decide

/-- RFC 9842 §5: the 40-byte `dcz` header is a skippable frame. -/
theorem frame_dcz_header (hash rest : List UInt8) (h : hash.length = 32) :
    frame httpWindow ([0x5E, 0x2A, 0x4D, 0x18, 0x20, 0x00, 0x00, 0x00] ++ hash ++ rest) =
      some ([], rest) := by
  simp [frame, Xxh64.leNat, h]

/-- A `Compressed_Block` (type 2) is not implemented and is rejected. -/
theorem decode_rejects_compressed :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x05, 0x2D, 0x00, 0x00, 0x68, 0x65, 0x6c,
      0x6c, 0x6f] = none := by decide

/-- Block type 3 is reserved. -/
theorem decode_rejects_reserved_block :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x05, 0x2F, 0x00, 0x00, 0x68, 0x65, 0x6c,
      0x6c, 0x6f] = none := by decide

theorem decode_rejects_checksum :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x24, 0x05, 0x29, 0x00, 0x00, 0x68, 0x65, 0x6c,
      0x6c, 0x6f, 0xa3, 0x6d, 0x9f, 0x89] = none := by decide

/-- The reserved bit of `Frame_Header_Descriptor` must be zero. -/
theorem decode_rejects_reserved_bit :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x28, 0x05, 0x29, 0x00, 0x00, 0x68, 0x65, 0x6c,
      0x6c, 0x6f] = none := by decide

/-- A frame naming dictionary 7 is rejected (dictionaries are planned). -/
theorem decode_rejects_dictionary :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x21, 0x07, 0x01, 0x09, 0x00, 0x00, 0x6f] =
      none := by decide

/-- A 4-byte `Frame_Content_Size` of 5 matches a 5-byte block; 4 does not. -/
theorem decode_contentSize :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x00, 0x05, 0x00, 0x00, 0x00, 0x29, 0x00,
      0x00, 0x68, 0x65, 0x6c, 0x6c, 0x6f] = some hello ∧
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x00, 0x04, 0x00, 0x00, 0x00, 0x29, 0x00,
      0x00, 0x68, 0x65, 0x6c, 0x6c, 0x6f] = none := by decide

/-- A 16 MiB window is rejected under the 8 MiB HTTP limit, and accepted with a
16 MiB limit. -/
theorem decode_window_limit :
    decode httpWindow [0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x70, 0x09, 0x00, 0x00, 0x6f] = none ∧
      decode 16777216 [0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x70, 0x09, 0x00, 0x00, 0x6f] =
        some [0x6f] := by decide

end Silmaril.Formats.Compression.Zstd

module

public import Silmaril.Formats.Compression.ContainerSpec.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.GzipHeader.Defs
import Silmaril.Proofs.Formats.Compression.ContainerSpec
import Silmaril.Proofs.Formats.Compression.ContainerProfiles

/-!
# zlib and gzip: the decoders against the declarative container semantics

Proved (standard axioms). Each decoder accepts **exactly** the inputs the
corresponding `ContainerSpec` relation describes, with the same output and rest
(soundness and completeness in one `iff`):

* `zlib_take_iff`: `Zlib.take` (= `Zlib.decoder`) and `ZlibMember`;
* `zlib_decompress_iff`: the whole-buffer `Zlib.decompress` and `ZlibMember … []`;
* `zlib_takeWithDictionary_iff`: `Zlib.takeWithDictionary` and `ZlibMember` or
  `ZlibDictMember` (DEFLATE decoded with the dictionary as history, via
  `DeflateSpec.deflateTakeWithHistory_iff` and `StreamWithHistory.window`);
* `parseHeader_iff`: the structured gzip header parser and `GzipMemberHeader`;
* `gzipMember_iff`: `gzipMember` (= `Gzip.decoder`) and `GzipMember`;
* `gzipDecompress_iff`: `gzipDecompress` (= `Gzip.decompress`) and `GzipFile`.

Separately named profiles (the decoders above are unchanged):

* `zlib_takeWindowed_iff`: `Zlib.takeWindowed` and `ZlibMemberWindowed`, every
  distance within the `CINFO` window; `zlibWindowOnly` is a member that only the
  unwindowed profile accepts (zlib 1.3.1 without `INFLATE_STRICT` accepts it);
* `zlib_takeWithDictionaryAnyWindow_iff`, `zlib_takeWithDictionaryWindowed_iff`:
  preset dictionaries for every `CINFO`, without and with the window bound;
  `takeWithDictionary_eq_anyWindow`: equal to `takeWithDictionary` on `CINFO = 7`;
* `gzip_decompressPrefix_iff`: the suffix-lenient file decoder
  `Gzip.decompressPrefix` and `GzipFilePrefix`; `gzipDecompress_iff_prefix`: the
  strict file decoder is the lenient one with an empty suffix.

The proofs go through `DeflateSpec.deflateTake_iff` for the body,
`crc32_eq_spec` and `Checksum.adler32_toNat_eq_symbolic` for the check values,
and `GzipHeader.parseHeader_agrees` for the gzip header.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.ContainerSpec

/-- **zlib member decoder**: `Zlib.take` returns `(out, rest)` exactly when the
input starts with an RFC 1950 member without preset dictionary decoding to `out`,
followed by `rest`. -/
theorem zlib_take_iff {bs out rest : List UInt8} :
    Zlib.take bs = some (out, rest) ↔ ZlibMember bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.take_iff

/-- The whole-buffer zlib decoder: exactly one member and nothing after it. -/
theorem zlib_decompress_iff {bs out : List UInt8} :
    Zlib.decompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ ZlibMember bs out [] :=
  Proofs.Formats.Compression.ContainerSpec.zlibDecompress_iff

/-- **zlib with a preset dictionary**: a member without `FDICT` ignores the
offered dictionary; a member with `FDICT` must name the dictionary's Adler-32 and
is decoded with the dictionary as history. -/
theorem zlib_takeWithDictionary_iff {dictionary bs out rest : List UInt8} :
    Zlib.takeWithDictionary dictionary bs = some (out, rest) ↔
      ZlibMember bs out rest ∨ ZlibDictMember dictionary bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.takeWithDictionary_iff

/-- The structured gzip header parser reads exactly the RFC 1952 §2.3 headers. -/
theorem parseHeader_iff {bs rest : List UInt8} {hdr : GzipHeader.Header} :
    GzipHeader.parseHeader bs = some (hdr, rest) ↔ GzipMemberHeader bs hdr rest :=
  Proofs.Formats.Compression.ContainerSpec.parseHeader_iff

/-- **gzip member decoder**: `gzipMember` returns `(out, rest)` exactly when the
input starts with an RFC 1952 member (with some header) decoding to `out`,
followed by `rest`. -/
theorem gzipMember_iff {bs out rest : List UInt8} :
    gzipMember bs = some (out, rest) ↔ ∃ hdr, GzipMember bs hdr out rest :=
  Proofs.Formats.Compression.ContainerSpec.gzipMember_iff

/-- **gzip file decoder**: `gzipDecompress` returns `out` exactly when the input
is one or more RFC 1952 members, with no other bytes, decoding to `out`. -/
theorem gzipDecompress_iff {bs out : List UInt8} :
    gzipDecompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ GzipFile bs out :=
  Proofs.Formats.Compression.ContainerSpec.gzipDecompress_iff

/-! ### zlib: the `CINFO` window -/

/-- **Strict-window zlib member decoder**: `Zlib.takeWindowed` accepts exactly the
members whose back-references stay within `2 ^ (CINFO + 8)` bytes. -/
theorem zlib_takeWindowed_iff {bs out rest : List UInt8} :
    Zlib.takeWindowed bs = some (out, rest) ↔ ZlibMemberWindowed bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.takeWindowed_iff

theorem ZlibMemberWindowed.member {bs out rest : List UInt8} (h : ZlibMemberWindowed bs out rest) :
    ZlibMember bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.zlibMemberWindowed_member h

/-- With a 32 KiB window (`CINFO = 7`) the window bound is no restriction. -/
theorem zlibMemberWindowed_iff_seven {cmf : UInt8} {tl out rest : List UInt8}
    (h7 : cmf.toNat / 16 = 7) :
    ZlibMemberWindowed (cmf :: tl) out rest ↔ ZlibMember (cmf :: tl) out rest :=
  Proofs.Formats.Compression.ContainerSpec.zlibMemberWindowed_iff_seven h7

/-- `CINFO = 0` (a 256-byte window), a back-reference of distance 257: a
`ZlibMember` (and accepted by zlib 1.3.1's `inflate` with `windowBits` 15 or 8)
that the windowed profile rejects. -/
theorem zlibWindowOnly :
    ZlibMember [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00, 0x00, 0x01, 0x06, 0x00, 0x01]
      (List.replicate 262 0) [] ∧
    ∀ out rest, ¬ ZlibMemberWindowed [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00, 0x00, 0x01,
      0x06, 0x00, 0x01] out rest :=
  Proofs.Formats.Compression.ContainerSpec.zlib_window_witness

/-! ### zlib: preset dictionaries for every window -/

/-- Dictionaries for every `CINFO`: the whole dictionary is the history (only its
last 32 KiB can be referenced). -/
theorem zlib_takeWithDictionaryAnyWindow_iff {dictionary bs out rest : List UInt8} :
    Zlib.takeWithDictionaryAnyWindow dictionary bs = some (out, rest) ↔
      ZlibMember bs out rest ∨ ZlibDictMemberAnyWindow dictionary bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.takeWithDictionaryAnyWindow_iff

theorem zlibDictMember_iff_anyWindow {dictionary bs out rest : List UInt8} :
    ZlibDictMember dictionary bs out rest ↔
      ZlibDictMemberAnyWindow dictionary bs out rest ∧
        ∃ cmf tl, bs = cmf :: tl ∧ cmf.toNat / 16 = 7 :=
  Proofs.Formats.Compression.ContainerSpec.zlibDictMember_iff_anyWindow

/-- `takeWithDictionary` is `takeWithDictionaryAnyWindow` on `CINFO = 7` inputs. -/
theorem takeWithDictionary_eq_anyWindow {dictionary bs : List UInt8}
    (h7 : ∀ cmf tl, bs = cmf :: tl → cmf.toNat / 16 = 7) :
    Zlib.takeWithDictionary dictionary bs = Zlib.takeWithDictionaryAnyWindow dictionary bs :=
  Proofs.Formats.Compression.ContainerSpec.takeWithDictionary_eq_anyWindow h7

theorem takeWithDictionary_anyWindow {dictionary bs out rest : List UInt8}
    (h : Zlib.takeWithDictionary dictionary bs = some (out, rest)) :
    Zlib.takeWithDictionaryAnyWindow dictionary bs = some (out, rest) :=
  Proofs.Formats.Compression.ContainerSpec.takeWithDictionary_anyWindow h

/-- Dictionaries within the `CINFO` window: the decoder installs only the last
`2 ^ (CINFO + 8)` dictionary bytes, the specification the whole dictionary; they
agree because no distance exceeds the window (`StreamWithHistoryWithin.window`). -/
theorem zlib_takeWithDictionaryWindowed_iff {dictionary bs out rest : List UInt8} :
    Zlib.takeWithDictionaryWindowed dictionary bs = some (out, rest) ↔
      ZlibMemberWindowed bs out rest ∨ ZlibDictMemberWindowed dictionary bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.takeWithDictionaryWindowed_iff

/-! ### gzip: suffix-lenient files -/

/-- **Suffix-lenient gzip file decoder**: `Gzip.decompressPrefix` returns
`(out, rest)` exactly when the input is one or more members, read greedily,
followed by `rest`, at which no member starts. -/
theorem gzip_decompressPrefix_iff {bs out rest : List UInt8} :
    Gzip.decompressPrefix bs = some (out, rest) ↔ GzipFilePrefix bs out rest :=
  Proofs.Formats.Compression.ContainerSpec.decompressPrefix_iff

theorem gzipFile_iff_prefix {bs out : List UInt8} : GzipFile bs out ↔ GzipFilePrefix bs out [] :=
  Proofs.Formats.Compression.ContainerSpec.gzipFile_iff_prefix

/-- The strict file decoder is the lenient one with nothing left over. -/
theorem gzipDecompress_iff_prefix {bs out : List UInt8} :
    gzipDecompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ Gzip.decompressPrefix bs = some (out, []) :=
  Proofs.Formats.Compression.ContainerSpec.gzipDecompress_iff_prefix

/-- GNU gzip's `hello` member followed by `XYZ`: a lenient file with suffix
`XYZ`, not a `GzipFile`. -/
theorem gzipTrailingGarbage :
    GzipFilePrefix [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48, 0xcd,
      0xc9, 0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00, 0x58, 0x59, 0x5a]
      [0x68, 0x65, 0x6c, 0x6c, 0x6f] [0x58, 0x59, 0x5a] ∧
    ∀ out, ¬ GzipFile [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48,
      0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00, 0x58, 0x59,
      0x5a] out :=
  Proofs.Formats.Compression.ContainerSpec.gzip_trailing_witness

end Silmaril.Formats.Compression.ContainerSpec

module

public import Silmaril.Formats.Compression.ContainerSpec.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.GzipHeader.Defs
import Silmaril.Proofs.Formats.Compression.ContainerSpec

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

end Silmaril.Formats.Compression.ContainerSpec

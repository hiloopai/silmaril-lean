module

public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.Deflate.Thms
public import Silmaril.Formats.Compression.Checksum.Thms
public import Silmaril.Formats.Compression.Vectors
import Silmaril.Proofs.Formats.Compression.Gzip
import Silmaril.Raw.Formats.Compression.Gzip.Basic
import Silmaril.Raw.Formats.Compression.Vectors

/-!
# gzip (RFC 1952): facts

Proved (standard axioms):

* `member_eq_decoder`: the format module's `gzipMember` is the framework
  container `framing.wrap Deflate.decoder`;
* `consumes`, `decoder_trailer`: a member consumes a prefix ending in the
  CRC-32/ISIZE trailer of its output, followed by the untouched rest;
* `framing_local`, `local`: header and trailer ignore appended bytes, so with
  `Deflate.local` bytes after a member never change how it decodes;
* `roundTrip`, `codec`, `compress_eq`, `decompress_compress`: the stored
  encoder round-trips;
* `decompress_eq`: a gzip file is `decoder.members`, so `members_encoder` and
  `decompress_append` decode concatenated members to the concatenated data
  (RFC 1952 §2.2);
* known answers: GNU gzip's and CPython's encodings of `hello`, and the
  rejection of a corrupted CRC-32.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Gzip

theorem member_eq_decoder : member = decoder := Proofs.Formats.Compression.Gzip.member_eq_decoder

theorem consumes : decoder.Consumes := Proofs.Formats.Compression.Gzip.consumes

/-- A member ends with the CRC-32 and ISIZE trailer of its output, then the rest. -/
theorem decoder_trailer {bytes out rest : List UInt8} (h : decoder bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (trailer out ++ rest) :=
  Proofs.Formats.Compression.Gzip.decoder_trailer h

theorem roundTrip : RoundTrip decoder encoder := Proofs.Formats.Compression.Gzip.roundTrip

theorem framing_local : framing.Local := Proofs.Formats.Compression.Gzip.framing_local

/-- Bytes after a gzip member never change how it decodes. -/
theorem «local» : decoder.Local := Proofs.Formats.Compression.Gzip.local_of_deflate Deflate.local

/-- gzip members with stored blocks, as a framework codec. -/
def codec : Codec := ⟨decoder, encoder, roundTrip⟩

theorem compress_eq (data : ByteArray) : (compress data).data.toList = encoder data.data.toList :=
  Proofs.Formats.Compression.Gzip.compress_eq data

theorem decompress_compress (data : ByteArray) : decompress (compress data) = some data :=
  gzipDecompress_gzipCompress data

/-- A gzip file is a sequence of one or more members. -/
theorem decompress_eq (bytes : ByteArray) :
    decompress bytes = (decoder.members bytes.data.toList).map (fun out => ⟨out.toArray⟩) :=
  Proofs.Formats.Compression.Gzip.decompress_eq bytes

/-- Concatenated members decode to the concatenated data. -/
theorem members_encoder {xs : List (List UInt8)} (hxs : xs ≠ []) :
    decoder.members (xs.flatMap encoder) = some xs.flatten :=
  roundTrip.members Proofs.Formats.Compression.Gzip.encoder_ne_nil hxs

theorem decompress_append (a b : ByteArray) :
    decompress (compress a ++ compress b) = some (a ++ b) :=
  gzipDecompress_append a b

theorem decompress_gnu : decompress gzipGnu = some helloBytes := gzipDecompress_gnu

theorem decompress_cpython : decompress gzipCpython = some helloBytes := gzipDecompress_cpython

/-- GNU gzip's vector with its first CRC-32 byte changed (`86` → `87`) is rejected. -/
theorem decompress_bad_crc :
    decompress ⟨#[0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48,
      0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x87, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00]⟩ = none :=
  gzipDecompress_bad_crc

end Silmaril.Formats.Compression.Gzip

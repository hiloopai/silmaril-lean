module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Formats.Compression.Thms
import Silmaril.Proofs.Formats.Compression.Deflate
import Silmaril.Raw.Formats.Compression.Deflate.Stored
import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
import Silmaril.Raw.Formats.Compression.Deflate.StoredWriter

/-!
# DEFLATE (RFC 1951): facts

Proved (standard axioms):

* `decoder_eq_some`, `consumes`: a member consumes a prefix of its input;
* `roundTrip`, `codec`: stored encodings decode back, whatever follows them;
  hence `exists_compresses` (every buffer is the decoding of some stream);
* `compress_isSome`, `compress_compresses`: the LZ77/fixed-Huffman compressor
  is total and sound;
* `fixedLitLen_valid`, `fixedDist_valid`: the fixed codes satisfy the Kraft inequality;
* `blocksBytes_take`: any partition into stored blocks of at most 65535 bytes is
  accepted (a semantic contract, not one encoder's block boundaries);
* `history_stored`, `history_match`, `no_history_rejected`: preset histories
  are consulted, and a match into a missing history is rejected;
* known-answer vectors produced by zlib (an independent implementation), one per
  block type, and two rejections (distance code 30, `BTYPE = 11`).

Open: `Task.local` (the append law), frozen.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

theorem decoder_eq_some {bytes out rest : List UInt8} :
    decoder bytes = some (out, rest) ↔ deflateTake bytes = .ok (out, rest) :=
  Proofs.Formats.Compression.Deflate.decoder_eq_some

theorem consumes : decoder.Consumes := Proofs.Formats.Compression.Deflate.decoder_consumes

theorem roundTrip : RoundTrip decoder encoder := Proofs.Formats.Compression.Deflate.roundTrip

/-- Raw DEFLATE with stored blocks, as a framework codec. -/
def codec : Codec := ⟨decoder, encoder, roundTrip⟩

theorem exists_compresses (data : ByteArray) : ∃ c, Compresses data c :=
  decompress_surjective data

theorem compress_isSome (data : ByteArray) : ∃ c, compress data = some c :=
  compress_total data

theorem compress_compresses {data c : ByteArray} (h : compress data = some c) :
    Compresses data c :=
  compress_sound h

theorem fixedLitLen_valid : isValidLengths fixedLitLenLengths 9 = true :=
  fixedLitLenLengths_valid

theorem fixedDist_valid : isValidLengths fixedDistLengths 5 = true :=
  fixedDistLengths_valid

/-- Every partition into bounded stored blocks decodes to its concatenation and
leaves the trailer untouched. -/
theorem blocksBytes_take (chunks : List (List UInt8)) (h : StoredWriter.Valid chunks)
    (trailer : List UInt8) :
    deflateTake (StoredWriter.blocksBytes chunks ++ trailer) = .ok (chunks.flatten, trailer) :=
  StoredWriter.deflateTake_blocksBytes chunks h trailer

theorem history_stored (history data tail : List UInt8) :
    deflateTakeWithHistory history (storedBytes data ++ tail) = .ok (data, tail) :=
  deflateTakeWithHistory_storedBytes history data tail

/-- With history `AB`, a fixed-Huffman match of length 4 at distance 2 expands. -/
theorem history_match :
    deflateTakeWithHistory [65, 66] [115, 4, 67, 0, 85, 102] =
      .ok ([65, 66, 65, 66, 65, 66], [85, 102]) :=
  seeded_fixed_match_checked

/-- Without history the same stream's match points before the output. -/
theorem no_history_rejected :
    deflateTakeWithHistory [] [115, 4, 67, 0, 85, 102] = .error .decodeOverrun :=
  unseeded_fixed_match_rejected

/-- zlib level 0, `"abc"`: one stored block. -/
theorem kat_stored :
    decompress ⟨#[0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63]⟩
      = some ⟨#[0x61, 0x62, 0x63]⟩ :=
  decompress_stored_vector

/-- zlib, `"abc"`: one fixed-Huffman block. -/
theorem kat_fixed :
    decompress ⟨#[0x4b, 0x4c, 0x4a, 0x06, 0x00]⟩ = some ⟨#[0x61, 0x62, 0x63]⟩ :=
  decompress_fixed_vector

/-- zlib level 9, a 40-byte string over `a b c d`: one dynamic-Huffman block. -/
theorem kat_dynamic :
    decompress ⟨#[0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
      0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
      0xb8, 0xe3, 0x01]⟩
      = some ⟨#[0x61, 0x63, 0x64, 0x64, 0x61, 0x61, 0x61, 0x64, 0x63, 0x63, 0x62, 0x61,
        0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x64, 0x63, 0x63, 0x62, 0x61, 0x63, 0x63,
        0x63, 0x62, 0x64, 0x64, 0x64, 0x64, 0x61, 0x63, 0x64, 0x62, 0x63, 0x64, 0x63,
        0x63, 0x63]⟩ :=
  decompress_dynamic_vector

/-- A fixed-Huffman back-reference with the reserved distance code 30 is rejected. -/
theorem kat_rejects_dist_code_30 : decompress ⟨#[0x73, 0x04, 0x3e, 0x00]⟩ = none :=
  decompress_rejects_dist_code_30

/-- `BTYPE = 11` is reserved. -/
theorem kat_rejects_reserved_btype : decompress ⟨#[0x07, 0x00]⟩ = none :=
  decompress_rejects_reserved_btype

end Silmaril.Formats.Compression.Deflate

module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Formats.Compression.Thms
public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
import Silmaril.Proofs.Formats.Compression.Deflate
import Silmaril.Proofs.Formats.Compression.DeflateLocal
import Silmaril.Proofs.Formats.Compression.Bounds
import Silmaril.Proofs.Formats.Compression.FixedEncoder
import Silmaril.Raw.Formats.Compression.Deflate.Stored
import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
import Silmaril.Raw.Formats.Compression.Deflate.StoredWriter
import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas

/-!
# DEFLATE (RFC 1951): facts

Proved (standard axioms):

* `decoder_eq_some`, `consumes`: a member consumes a prefix of its input;
* `deflateTake_append`, `deflateTakeWithHistory_append`, `local`, `task_local`:
  bytes appended after a member never change how it decodes (the append law,
  with or without a preset history);
* `roundTrip`, `codec`: stored encodings decode back, whatever follows them;
  hence `exists_compresses` (every buffer is the decoding of some stream);
* `compress_take`, `roundTripFixed`, `codecFixed`: the compressing encoder
  (`compress`, greedy LZ77 with one fixed-Huffman block) emits one complete
  member, which the list decoder reads back whatever follows it;
* `output_le`, `withHistory_output_le`, `decoder_output_le`, `decompress_output_le`:
  intrinsic output bounds; a member produces at most 2064 bytes (258 per bit)
  for each input byte it consumes;
* `compress_isSome`, `compress_compresses`: the LZ77/fixed-Huffman compressor
  is total and sound;
* `fixedLitLen_valid`, `fixedDist_valid`: the fixed codes satisfy the Kraft inequality;
* `blocksBytes_take`: any partition into stored blocks of at most 65535 bytes is
  accepted (a semantic contract, not one encoder's block boundaries);
* `withHistory_empty`, `withHistory_suffix`: the empty
  history is plain DEFLATE, and with any history a member consumes a prefix;
* `history_stored`, `history_match`, `no_history_rejected`: preset histories
  are consulted, and a match into a missing history is rejected;
* canonical Huffman codes (RFC 1951 §3.2.2): `assignCodes_getElem?` (the entry of each
  symbol), the Kraft sums `kraftUpTo_zero`, `kraftUpTo_succ`, `kraft_foldl`, the first codes
  `firstCode_zero`, `firstCode_succ`, `firstCode_kraft`, `firstCode_add_count_le`, the ranks
  `count_take_lt`, `count_take_lt_of_lt`, `isValidLengths_le`, `listGet_eq`, and
  `HuffmanTable.ofLengths_symOK` (every symbol with a nonzero length has a decodable code);
* known-answer vectors produced by zlib (an independent implementation), one per
  block type, and two rejections (distance code 30, `BTYPE = 11`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

theorem decoder_eq_some {bytes out rest : List UInt8} :
    decoder bytes = some (out, rest) ↔ deflateTake bytes = .ok (out, rest) :=
  Proofs.Formats.Compression.Deflate.decoder_eq_some

theorem consumes : decoder.Consumes := Proofs.Formats.Compression.Deflate.decoder_consumes

theorem roundTrip : RoundTrip decoder encoder := Proofs.Formats.Compression.Deflate.roundTrip

/-- Bytes after a DEFLATE stream are passed through untouched. -/
theorem deflateTake_append {bs out rest : List UInt8} (h : deflateTake bs = .ok (out, rest))
    (tail : List UInt8) : deflateTake (bs ++ tail) = .ok (out, rest ++ tail) :=
  Proofs.Formats.Compression.DeflateLocal.deflateTake_append h tail

/-- The same with a preset history (zlib dictionaries). -/
theorem deflateTakeWithHistory_append {history bs out rest : List UInt8}
    (h : deflateTakeWithHistory history bs = .ok (out, rest)) (tail : List UInt8) :
    deflateTakeWithHistory history (bs ++ tail) = .ok (out, rest ++ tail) :=
  Proofs.Formats.Compression.DeflateLocal.deflateTakeWithHistory_append h tail

/-- **The append law**: DEFLATE members are self-delimiting. -/
theorem «local» : decoder.Local := Proofs.Formats.Compression.DeflateLocal.decoder_local

theorem task_local : Task.local := «local»

/-- Raw DEFLATE with stored blocks, as a framework codec. -/
def codec : Codec := ⟨decoder, encoder, roundTrip⟩

/-- The output of `compress` is one complete member, decoded exactly to its end. -/
theorem compress_take {data c : ByteArray} (h : compress data = some c) :
    deflateTake c.data.toList = .ok (data.data.toList, []) :=
  Proofs.Formats.Compression.FixedEncoder.compress_take h

/-- The compressing encoder round-trips, whatever follows the member. -/
theorem roundTripFixed : RoundTrip decoder encoderFixed :=
  Proofs.Formats.Compression.FixedEncoder.roundTripFixed

/-- Raw DEFLATE with the compressing fixed-Huffman encoder, as a framework codec. -/
def codecFixed : Codec := ⟨decoder, encoderFixed, roundTripFixed⟩

/-- **Output bound**: each consumed input byte yields at most 2064 output bytes
(a token consumes at least one bit and emits at most 258 bytes). -/
theorem output_le {bs out rest : List UInt8} (h : deflateTake bs = .ok (out, rest)) :
    out.length ≤ 2064 * (bs.length - rest.length) :=
  Proofs.Formats.Compression.Bounds.deflateTake_output_le h

/-- With a preset history, the newly produced output obeys the same bound. -/
theorem withHistory_output_le {history bs out rest : List UInt8}
    (h : deflateTakeWithHistory history bs = .ok (out, rest)) :
    out.length ≤ 2064 * (bs.length - rest.length) :=
  Proofs.Formats.Compression.Bounds.deflateTakeWithHistory_output_le h

theorem decoder_output_le {bytes out rest : List UInt8} (h : decoder bytes = some (out, rest)) :
    out.length ≤ 2064 * (bytes.length - rest.length) :=
  Proofs.Formats.Compression.Bounds.decoder_outputLe h

theorem decompress_output_le {c d : ByteArray} (h : decompress c = some d) :
    d.size ≤ 2064 * c.size :=
  Proofs.Formats.Compression.Bounds.decompress_output_le h

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

/-- The empty history is plain DEFLATE. -/
theorem withHistory_empty (input : List UInt8) :
    deflateTakeWithHistory [] input = deflateTake input :=
  _root_.Silmaril.Formats.Compression.Deflate.deflateTakeWithHistory_empty input

/-- With any history, a member consumes a prefix of its input. -/
theorem withHistory_suffix {history input out rest : List UInt8}
    (h : deflateTakeWithHistory history input = .ok (out, rest)) : rest <:+ input :=
  _root_.Silmaril.Formats.Compression.Deflate.deflateTakeWithHistory_suffix h

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

/-! ### Canonical Huffman codes -/

theorem listGet_eq {α : Type} (l : List α) (i : Nat) : listGet l i = l[i]? :=
  _root_.Silmaril.Formats.Compression.listGet_eq l i

section Canonical

variable (L : CodeLengths) (M : Nat)

theorem assignCodes_getElem? (j : Nat) :
    (assignCodes L M)[j]? =
      L[j]?.map (fun len =>
        canonEntry M (nextCode (countByLength L M)) j len ((L.take j).count len)) :=
  _root_.Silmaril.Formats.Compression.assignCodes_getElem? L M j

theorem kraftUpTo_zero : kraftUpTo L M 0 = 0 :=
  _root_.Silmaril.Formats.Compression.kraftUpTo_zero L M

theorem kraftUpTo_succ (k : Nat) :
    kraftUpTo L M (k + 1) = kraftUpTo L M k + L.count (k + 1) * 2 ^ (M - (k + 1)) :=
  _root_.Silmaril.Formats.Compression.kraftUpTo_succ L M k

theorem kraft_foldl (acc : Nat) :
    L.foldl (fun (acc : Nat) (len : Nat) => if len = 0 then acc else acc + (1 <<< (M - len))) acc =
      acc + kraftTotal L M :=
  _root_.Silmaril.Formats.Compression.kraft_foldl L M acc

theorem isValidLengths_le (h : isValidLengths L M = true) : ∀ x ∈ L, x ≤ M :=
  _root_.Silmaril.Formats.Compression.isValidLengths_le L M h

theorem firstCode_zero (hM : 0 < M) : firstCode L M 0 = 0 :=
  _root_.Silmaril.Formats.Compression.firstCode_zero L M hM

theorem firstCode_succ (m : Nat) (hm : m + 1 < M) :
    firstCode L M (m + 1) = (firstCode L M m + L.count (m + 1)) * 2 :=
  _root_.Silmaril.Formats.Compression.firstCode_succ L M m hm

theorem firstCode_kraft (m : Nat) (hm : m < M) :
    (firstCode L M m + L.count (m + 1)) * 2 ^ (M - (m + 1)) = kraftUpTo L M (m + 1) :=
  _root_.Silmaril.Formats.Compression.firstCode_kraft L M m hm

theorem firstCode_add_count_le (hv : isValidLengths L M = true) (m : Nat) (hm : m < M) :
    firstCode L M m + L.count (m + 1) ≤ 2 ^ (m + 1) :=
  _root_.Silmaril.Formats.Compression.firstCode_add_count_le L M hv m hm

end Canonical

theorem count_take_lt (L : List Nat) (s : Nat) (hs : s < L.length) :
    (L.take s).count L[s] < L.count L[s] :=
  _root_.Silmaril.Formats.Compression.count_take_lt L s hs

theorem count_take_lt_of_lt (L : List Nat) (j s : Nat) (hj : j < s) (hs : s < L.length) :
    (L.take j).count L[j] < (L.take s).count L[j] :=
  _root_.Silmaril.Formats.Compression.count_take_lt_of_lt L j s hj hs

/-- Every symbol with a nonzero code length in a table built by `HuffmanTable.ofLengths` has a
code the LSB decoder recovers. -/
theorem HuffmanTable.ofLengths_symOK {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) {s : Nat} (hs : s < L.length)
    (hpos : 0 < L[s]) : t.SymOK s :=
  _root_.Silmaril.Formats.Compression.HuffmanTable.ofLengths_symOK h hs hpos

end Silmaril.Formats.Compression.Deflate

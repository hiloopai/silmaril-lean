module

public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Deflate.Thms
public import Silmaril.Formats.Compression.Checksum.Thms
public import Silmaril.Formats.Compression.Vectors
import Silmaril.Proofs.Formats.Compression.Zlib
import Silmaril.Raw.Formats.Compression.Zlib.Take
import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
import Silmaril.Raw.Formats.Compression.Vectors

/-!
# zlib (RFC 1950): facts

Proved (standard axioms):

* `take_eq_decoder`: the format module's `zlibTake` is the framework container
  `framing.wrap Deflate.decoder`, so the framework laws apply;
* `consumes`, `decoder_trailer`: a member consumes a prefix ending in the
  Adler-32 trailer of its output, followed by the untouched rest;
* `roundTrip`, `codec`, `compress_eq`, `decompress_compress`: the stored
  encoder round-trips, as a member followed by anything and as a whole buffer;
* `decompress_eq`: whole-buffer decoding is `decoder.whole`;
* `local_of_deflate`: the append law for zlib members follows from the one for
  DEFLATE (`Deflate.Task.local`);
* known answers: CPython's `zlib.compress(b"hello")` at levels 6 and 0, our
  encoder agreeing with CPython byte for byte at level 0, and rejections of a
  corrupted Adler-32 and of `FDICT = 1` without a dictionary;
* preset dictionaries: without `FDICT` the dictionary is ignored; with it, the
  dictionary's Adler-32 is checked and its bytes seed the history.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zlib

theorem take_eq_decoder : take = decoder := Proofs.Formats.Compression.Zlib.take_eq_decoder

theorem consumes : decoder.Consumes := Proofs.Formats.Compression.Zlib.consumes

/-- A member ends with the Adler-32 trailer of its output, then the rest. -/
theorem decoder_trailer {bytes out rest : List UInt8} (h : decoder bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (trailer out ++ rest) :=
  Proofs.Formats.Compression.Zlib.decoder_trailer h

theorem roundTrip : RoundTrip decoder encoder := Proofs.Formats.Compression.Zlib.roundTrip

/-- zlib with stored blocks, as a framework codec. -/
def codec : Codec := ⟨decoder, encoder, roundTrip⟩

theorem local_of_deflate (h : Deflate.Task.local) : decoder.Local :=
  Proofs.Formats.Compression.Zlib.local_of_deflate h

theorem decompress_eq (bytes : ByteArray) :
    decompress bytes = (decoder.whole bytes.data.toList).map (fun out => ⟨out.toArray⟩) :=
  Proofs.Formats.Compression.Zlib.decompress_eq bytes

theorem compress_eq (data : ByteArray) : (compress data).data.toList = encoder data.data.toList :=
  Proofs.Formats.Compression.Zlib.compress_eq data

theorem decompress_compress (data : ByteArray) : decompress (compress data) = some data :=
  zlibDecompress_zlibCompress data

set_option maxRecDepth 100000 in
/-- CPython's `zlib.compress(b"hello")` is one member decoding to `hello`. -/
theorem decoder_sampleHello : decoder sampleHello = some (helloBytes, []) := by
  rw [← take_eq_decoder]; decide

theorem helloBytes_eq_toUTF8 : "hello".toUTF8.toList = helloBytes := by
  rw [Compression.helloBytes_eq_toUTF8]; decide +kernel

theorem decompress_cpython_fixed : decompress zlibCpythonFixed = some Compression.helloBytes :=
  zlibDecompress_cpython_fixed

theorem decompress_cpython_stored : decompress zlibCpythonStored = some Compression.helloBytes :=
  zlibDecompress_cpython_stored

/-- The stored-block encoder agrees with CPython's `zlib.compress(b"hello", 0)`. -/
theorem compress_hello_eq_cpython : compress Compression.helloBytes = zlibCpythonStored :=
  zlibCompress_hello_eq_cpython

/-- The level-6 vector with its last Adler-32 byte changed (`15` → `16`) is rejected. -/
theorem decompress_bad_adler :
    decompress ⟨#[0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c, 0x02,
      0x16]⟩ = none :=
  zlibDecompress_bad_adler

/-- A stream asking for a preset dictionary is rejected by the dictionary-free decoder. -/
theorem decompress_fdict (cmf flg : UInt8) (rest : List UInt8) (h : flg &&& 0x20 ≠ 0) :
    decompress ⟨(cmf :: flg :: rest).toArray⟩ = none :=
  zlibDecompress_fdict cmf flg rest h

/-- Without `FDICT`, an offered dictionary is ignored. -/
theorem takeWithDictionary_eq_take (dictionary input : List UInt8)
    (hfree : ∀ header body, ZlibDictionary.checkHeader input = some (header, body) →
      header.dictionaryID = none) :
    takeWithDictionary dictionary input = take input :=
  ZlibDictionary.takeWithDictionary_eq_zlibTake dictionary input hfree

/-- With `FDICT`, stored data decodes when the dictionary's Adler-32 matches. -/
theorem takeWithDictionary_stored (dictionary data tail : List UInt8) :
    takeWithDictionary dictionary
      ([0x78, 0x20] ++ be32Bytes (ZlibDictionary.dictionaryChecksum dictionary) ++
        (Deflate.storedBytes data ++ ((zlibTrailer ⟨data.toArray⟩).data.toList ++ tail))) =
      some (data, tail) :=
  ZlibDictionary.takeWithDictionary_storedBytes dictionary data tail

/-- A different dictionary is rejected. -/
theorem takeWithDictionary_wrong (dictionary offered body : List UInt8)
    (hwrong : ZlibDictionary.dictionaryChecksum offered ≠
      ZlibDictionary.dictionaryChecksum dictionary) :
    takeWithDictionary offered
      ([0x78, 0x20] ++ be32Bytes (ZlibDictionary.dictionaryChecksum dictionary) ++ body) = none :=
  ZlibDictionary.takeWithDictionary_wrong_dictionary dictionary offered body hwrong

/-- Dictionary `AB`: a fixed-Huffman match into the dictionary expands. -/
theorem dictionary_match :
    takeWithDictionary [65, 66] [120, 32, 0, 198, 0, 132, 115, 4, 67, 0, 5, 100, 1, 138, 170] =
      some ([65, 66, 65, 66, 65, 66], [170]) :=
  ZlibDictionary.dictionary_match_checked

/-- The same member with dictionary `AC` fails its DICTID check. -/
theorem dictionary_wrong_rejected :
    takeWithDictionary [65, 67] [120, 32, 0, 198, 0, 132, 115, 4, 67, 0, 5, 100, 1, 138, 170] =
      none :=
  ZlibDictionary.wrong_dictionary_rejected

end Silmaril.Formats.Compression.Zlib

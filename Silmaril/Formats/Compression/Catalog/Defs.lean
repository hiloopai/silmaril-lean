module

public import Silmaril.Formats.Compression.Format.Defs
public import Silmaril.Formats.Compression.Transform.Defs
public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Formats.Compression.DeflateSpec.Defs
public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.GzipHeader.Defs
public import Silmaril.Formats.Compression.Inflate.Defs

/-!
# The catalogue of compressed formats

DEFLATE, zlib and gzip as `Format`s, with the encodings and the claim lists their
certificates (`Catalog.Thms`) prove. The formats **reuse** the existing decoders;
`Catalog.Thms` proves that they denote `Deflate.decoder`, `Zlib.decoder`,
`Zlib.takeWithDictionary`, `Gzip.decoder` and `Gzip.decompress`, so code using
those (and `Zlib.codec`, `Gzip.codec`) is unaffected.

* `deflate`: `Params` is the preset history (empty for plain RFC 1951 streams),
  `Error` is `Deflate.DecompressError`, `decodeE` is `deflateTakeWithHistory`;
* `zlib`: `Params` is the offered preset dictionary (`none`: dictionary-free).
  A member is `(zlibFraming dictionary).wrapDep deflate.decode`: the header
  (`zlibParseHeader`) resolves the DEFLATE history from `FDICT`, the `DICTID` and the
  offered dictionary (`zlibHistory`), and the trailer is the Adler-32 check;
* `gzipMember`: one RFC 1952 member, no parameters; `gzipFile`: the whole-file
  `Transform` of one or more members;
* `identity`: the identity coding, as a format whose one member is the whole
  input. It is not self-delimiting, and its certificate says so by omission
  (`identity_not_local` proves the append law fails);
* `deflateClaims`, `zlibClaims`, `gzipClaims`, `identityClaims`: exactly what is
  proved for each, in the vocabulary of `Capability`. The DEFLATE relational
  spec (`DeflateSpec.Stream .strict`) is claimed for the empty history only, and
  the streaming machines for the dictionary-free formats only.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Catalog

open Inflate.Stream

/-! ## DEFLATE -/

/-- Raw DEFLATE (RFC 1951) with a preset history. -/
def deflate : Format where
  Params := List UInt8
  Error := Deflate.DecompressError
  decodeE := Deflate.deflateTakeWithHistory

/-- The independent RFC 1951 semantics, as a relation; it describes streams
with an empty history. -/
def deflateSpec : Rel deflate := fun _ input out rest => DeflateSpec.Stream .strict input out rest

/-- Stored blocks, read back with any history. -/
def deflateStored : Encoding deflate where
  EParams := List UInt8
  params history := history
  encode _ := Deflate.encoder

/-- Greedy LZ77 with one fixed-Huffman block, for the empty history. -/
def deflateFixed : Encoding deflate where
  EParams := Unit
  params _ := []
  encode _ := Deflate.encoderFixed

/-- What is proved about DEFLATE. -/
def deflateClaims : List (Capability deflate) :=
  [.consumes Scope.all, .local Scope.all,
   .spec (Scope.only []) deflateSpec, .deterministic (Scope.only []) deflateSpec,
   .vector [] [0x4b, 0x4c, 0x4a, 0x06, 0x00] [0x61, 0x62, 0x63] [],
   .roundTrip deflateStored, .roundTrip deflateFixed,
   .outputLinear Scope.all 2064,
   .callCapacity (Inflate.raw .v131) RawMachine.output RawMachine.Call.capacity,
   .callCapacity (Inflate.raw .develop) RawMachine.output RawMachine.Call.capacity,
   .streamSound [] (Inflate.raw .v131), .streamComplete [] (Inflate.raw .v131),
   .streamSound [] (Inflate.raw .develop), .streamComplete [] (Inflate.raw .develop)]

/-- No integrity check, and the usual length side channel. -/
def deflateSecurity : Security where
  hazards := [.noIntegrity, .compressionLengthOracle]

/-! ## zlib -/

/-- The DEFLATE history a zlib header selects: none without `FDICT`; with it,
the window suffix of the offered dictionary when its Adler-32 is the header's
`DICTID` (in the 32 KiB profile), and rejection otherwise. -/
def zlibHistory (dictionary : Option (List UInt8)) (header : ZlibDictionary.Header) :
    Option (List UInt8) :=
  match header.dictionaryID, dictionary with
  | none, _ => some []
  | some _, none => none
  | some expected, some d =>
    if ZlibDictionary.supportedDictionaryProfile header ∧
        ZlibDictionary.dictionaryChecksum d = expected then
      some (ZlibDictionary.history d)
    else none

/-- The zlib header, with the DEFLATE history as its metadata. -/
def zlibParseHeader (dictionary : Option (List UInt8)) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  (ZlibDictionary.checkHeader bytes).bind fun (header, body) =>
    (zlibHistory dictionary header).map (·, body)

/-- The RFC 1950 container, with the offered dictionary. -/
def zlibFraming (dictionary : Option (List UInt8)) : Framing (List UInt8) where
  header := zlibParseHeader dictionary
  trailer _ out afterBody := zlibCheckTrailer out afterBody

/-- zlib (RFC 1950), with an optional offered preset dictionary. -/
def zlib : Format :=
  Format.ofDecoder (Option (List UInt8)) fun dictionary =>
    (zlibFraming dictionary).wrapDep deflate.decode

/-- The independent closed form of Adler-32 (RFC 1950 §8.2). -/
def adler32Ref (bytes : List UInt8) : UInt32 :=
  UInt32.ofNat (adler32Symbolic (bytes.map UInt8.toNat))

def zlibStored : Encoding zlib := ⟨Unit, fun _ => none, fun _ => Zlib.encoder⟩

def zlibFixed : Encoding zlib := ⟨Unit, fun _ => none, fun _ => Zlib.encoderFixed⟩

/-- The `FDICT = 1` header for `dictionary`: `78 20` and its `DICTID`. -/
def zlibDictionaryHeader (dictionary : List UInt8) : List UInt8 :=
  [0x78, 0x20] ++ be32Bytes (ZlibDictionary.dictionaryChecksum dictionary)

/-- Stored blocks under a preset-dictionary header, for that dictionary. -/
def zlibStoredWithDictionary : Encoding zlib where
  EParams := List UInt8
  params := some
  encode dictionary data :=
    zlibDictionaryHeader dictionary ++ Deflate.encoder data ++
      (zlibTrailer ⟨data.toArray⟩).data.toList

/-- What is proved about zlib. -/
def zlibClaims : List (Capability zlib) :=
  [.consumes Scope.all, .local Scope.all,
   .trailer Scope.all Zlib.trailer, .checksumSpec Checksum.adler32 adler32Ref,
   .vector none Zlib.sampleHello Zlib.helloBytes [],
   .vector (some [65, 66]) [120, 32, 0, 198, 0, 132, 115, 4, 67, 0, 5, 100, 1, 138, 170]
     [65, 66, 65, 66, 65, 66] [170],
   .roundTrip zlibStored, .roundTrip zlibFixed, .roundTrip zlibStoredWithDictionary,
   .outputLinear Scope.all 2064,
   .callCapacity (Inflate.member .v131 .zlib) MemberMachine.output RawMachine.Call.capacity,
   .callCapacity (Inflate.member .develop .zlib) MemberMachine.output RawMachine.Call.capacity,
   .streamSound none (Inflate.member .v131 .zlib),
   .streamRejectSound none (Inflate.member .v131 .zlib),
   .streamComplete none (Inflate.member .v131 .zlib),
   .streamSound none (Inflate.member .develop .zlib),
   .streamRejectSound none (Inflate.member .develop .zlib),
   .streamComplete none (Inflate.member .develop .zlib)]

def zlibSecurity : Security where
  hazards := [.checksumNotMac "Adler-32", .compressionLengthOracle]

/-! ## gzip -/

/-- One gzip (RFC 1952) member. -/
def gzipMember : Format := Format.ofDecoder Unit fun _ => Gzip.decoder

/-- A gzip file: one or more members. -/
def gzipFile : Transform := Transform.members gzipMember

/-- A member with any valid header (name, comment, extra field, MTIME, OS, FHCRC)
and stored blocks. -/
def gzipHeaders : Encoding gzipMember where
  EParams := { h : GzipHeader.Header // h.Valid }
  params _ := ()
  encode h := GzipHeader.encodeMember h.1

def gzipFixed : Encoding gzipMember := ⟨Unit, fun _ => (), fun _ => Gzip.encoderFixed⟩

/-- What is proved about gzip members. -/
def gzipClaims : List (Capability gzipMember) :=
  [.consumes Scope.all, .local Scope.all,
   .trailer Scope.all Gzip.trailer, .checksumSpec Checksum.crc32 crc32Spec,
   .roundTrip gzipHeaders, .roundTrip gzipFixed,
   .outputLinear Scope.all 2064,
   .callCapacity (Inflate.member .v131 .gzip) MemberMachine.output RawMachine.Call.capacity,
   .callCapacity (Inflate.member .develop .gzip) MemberMachine.output RawMachine.Call.capacity,
   .streamSound () (Inflate.member .v131 .gzip),
   .streamRejectSound () (Inflate.member .v131 .gzip),
   .streamComplete () (Inflate.member .v131 .gzip),
   .streamSound () (Inflate.member .develop .gzip),
   .streamRejectSound () (Inflate.member .develop .gzip),
   .streamComplete () (Inflate.member .develop .gzip)]

def gzipSecurity : Security where
  hazards := [.checksumNotMac "CRC-32", .compressionLengthOracle]

/-! ## identity -/

/-- The identity coding: one member is the whole input. -/
def identity : Format where
  Params := Unit
  Error := Empty
  decodeE _ bytes := .ok (bytes, [])

/-- What is proved about the identity format: it is **not** self-delimiting,
and so claims neither `local` nor a member round trip. -/
def identityClaims : List (Capability identity) :=
  [.consumes Scope.all, .outputLinear Scope.all 1, .vector () [1, 2] [1, 2] []]

def identitySecurity : Security where
  hazards := [.noIntegrity]

end Silmaril.Formats.Compression.Catalog

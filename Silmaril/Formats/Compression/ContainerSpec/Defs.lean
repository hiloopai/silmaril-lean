module

public import Silmaril.Formats.Compression.DeflateSpec.Defs
public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Silmaril.Formats.Compression.GzipHeader.Defs

/-!
# zlib (RFC 1950) and gzip (RFC 1952) containers, declaratively

Relations saying which byte strings are zlib and gzip members and files and
what they decode to, written to be read against the RFCs. Like `DeflateSpec`,
they share nothing with the decoders (`Zlib.take`, `gzipMember`,
`gzipDecompress`): the body is a `DeflateSpec.Stream`, the check values are the
*specifications* `adler32Symbolic` (RFC 1950 §8.2, closed form) and `crc32Spec`
(ISO 3309 / ITU-T V.42 polynomial division, RFC 1952 §8), and multi-byte numbers
are read by `leValue`/`beValue`. The only shared definition is the record
`GzipHeader.Header`, used to name the parsed header fields.
`ContainerSpec.Thms` proves the decoders sound and complete for these relations.

* RFC 1950 §2.2: `ZlibHeader` (CMF/FLG), `ZlibMember` (`FDICT = 0`),
  `ZlibDictMember` (`FDICT = 1`, `DICTID` and the dictionary as DEFLATE history);
* RFC 1952 §2.3: `GzipFlags`, `ExtraField`, `ZeroTerminated`, `HeaderCrc`,
  `GzipMemberHeader`, `GzipMember`; §2.2: `GzipFile`, one or more members;
* profiles: `ZlibMemberWindowed`, `ZlibDictMemberAnyWindow`,
  `ZlibDictMemberWindowed`, `GzipFilePrefix`.

## Policy

* The DEFLATE body is read under `DeflateSpec.Policy.strict` (zlib's policy; see
  `DeflateSpec.Defs`).
* zlib: `FLEVEL` is not constrained (RFC 1950 §2.2: "not needed for
  decompression"). In `ZlibMember` and `ZlibDictMember` the window size `CINFO`
  does not limit back-reference distances (zlib checks this only with
  `INFLATE_STRICT`); the separately named `ZlibMemberWindowed` and
  `ZlibDictMemberWindowed` do limit them to `zlibWindow cmf = 2 ^ (CINFO + 8)`.
* zlib with a preset dictionary: `ZlibDictMember` specifies only `CINFO = 7`
  (32 KiB window), matching `Zlib.takeWithDictionary`; `ZlibDictMemberAnyWindow`
  and `ZlibDictMemberWindowed` allow every `CINFO`, as RFC 1950 does.
* gzip: FEXTRA subfields, the ISO 8859-1 content of FNAME/FCOMMENT, `XFL` and
  `OS` are not constrained (RFC 1952 §2.3.1.2: a compliant decompressor "need
  not examine any other part of the header"). A gzip file (`GzipFile`) has no
  bytes after its last member; `GzipFilePrefix` is the separately named
  suffix-lenient profile (members read greedily, then a suffix at which no
  member starts).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.ContainerSpec

open DeflateSpec

/-! ## Numbers (RFC 1950 §2.1, RFC 1952 §2.1) -/

/-- An unsigned number stored least significant byte first (RFC 1952 §2.1). -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- An unsigned number stored most significant byte first (RFC 1950 §2.1,
"MSB order"). -/
def beValue (bytes : List UInt8) : Nat := leValue bytes.reverse

/-- The Adler-32 of `data`, by its closed form (RFC 1950 §8.2, §9). -/
def adler32Of (data : List UInt8) : Nat := adler32Symbolic (data.map UInt8.toNat)

/-- The CRC-32 of `data`, by polynomial division (RFC 1952 §8). -/
def crc32Of (data : List UInt8) : Nat := (crc32Spec data).toNat

/-! ## zlib (RFC 1950 §2.2) -/

/-- `CMF` and `FLG`: `CM` (bits 0–3 of `CMF`) is 8 ("deflate"), `CINFO` (bits 4–7)
is at most 7 ("Values of CINFO above 7 are not allowed"), and "CMF*256 + FLG is a
multiple of 31" (`FCHECK`). -/
structure ZlibHeader (cmf flg : UInt8) : Prop where
  cm : cmf.toNat % 16 = 8
  cinfo : cmf.toNat / 16 ≤ 7
  fcheck : (cmf.toNat * 256 + flg.toNat) % 31 = 0

/-- `FDICT`, bit 5 of `FLG`: a preset dictionary identifier follows. -/
def fdict (flg : UInt8) : Bool := flg.toNat.testBit 5

/-- **A zlib member without a preset dictionary** at the front of `input`,
decoding to `out`, followed by `rest`: `CMF`, `FLG`, the DEFLATE stream, then
`ADLER32`, the Adler-32 of the uncompressed data, most significant byte first. -/
def ZlibMember (input out rest : List UInt8) : Prop :=
  ∃ cmf flg body adler : _,
    input = cmf :: flg :: body ∧ ZlibHeader cmf flg ∧ fdict flg = false ∧
    Stream .strict body out (adler ++ rest) ∧
    adler.length = 4 ∧ beValue adler = adler32Of out

/-- **A zlib member with the preset dictionary `dictionary`**: `FDICT = 1`, then
`DICTID`, the Adler-32 of the dictionary (most significant byte first); the
DEFLATE stream is decoded with the dictionary as history ("the dictionary … is
initially fed to the compressor without producing any compressed output"), and
`ADLER32` covers the output only. Only `CINFO = 7` is specified (see Policy). -/
def ZlibDictMember (dictionary input out rest : List UInt8) : Prop :=
  ∃ cmf flg dictid body adler : _,
    input = cmf :: flg :: (dictid ++ body) ∧ ZlibHeader cmf flg ∧ fdict flg = true ∧
    cmf.toNat / 16 = 7 ∧ dictid.length = 4 ∧ beValue dictid = adler32Of dictionary ∧
    StreamWithHistory .strict dictionary body out (adler ++ rest) ∧
    adler.length = 4 ∧ beValue adler = adler32Of out

/-! ### zlib profiles: the `CINFO` window, dictionaries for every window

`ZlibMember` and `ZlibDictMember` do not bound back-reference distances by the
window `CINFO` announces (as zlib without `INFLATE_STRICT`). The relations below
are separately named profiles. -/

/-- The LZ77 window a zlib header announces: "CINFO is the base-2 logarithm of
the LZ77 window size, minus eight", so `2 ^ (CINFO + 8)` bytes. -/
def zlibWindow (cmf : UInt8) : Nat := 2 ^ (cmf.toNat / 16 + 8)

/-- **A zlib member within its window**: `ZlibMember`, with every back-reference
distance at most `zlibWindow cmf` (RFC 1950 §2.2, `CINFO`). -/
def ZlibMemberWindowed (input out rest : List UInt8) : Prop :=
  ∃ cmf flg body adler : _,
    input = cmf :: flg :: body ∧ ZlibHeader cmf flg ∧ fdict flg = false ∧
    StreamWithin .strict (some (zlibWindow cmf)) body out (adler ++ rest) ∧
    adler.length = 4 ∧ beValue adler = adler32Of out

/-- **A zlib member with the preset dictionary `dictionary`, for every `CINFO`**:
`ZlibDictMember` without the `CINFO = 7` restriction. The whole dictionary is
the history; back-references are bounded only by RFC 1951's 32768, so a stream
may reach up to 32 KiB into the dictionary whatever its `CINFO`. -/
def ZlibDictMemberAnyWindow (dictionary input out rest : List UInt8) : Prop :=
  ∃ cmf flg dictid body adler : _,
    input = cmf :: flg :: (dictid ++ body) ∧ ZlibHeader cmf flg ∧ fdict flg = true ∧
    dictid.length = 4 ∧ beValue dictid = adler32Of dictionary ∧
    StreamWithHistory .strict dictionary body out (adler ++ rest) ∧
    adler.length = 4 ∧ beValue adler = adler32Of out

/-- **A zlib member with a preset dictionary, within its window**: as
`ZlibDictMemberAnyWindow`, with every back-reference distance at most
`zlibWindow cmf`, so only the last `zlibWindow cmf` bytes of the dictionary can
be referenced. -/
def ZlibDictMemberWindowed (dictionary input out rest : List UInt8) : Prop :=
  ∃ cmf flg dictid body adler : _,
    input = cmf :: flg :: (dictid ++ body) ∧ ZlibHeader cmf flg ∧ fdict flg = true ∧
    dictid.length = 4 ∧ beValue dictid = adler32Of dictionary ∧
    StreamWithHistoryWithin .strict (some (zlibWindow cmf)) dictionary body out (adler ++ rest) ∧
    adler.length = 4 ∧ beValue adler = adler32Of out

/-! ## gzip (RFC 1952 §2.3) -/

open GzipHeader (Header)

/-- `FLG` (§2.3.1) announces the fields of `hdr`: bit 0 `FTEXT`, bit 1 `FHCRC`,
bit 2 `FEXTRA`, bit 3 `FNAME`, bit 4 `FCOMMENT`; bits 5–7 are reserved and zero
(§2.4: a decompressor "must give an error indication if any reserved bit is
non-zero"). -/
structure GzipFlags (flg : UInt8) (hdr : Header) : Prop where
  ftext : flg.toNat.testBit 0 = hdr.text
  fhcrc : flg.toNat.testBit 1 = hdr.hcrc
  fextra : flg.toNat.testBit 2 = hdr.extra.isSome
  fname : flg.toNat.testBit 3 = hdr.name.isSome
  fcomment : flg.toNat.testBit 4 = hdr.comment.isSome
  reserved : flg.toNat < 32

/-- `FEXTRA`: `bytes` is `XLEN` (two bytes, least significant first), then the
`XLEN` bytes `x`. -/
def ExtraField (x bytes : List UInt8) : Prop :=
  ∃ xlen, xlen.length = 2 ∧ leValue xlen = x.length ∧ bytes = xlen ++ x

/-- `FNAME`, `FCOMMENT`: `bytes` is `s` "terminated by a zero byte"; `s` has no
zero byte. -/
def ZeroTerminated (s bytes : List UInt8) : Prop := 0 ∉ s ∧ bytes = s ++ [0]

/-- An optional field: absent (no bytes), or present and serialised by `field`. -/
def Optional (field : List UInt8 → List UInt8 → Prop) : Option (List UInt8) → List UInt8 → Prop
  | none, bytes => bytes = []
  | some x, bytes => field x bytes

/-- `FHCRC` (§2.3.1): when present, `bytes` is "the two least significant bytes
of the CRC32 for all bytes of the gzip header up to and not including the
CRC16", stored least significant byte first; `pre` is that header prefix. -/
def HeaderCrc (present : Bool) (pre bytes : List UInt8) : Prop :=
  if present then bytes.length = 2 ∧ leValue bytes = crc32Of pre % 65536 else bytes = []

/-- **A gzip member header** with fields `hdr` at the front of the input,
followed by `rest`: `ID1 = 1f`, `ID2 = 8b`, `CM = 8`, `FLG`, `MTIME` (four bytes,
least significant first), `XFL`, `OS`, then the optional `FEXTRA`, `FNAME`,
`FCOMMENT` and `FHCRC`, in that order. -/
inductive GzipMemberHeader : List UInt8 → Header → List UInt8 → Prop
  | mk {hdr : Header} {flg : UInt8} {mtime xb nb cb crc rest : List UInt8}
      (flags : GzipFlags flg hdr)
      (mtimeLength : mtime.length = 4) (mtimeValue : leValue mtime = hdr.mtime)
      (extra : Optional ExtraField hdr.extra xb)
      (name : Optional ZeroTerminated hdr.name nb)
      (comment : Optional ZeroTerminated hdr.comment cb)
      (hcrc : HeaderCrc hdr.hcrc ([0x1f, 0x8b, 8, flg] ++ mtime ++ [hdr.xfl, hdr.os] ++
        xb ++ nb ++ cb) crc) :
      GzipMemberHeader ([0x1f, 0x8b, 8, flg] ++ mtime ++ [hdr.xfl, hdr.os] ++
        xb ++ nb ++ cb ++ crc ++ rest) hdr rest

/-- **A gzip member** (§2.3) with header `hdr`, decoding to `out`, followed by
`rest`: the header, the DEFLATE stream, `CRC32` (the CRC-32 of the uncompressed
data) and `ISIZE` ("the size of the original (uncompressed) input data modulo
2^32"), both four bytes least significant first. -/
def GzipMember (input : List UInt8) (hdr : Header) (out rest : List UInt8) : Prop :=
  ∃ body crc isize : _, GzipMemberHeader input hdr body ∧
    Stream .strict body out (crc ++ isize ++ rest) ∧
    crc.length = 4 ∧ leValue crc = crc32Of out ∧
    isize.length = 4 ∧ leValue isize = out.length % 2 ^ 32

/-- **A gzip file** (§2.2): "a series of members", one or more, every byte part
of a member, decoding to the concatenation of their outputs. -/
inductive GzipFile : List UInt8 → List UInt8 → Prop
  | last {input hdr out} : GzipMember input hdr out [] → GzipFile input out
  | cons {input hdr out rest out'} :
      GzipMember input hdr out rest → GzipFile rest out' → GzipFile input (out ++ out')

/-- **A gzip file followed by bytes that are not a member** (the suffix-lenient
profile): one or more members, read greedily, then `rest`, the first suffix at
which no member starts (possibly empty). -/
inductive GzipFilePrefix : List UInt8 → List UInt8 → List UInt8 → Prop
  | last {input hdr out rest} :
      GzipMember input hdr out rest → (∀ hdr' out' rest', ¬ GzipMember rest hdr' out' rest') →
      GzipFilePrefix input out rest
  | cons {input hdr out mid out' rest} :
      GzipMember input hdr out mid → GzipFilePrefix mid out' rest →
      GzipFilePrefix input (out ++ out') rest

end Silmaril.Formats.Compression.ContainerSpec

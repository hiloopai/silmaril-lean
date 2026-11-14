module

public import Silmaril.Formats.Compression.GzipHeader.Defs
public import Silmaril.Formats.Compression.Gzip.Thms
import Silmaril.Proofs.Formats.Compression.GzipHeader

/-!
# gzip member headers (RFC 1952 §2.3): facts

Proved (standard axioms):

* `parseHeader_agrees`: `parseHeader` accepts exactly the inputs `Gzip.checkHeader`
  (and so the member decoder `Gzip.decoder`) accepts, with the same rest;
* `parseHeader_encodeHeader`, `checkHeader_encodeHeader`: a valid header is read
  back as itself, by both parsers, whatever follows it;
* `roundTrip`: `encodeMember h` round-trips through `Gzip.decoder` for every valid
  `h`, and `encodeMember_default`: with the default header it is `Gzip.encoder`;
* known answers: the header of GNU gzip's `hello` vector, and a hand-built header
  with FEXTRA (one `AP` subfield), FNAME `hello.txt`, FCOMMENT and FHCRC (CRC16
  `0xC07A`, cross-checked with `zlib.crc32`), which a corrupted FHCRC makes the
  decoder reject.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.GzipHeader

/-- **Agreement**: the structured parser accepts exactly what the member decoder's
header check accepts, leaving the same rest. -/
theorem parseHeader_agrees (bytes : List UInt8) :
    (parseHeader bytes).map (fun p => ((), p.2)) = Gzip.checkHeader bytes :=
  Proofs.Formats.Compression.GzipHeader.parseHeader_agrees bytes

/-- **Round trip** of the header: a valid header is parsed back, rest untouched. -/
theorem parseHeader_encodeHeader {h : Header} (hv : h.Valid) (rest : List UInt8) :
    parseHeader (encodeHeader h ++ rest) = some (h, rest) :=
  Proofs.Formats.Compression.GzipHeader.parseHeader_encodeHeader hv rest

theorem checkHeader_encodeHeader {h : Header} (hv : h.Valid) (rest : List UInt8) :
    Gzip.checkHeader (encodeHeader h ++ rest) = some ((), rest) :=
  Proofs.Formats.Compression.GzipHeader.checkHeader_encodeHeader hv rest

/-- The container writes `encodeHeader h` and `Gzip.trailer`. -/
theorem writes {h : Header} (hv : h.Valid) : Gzip.framing.Writes (encodeHeader h) Gzip.trailer :=
  Proofs.Formats.Compression.GzipHeader.writes hv

/-- **A member with any valid header round-trips** through the gzip member decoder. -/
theorem roundTrip {h : Header} (hv : h.Valid) : RoundTrip Gzip.decoder (encodeMember h) :=
  Proofs.Formats.Compression.GzipHeader.roundTrip hv

theorem encodeHeader_default : encodeHeader default = Gzip.header := by decide

theorem encodeMember_default : encodeMember default = Gzip.encoder := by
  rw [encodeMember, encodeHeader_default]

/-! ## Known answers -/

/-- The header of `printf hello | gzip -n`: no flags, `MTIME = 0`, `XFL = 0`,
`OS = 3` (Unix). -/
def gnuHeader : Header :=
  { text := false, mtime := 0, xfl := 0, os := 3, extra := none, name := none,
    comment := none, hcrc := false }

theorem parseHeader_gnu :
    parseHeader gzipGnu.data.toList = some (gnuHeader, gzipGnu.data.toList.drop 10) := by decide

/-- A header with every optional field: FEXTRA holding one subfield `AP` (the
Apollo subfield ID RFC 1952 §2.3.1.1 lists) with data `01 02`, FNAME
`hello.txt`, FCOMMENT `hi`, FHCRC; `MTIME = 1700000000`, `XFL = 2`, `OS = 3`. -/
def fullHeader : Header :=
  { text := false, mtime := 1700000000, xfl := 2, os := 3,
    extra := some [0x41, 0x50, 0x02, 0x00, 0x01, 0x02],
    name := some [0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x2e, 0x74, 0x78, 0x74],
    comment := some [0x68, 0x69], hcrc := true }

/-- `fullHeader`, serialised. The last two bytes are FHCRC: in Python,
`zlib.crc32(header[:31]) & 0xffff == 0xc07a`. -/
def fullHeaderBytes : List UInt8 :=
  [0x1f, 0x8b, 0x08, 0x1e, 0x00, 0xf1, 0x53, 0x65, 0x02, 0x03, 0x06, 0x00, 0x41, 0x50,
   0x02, 0x00, 0x01, 0x02, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x2e, 0x74, 0x78, 0x74, 0x00,
   0x68, 0x69, 0x00, 0x7a, 0xc0]

theorem fullHeader_valid : fullHeader.Valid := by decide

theorem fullHeader_conventions :
    fullHeader.extraWellFormed ∧ fullHeader.latin1Strict ∧ fullHeader.xflDefined := by decide

theorem encodeHeader_full : encodeHeader fullHeader = fullHeaderBytes := by
  decide +kernel

theorem parseHeader_full : parseHeader fullHeaderBytes = some (fullHeader, []) := by decide

theorem checkHeader_full : Gzip.checkHeader fullHeaderBytes = some ((), []) := by decide

theorem parseSubfields_full :
    parseSubfields [0x41, 0x50, 0x02, 0x00, 0x01, 0x02] = some [(0x41, 0x50, [0x01, 0x02])] := by
  decide

/-- With the first FHCRC byte changed (`7a` → `7b`) the header is rejected. -/
theorem checkHeader_bad_hcrc :
    Gzip.checkHeader (fullHeaderBytes.set 31 0x7b) = none := by decide

end Silmaril.Formats.Compression.GzipHeader

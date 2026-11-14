module

public import Silmaril.Formats.Compression.Gzip.Defs

/-!
# gzip member headers (RFC 1952 §2.3)

The gzip member decoder (`Gzip.checkHeader`) checks the header and skips its
optional fields, as RFC 1952 §2.3.1.2 allows. This topic parses the same header
into a structure and writes one back:

* `Header`: FTEXT, MTIME, XFL, OS, the optional FEXTRA, FNAME and FCOMMENT
  fields, and whether FHCRC is present;
* `parseHeader`: the structured parser. It accepts exactly what `checkHeader`
  accepts (magic, `CM = 8`, reserved FLG bits clear, optional fields present,
  the FHCRC header CRC correct) and leaves the same rest (`GzipHeader.parseHeader_agrees`);
* `encodeHeader`, `Header.Valid`: the writer, computing the FHCRC CRC16 (the low
  16 bits of the CRC-32 of the header bytes before it) when `hcrc` is set, and
  the conditions under which `parseHeader` reads back what it wrote;
* `encodeMember h`: a gzip member with header `h`, stored DEFLATE blocks and the
  CRC-32/ISIZE trailer;
* `parseSubfields`, `Header.extraWellFormed`, `Header.latin1Strict`,
  `Header.xflDefined`: what RFC 1952 says about the content of the optional fields
  and XFL. None of them is checked by the decoder, as §2.3.1.2 permits: a
  compliant decompressor "need not examine any other part of the header".
-/

@[expose] public section

namespace Silmaril.Formats.Compression.GzipHeader

/-- A parsed gzip member header. `CM` is always 8 (deflate) and is not stored.
`mtime` is the 32-bit little-endian MTIME field; `extra` is the FEXTRA payload
(without its XLEN prefix), `name` and `comment` the FNAME and FCOMMENT bytes
(without their terminating zero). `hcrc` records whether FHCRC is present; its
value is determined by the bytes before it. -/
structure Header where
  text : Bool
  mtime : Nat
  xfl : UInt8
  os : UInt8
  extra : Option (List UInt8)
  name : Option (List UInt8)
  comment : Option (List UInt8)
  hcrc : Bool
  deriving DecidableEq, Repr

/-- The default header is the one `Gzip.header` writes: no flags, `MTIME = 0`,
`XFL = 0`, `OS = 255` (unknown), the defaults RFC 1952 §2.3.1.2 suggests. -/
instance : Inhabited Header :=
  ⟨{ text := false, mtime := 0, xfl := 0, os := 255, extra := none, name := none,
     comment := none, hcrc := false }⟩

/-! ## Parsing -/

/-- FEXTRA: `XLEN` (two bytes, little-endian), then that many bytes. -/
def parseExtra : List UInt8 → Option (List UInt8 × List UInt8)
  | x0 :: x1 :: r =>
    let n := x0.toNat + 256 * x1.toNat
    if n ≤ r.length then some (r.take n, r.drop n) else none
  | _ => none

/-- FNAME, FCOMMENT: bytes up to a terminating zero, which is consumed. -/
def parseZeroTerminated : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | 0 :: rest => some ([], rest)
  | b :: rest => (parseZeroTerminated rest).map fun p => (b :: p.1, p.2)

/-- An optional field: parsed with `p` when `present`, absent otherwise. -/
def optField (present : Prop) [Decidable present] (p : List UInt8 → Option (List UInt8 × List UInt8))
    (bs : List UInt8) : Option (Option (List UInt8) × List UInt8) :=
  if present then (p bs).map fun q => (some q.1, q.2) else some (none, bs)

/-- The optional fields FEXTRA, FNAME, FCOMMENT selected by `flg`, in that order. -/
def parseOptional (flg : UInt8) (bs : List UInt8) :
    Option ((Option (List UInt8) × Option (List UInt8) × Option (List UInt8)) × List UInt8) :=
  (optField (flg &&& gzipFEXTRA ≠ 0) parseExtra bs).bind fun p1 =>
    (optField (flg &&& gzipFNAME ≠ 0) parseZeroTerminated p1.2).bind fun p2 =>
      (optField (flg &&& gzipFCOMMENT ≠ 0) parseZeroTerminated p2.2).map fun p3 =>
        ((p1.1, p2.1, p3.1), p3.2)

/-- FHCRC, when `flg` selects it: two bytes, little-endian, equal to the low 16
bits of the CRC-32 of the header bytes before them. `member` is the member from
its first byte and `afterOpt` what follows the other optional fields. This is the
check `gzipSkipHeaderFields` performs. -/
def checkHcrc (flg : UInt8) (member afterOpt : List UInt8) : Option (List UInt8) :=
  if flg &&& gzipFHCRC ≠ 0 then
    match afterOpt with
    | c0 :: c1 :: r =>
      let headerLen := member.length - afterOpt.length
      let crc16 := crc32List ((member.take headerLen).map (λ b => b.toNat)) % 65536
      if c0.toNat + 256 * c1.toNat = crc16 then some r else none
    | _ => none
  else some afterOpt

/-- **The member header**, parsed (RFC 1952 §2.3): the same acceptance as
`Gzip.checkHeader`, returning the fields it skips. -/
def parseHeader (bytes : List UInt8) : Option (Header × List UInt8) :=
  match bytes with
  | 0x1F :: 0x8B :: cm :: flg :: m0 :: m1 :: m2 :: m3 :: xfl :: os :: rest =>
    if cm ≠ 8 ∨ flg &&& gzipFRESERVED ≠ 0 then none
    else
      match parseOptional flg rest with
      | none => none
      | some ((extra, name, comment), afterOpt) =>
        match checkHcrc flg bytes afterOpt with
        | none => none
        | some r =>
          some ({ text := decide (flg &&& gzipFTEXT ≠ 0), mtime := le32Val m0 m1 m2 m3,
                  xfl, os, extra, name, comment, hcrc := decide (flg &&& gzipFHCRC ≠ 0) }, r)
  | _ => none

/-! ## Writing -/

/-- The low 16 bits of `n`, little-endian. -/
def le16Bytes (n : Nat) : List UInt8 := [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256)]

/-- The FLG byte of a header: FTEXT, FHCRC, FEXTRA, FNAME, FCOMMENT. -/
def Header.flg (h : Header) : UInt8 :=
  UInt8.ofNat (h.text.toNat + 2 * h.hcrc.toNat + 4 * h.extra.isSome.toNat +
    8 * h.name.isSome.toNat + 16 * h.comment.isSome.toNat)

/-- The optional fields FEXTRA, FNAME, FCOMMENT, serialised. -/
def encodeOptional (h : Header) : List UInt8 :=
  (match h.extra with | none => [] | some x => le16Bytes x.length ++ x) ++
  (match h.name with | none => [] | some s => s ++ [0]) ++
  (match h.comment with | none => [] | some s => s ++ [0])

/-- The header bytes before FHCRC. -/
def encodePrefix (h : Header) : List UInt8 :=
  [0x1F, 0x8B, 0x08, h.flg] ++ le32Bytes h.mtime ++ [h.xfl, h.os] ++ encodeOptional h

/-- The FHCRC value of a header prefix: the low 16 bits of its CRC-32. -/
def hcrcOf (pre : List UInt8) : Nat := crc32List (pre.map (λ b => b.toNat)) % 65536

/-- **The member header**, serialised, with FHCRC when `h.hcrc`. -/
def encodeHeader (h : Header) : List UInt8 :=
  encodePrefix h ++ (if h.hcrc then le16Bytes (hcrcOf (encodePrefix h)) else [])

/-- The headers `encodeHeader` writes faithfully: MTIME fits in 32 bits, the
FEXTRA payload in XLEN, and FNAME and FCOMMENT contain no zero byte. -/
def Header.Valid (h : Header) : Prop :=
  h.mtime < 2 ^ 32 ∧ h.extra.all (fun x => decide (x.length < 65536)) ∧
    h.name.all (fun s => !s.contains 0) ∧ h.comment.all (fun s => !s.contains 0)

instance (h : Header) : Decidable h.Valid := by unfold Header.Valid; infer_instance

/-- **A gzip member** with header `h`: stored DEFLATE blocks and the CRC-32/ISIZE
trailer. -/
abbrev encodeMember (h : Header) : Encoder :=
  Framing.encode (encodeHeader h) Deflate.encoder Gzip.trailer

/-! ## Field conventions, not enforced by the decoder -/

/-- The FEXTRA subfields (RFC 1952 §2.3.1.1): `SI1`, `SI2`, `LEN` (two bytes,
little-endian), then `LEN` bytes of data, repeated to the end of the field.
`fuel` bounds the number of subfields; each takes at least four bytes. -/
def parseSubfieldsFuel : Nat → List UInt8 → Option (List (UInt8 × UInt8 × List UInt8))
  | _, [] => some []
  | fuel + 1, si1 :: si2 :: l0 :: l1 :: r =>
    let n := l0.toNat + 256 * l1.toNat
    if n ≤ r.length then
      (parseSubfieldsFuel fuel (r.drop n)).map ((si1, si2, r.take n) :: ·)
    else none
  | _, _ => none

/-- The FEXTRA payload as a list of subfields `(SI1, SI2, data)`, or `none` if
it is not a sequence of subfields. -/
def parseSubfields (x : List UInt8) : Option (List (UInt8 × UInt8 × List UInt8)) :=
  parseSubfieldsFuel x.length x

/-- FEXTRA, if present, is a sequence of subfields (RFC 1952 §2.3.1.1). The
decoder does not require this: it skips `XLEN` bytes, as §2.3.1.2 allows. -/
def Header.extraWellFormed (h : Header) : Prop :=
  h.extra.all (fun x => (parseSubfields x).isSome)

/-- An ISO 8859-1 graphic character: `0x20`–`0x7E` (printable ASCII, with the
space) or `0xA0`–`0xFF`. The C0 and C1 control ranges are excluded. -/
def isLatin1Graphic (b : UInt8) : Bool := (0x20 ≤ b && b ≤ 0x7E) || 0xA0 ≤ b

/-- FNAME and FCOMMENT read strictly. RFC 1952 §2.3.1 says the name "must consist
of ISO 8859-1 (LATIN-1) characters" and so must the comment, in which "line breaks
should be denoted by a single line feed character (10 decimal)". We read
"characters" as graphic characters of ISO 8859-1, allowing line feed in the
comment. Decoders (GNU gzip, zlib, CPython) accept any non-zero byte here, and
in practice names are often UTF-8; `parseHeader` follows them. -/
def Header.latin1Strict (h : Header) : Prop :=
  h.name.all (·.all isLatin1Graphic) ∧
    h.comment.all (·.all fun b => isLatin1Graphic b || b == 0x0A)

/-- XFL for the deflate method (RFC 1952 §2.3.1): `2` for maximum compression,
`4` for the fastest algorithm. RFC 1952 defines no other values; `0` is common in
practice (GNU gzip at its default level, and `Gzip.header`), and decoders ignore
the field. -/
def Header.xflDefined (h : Header) : Prop := h.xfl = 2 ∨ h.xfl = 4

instance (h : Header) : Decidable h.extraWellFormed := by
  unfold Header.extraWellFormed; infer_instance

instance (h : Header) : Decidable h.latin1Strict := by
  unfold Header.latin1Strict; infer_instance

instance (h : Header) : Decidable h.xflDefined := by
  unfold Header.xflDefined; infer_instance

end Silmaril.Formats.Compression.GzipHeader

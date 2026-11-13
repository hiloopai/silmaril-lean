module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Formats.Compression.Gzip.Basic

/-!
# gzip (RFC 1952)

A gzip member is a `Framing` around DEFLATE: the fixed 10-byte header (magic
`1f 8b`, `CM = 8`, reserved `FLG` bits clear) with the optional `FEXTRA`,
`FNAME`, `FCOMMENT` and `FHCRC` fields skipped (the header CRC checked), a
DEFLATE stream, and a trailer of the output's CRC-32 and its length modulo
`2^32`, both little-endian. A gzip file is one or more members
(`Decoder.members`).

* `checkHeader`, `framing`, `decoder`: the container and its member decoder;
  `member` is the same decoder written out directly;
* `trailer out`: `le32 (crc32.digest out) ++ le32Bytes out.length`;
* `encoderFixed`: one member with the compressing fixed-Huffman stream
  `Deflate.encoderFixed`;
* `header`, `encoder`: the header we emit (no optional fields, `OS = 255`),
  stored DEFLATE blocks, the trailer;
* `decompress`, `compress`: the `ByteArray` multi-member decoder and the
  one-member stored-block encoder.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Gzip

/-- The RFC 1952 member header: fixed part, then the optional fields. -/
def checkHeader (bytes : List UInt8) : Option (Unit × List UInt8) :=
  match bytes with
  | 0x1F :: 0x8B :: cm :: flg :: _mt0 :: _mt1 :: _mt2 :: _mt3 :: _xfl :: _os :: rest =>
    if cm ≠ 8 ∨ flg &&& gzipFRESERVED ≠ 0 then none
    else (gzipSkipHeaderFields flg bytes rest).map ((), ·)
  | _ => none

/-- The RFC 1952 container. -/
def framing : Framing Unit where
  header := checkHeader
  trailer _ out afterBody := gzipCheckTrailer out afterBody

/-- **One RFC 1952 member** at the front of the input. -/
abbrev decoder : Decoder := framing.wrap Deflate.decoder

/-- The same member decoder, as written in the format module. -/
abbrev member : Decoder := gzipMember

/-- The trailer after output `out`: CRC-32, then the length modulo `2^32`. -/
def trailer (out : List UInt8) : List UInt8 :=
  le32 (Checksum.crc32.digest out) ++ le32Bytes out.length

/-- The header we emit: no optional fields, `MTIME = 0`, `OS = 255`. -/
def header : List UInt8 := gzipMagic ++ [0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF]

/-- One member: header, stored DEFLATE blocks, trailer. -/
abbrev encoder : Encoder := Framing.encode header Deflate.encoder trailer

/-- One compressing member: header, a fixed-Huffman DEFLATE stream
(`Deflate.encoderFixed`), the trailer. -/
abbrev encoderFixed : Encoder := Framing.encode header Deflate.encoderFixed trailer

/-- A whole gzip file: one or more members, every trailer verified. -/
abbrev decompress : ByteArray → Option ByteArray := gzipDecompress

/-- The one-member stored-block encoder on `ByteArray`. -/
abbrev compress : ByteArray → ByteArray := gzipCompress

end Silmaril.Formats.Compression.Gzip

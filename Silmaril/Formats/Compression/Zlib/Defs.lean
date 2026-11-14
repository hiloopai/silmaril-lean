module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Formats.Compression.Checksum.Defs
public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Formats.Compression.Zlib.Windowed

/-!
# zlib (RFC 1950)

A zlib member is a `Framing` around DEFLATE: the CMF/FLG header (`CM = 8`,
`CINFO ≤ 7`, the mod-31 `FCHECK`, `FDICT = 0`), a DEFLATE stream, and the
big-endian Adler-32 of the output.

* `framing`, `decoder`: the container and its member decoder; `take` is the
  same decoder written out directly (`take_eq_decoder` in `Zlib.Thms`);
* `trailer out`: the trailer of output `out`, `be32 (adler32.digest out)`;
* `encoder`: header `78 01`, stored DEFLATE blocks, trailer; `encoderFixed`: the
  same with the compressing fixed-Huffman stream `Deflate.encoderFixed`;
* `decompress`, `compress`: the `ByteArray` whole-buffer decoder (exactly one
  member) and the stored-block encoder;
* `takeWithDictionary dictionary`: the `FDICT = 1` variant, which checks the
  dictionary's Adler-32 and seeds the DEFLATE history with it;
* profiles (`Zlib.Windowed`): `takeWindowed` (distances within the `CINFO`
  window), `takeWithDictionaryAnyWindow` (dictionaries for every `CINFO`),
  `takeWithDictionaryWindowed` (both);
* `sampleHello`: CPython's `zlib.compress(b"hello")`, a concrete member.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zlib

/-- The RFC 1950 container (no preset dictionary). -/
def framing : Framing Unit where
  header bytes := (zlibCheckHeader bytes).map ((), ·)
  trailer _ out afterBody := zlibCheckTrailer out afterBody

/-- **One RFC 1950 member** at the front of the input. -/
abbrev decoder : Decoder := framing.wrap Deflate.decoder

/-- The same member decoder, as written in the format module. -/
abbrev take : Decoder := zlibTake

/-- The trailer after output `out`: its Adler-32, big-endian. -/
def trailer (out : List UInt8) : List UInt8 := be32 (Checksum.adler32.digest out)

/-- Header `78 01`, then stored DEFLATE blocks, then the trailer. -/
abbrev encoder : Encoder := Framing.encode zlibHeader Deflate.encoder trailer

/-- One compressing member: header, a fixed-Huffman DEFLATE stream
(`Deflate.encoderFixed`), the Adler-32 trailer. -/
abbrev encoderFixed : Encoder := Framing.encode zlibHeader Deflate.encoderFixed trailer

/-- A whole buffer holding exactly one member. -/
abbrev decompress : ByteArray → Option ByteArray := zlibDecompress

/-- The stored-block encoder on `ByteArray`. -/
abbrev compress : ByteArray → ByteArray := zlibCompress

/-- A member with an offered preset dictionary (`FDICT = 1`). -/
abbrev takeWithDictionary : List UInt8 → Decoder := ZlibDictionary.takeWithDictionary

/-- `zlib.compress(b"hello")` (CPython, level 6): header `78 9c`, one
fixed-Huffman block, Adler-32 `06 2c 02 15`. -/
def sampleHello : List UInt8 :=
  [0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c, 0x02, 0x15]

/-- The ASCII bytes of `hello`. -/
def helloBytes : List UInt8 := [0x68, 0x65, 0x6c, 0x6c, 0x6f]

end Silmaril.Formats.Compression.Zlib

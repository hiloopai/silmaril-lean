module

public import Silmaril.Net.Http1.Codings.Defs
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Formats.Compression.Zlib.Thms

/-!
# Transfer codings from the compression library

`Silmaril.Net.Http1.Codings` takes the decoders of `gzip`, `deflate` and `compress` as a
parameter (`Decoders`) and proves the transfer-coding round trip from one assumption,
`Decoders.Inverts`. This module instantiates the parameter with the codecs of
`Silmaril.Formats.Compression` and discharges the assumption (`CodingLib.Thms`):

| coding | RFC 9110 §8.4.1 | codec |
| --- | --- | --- |
| `gzip` (and `x-gzip`) | an RFC 1952 file: one or more members | `Silmaril.Formats.Compression.Gzip.codec` (multi-member) |
| `deflate` | the zlib format (RFC 1950) | `Silmaril.Formats.Compression.Zlib.codec` |
| `compress` | LZW | not implemented (`none`): a recipient answers `501` |

RFC 9112 §7.2 defines the `gzip` transfer coding by RFC 9110 §8.4.1.3, which names "the
gzip file format" of RFC 1952; §2.2 of that format allows several members. So `gzip` decodes
a whole file of one or more members (`Decoder.members`, as `Gzip.decompress` and the
content-coding registry do), and trailing octets after the last member are rejected. `deflate`
reads one whole zlib member (`Decoder.whole`, no trailing octets).

**What the round trip does and does not establish.** `libDecoders_inverts` uses exactly
`Gzip.roundTrip` and `Zlib.roundTrip` (`Silmaril.Formats.Compression`), which are unconditional
(standard axioms only) and are about the library's **stored-block encoders**: decoding inverts
*those* encoders. It says nothing about decoding octets produced by other
(Huffman-compressing) encoders; the decoder's correctness on arbitrary input is the compression
library's `DeflateSpec.deflateTake_iff`, which this module does not use. For `gzip` the encoder writes one
member, and the multi-member decoder reads it back (`RoundTrip.members_single`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Formats.Compression

/-- The decoders of the library, by canonical coding name. -/
def libDecoders : Decoders := fun n =>
  if n = gzipName then some Gzip.codec.decode.members
  else if n = deflateName then some Zlib.codec.decode.whole
  else none

/-- The encoders of the library, by canonical coding name. -/
def libEncoders : Encoders := fun n =>
  if n = gzipName then some Gzip.codec.encode
  else if n = deflateName then some Zlib.codec.encode
  else none

/-- The codings the library implements, for `ServerConfig.implements`. -/
def libImplements (n : Bytes) : Bool := (libDecoders n).isSome

end Silmaril.Net.Http1

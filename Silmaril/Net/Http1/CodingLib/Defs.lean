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
| `gzip` (and `x-gzip`) | RFC 1952 member | `Silmaril.Formats.Compression.Gzip.codec` |
| `deflate` | the zlib format (RFC 1950) | `Silmaril.Formats.Compression.Zlib.codec` |
| `compress` | LZW | not implemented (`none`): a recipient answers `501` |

Each decoder reads one whole member (`Decoder.whole`, no trailing octets). The encoders write
stored blocks, so they do not compress; the decoders accept every DEFLATE block type.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Formats.Compression

/-- The decoders of the library, by canonical coding name. -/
def libDecoders : Decoders := fun n =>
  if n = gzipName then some Gzip.codec.decode.whole
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

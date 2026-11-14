module

@[expose] public section

/-!
# QPACK error codes (RFC 9204 §6)

"The following error codes are defined for HTTP/3 to indicate failures of QPACK that prevent
the stream or connection from continuing" (§6):

| Error | Code | Raised by |
| --- | --- | --- |
| `QPACK_DECOMPRESSION_FAILED` | `0x0200` | the decoder, on an encoded field section |
| `QPACK_ENCODER_STREAM_ERROR` | `0x0201` | the decoder, on an encoder instruction |
| `QPACK_DECODER_STREAM_ERROR` | `0x0202` | the encoder, on a decoder instruction |

All three are connection errors when raised by the operations of this development.
-/

namespace Silmaril.Net.Qpack

/-- A QPACK connection error (§6). -/
inductive QpackError where
  /-- `QPACK_DECOMPRESSION_FAILED` (0x0200): an encoded field section cannot be interpreted. -/
  | decompressionFailed
  /-- `QPACK_ENCODER_STREAM_ERROR` (0x0201): an encoder instruction cannot be interpreted. -/
  | encoderStreamError
  /-- `QPACK_DECODER_STREAM_ERROR` (0x0202): a decoder instruction cannot be interpreted. -/
  | decoderStreamError
  deriving DecidableEq, Repr, Inhabited

/-- The HTTP/3 error code of a QPACK error (§6, §8.3). -/
def QpackError.code : QpackError → Nat
  | .decompressionFailed => 0x0200
  | .encoderStreamError => 0x0201
  | .decoderStreamError => 0x0202

end Silmaril.Net.Qpack

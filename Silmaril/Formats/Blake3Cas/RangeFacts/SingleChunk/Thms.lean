module

public import Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.SingleChunk

public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk

open Silmaril.Crypto.Blake3

/-- The official encoder's bytes for this profile are accepted by the matching
strict decoder. Covers the empty object, zero-count windows, EOF, and all
in-bounds byte windows of a single BLAKE3 chunk. -/
theorem complete {digest original : Bytes} (profile : Profile) (request : Request) {cap : Nat}
    (named : Named concrete digest original) (small : original.length ≤ 1024) (withinCap : original.length ≤ cap)
    (bound : let window := request.window original.length; window.start + window.count ≤ original.length) :
    ∃ wire response, encode? profile request original = some wire ∧
      decode? profile cap digest request wire original = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧
      response.done.bytes = (original.drop (request.window original.length).start).take (request.window original.length).count :=
  Proofs.Formats.Blake3Cas.RangeFacts.SingleChunk.complete profile request named small withinCap bound

end Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk

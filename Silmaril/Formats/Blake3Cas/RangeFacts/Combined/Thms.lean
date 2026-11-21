module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Combined

public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Combined

open Silmaril.Crypto.Blake3

theorem fullPlan_geometry (size : Nat) : Bao.fullPlan size 1 = chunkPlan (geometry 0 size) :=
  Proofs.Formats.Blake3Cas.RangeFacts.Combined.fullPlan_geometry size

/-- The official combined encoder followed by the strict whole-object range API.
`Named` includes `original.length < 2^64`. No further alignment, chunk-count,
or final-chunk restriction applies; the verifier cap must cover the payload. -/
theorem complete {digest original : Bytes} {cap : Nat}
    (named : Named concrete digest original) (withinCap : original.length ≤ cap) :
    ∃ wire response, encode? original = some wire ∧
      decodeCombined? cap digest (.toEnd 0) wire = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧ response.done.bytes = original :=
  Proofs.Formats.Blake3Cas.RangeFacts.Combined.complete named withinCap

end Silmaril.Formats.Blake3Cas.RangeFacts.Combined

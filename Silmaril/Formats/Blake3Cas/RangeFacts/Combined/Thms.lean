module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Combined

public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Combined

open Silmaril.Crypto.Blake3

theorem fullPlan_geometry (size : Nat) : Bao.fullPlan size 1 = chunkPlan (geometry 0 size) :=
  Proofs.Formats.Blake3Cas.RangeFacts.Combined.fullPlan_geometry size

/-- The official combined encoder and strict range API agree on every in-bounds
window, including proper interior ranges and empty ranges. EOF is authenticated
because combined frames disclose the entire right edge, not because the request
finishes. `Named` includes `original.length < 2^64`. -/
theorem completeWindow {digest original : Bytes} {cap : Nat} (request : Request)
    (named : Named concrete digest original) (withinCap : original.length ≤ cap)
    (within : let window := request.window original.length; window.start + window.count ≤ original.length) :
    ∃ wire response, encode? original = some wire ∧
      decodeCombined? cap digest request wire = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧
      response.done.bytes = (original.drop (request.window original.length).start).take (request.window original.length).count :=
  Proofs.Formats.Blake3Cas.RangeFacts.Combined.completeWindow request named withinCap within

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

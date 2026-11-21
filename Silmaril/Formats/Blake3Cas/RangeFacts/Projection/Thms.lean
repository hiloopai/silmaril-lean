module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Projection.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Projection

public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Projection

open Silmaril.Crypto.Blake3 (Bytes)

theorem Contiguous.append {size base : Nat} {digest left right : Bytes} {lhs rhs : List (SpanFact size digest)}
    (first : Contiguous base lhs left) (last : Contiguous (base + left.length) rhs right) :
    Contiguous base (lhs ++ rhs) (left ++ right) :=
  Proofs.Formats.Blake3Cas.RangeFacts.Projection.append first last

/-- Any contiguous checked tape segment advances the clamped cursor and projects exactly
the intersection of the segment and request. This makes no EOF assertion. -/
theorem project {size base : Nat} {digest bytes : Bytes} {fields : List Bytes} (request : Bao.RangeRequest)
    (tape : Tape size digest fields) (contiguous : Contiguous base tape.spans bytes) :
    ∃ coverage,
      tape.project? request (cursorAt request base) = some ⟨cursorAt request (base + bytes.length), coverage⟩ ∧
      coverage.bytes = clip request base bytes :=
  Proofs.Formats.Blake3Cas.RangeFacts.Projection.project request tape contiguous

/-- If a completed body's contiguous data contains the requested interval, range projection
succeeds with exactly the requested bytes. The result remains staged at `size`. -/
theorem range {size base : Nat} {digest bytes : Bytes} {fields : List Bytes} (request : Bao.RangeRequest)
    (body : CompleteBody size digest fields) (contiguous : Contiguous base body.tape.spans bytes)
    (starts : base ≤ request.start) (ends : request.start + request.count ≤ base + bytes.length)
    (within : request.start + request.count ≤ size) :
    ∃ result, body.range? request = some result ∧
      result.coverage.bytes = (bytes.drop (request.start - base)).take request.count :=
  Proofs.Formats.Blake3Cas.RangeFacts.Projection.range request body contiguous starts ends within

end Silmaril.Formats.Blake3Cas.RangeFacts.Projection

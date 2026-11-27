module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

/-- A valid short body fragment gives the typed wait reply. Finalization
is a separate operation. -/
theorem wait_body {cursor : Cursor} {header chunk : KBytes} {offset size : Nat}
    {pending : Arrow.Framing.Incremental.Buffer size}
    (atBody : cursor.input = .body offset header size pending)
    (valid : chunk.wf = true) (short : pending.bytes.len + chunk.len < size) :
    feed cursor chunk = .ok (.wait
      { cursor with input := .body offset header size (pending.feed chunk valid).buffered }) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.wait_body atBody valid short

/-- At the declared input cutoff, the prior complete records and events agree
with immutable pulls. Finish points at the body, and the immutable error
retains the original message offset and ordinal. -/
theorem body_cutoff_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.body_cutoff_exact run

/-- Two admitted body cutoffs of the same supplied octets under the same
limits retain identical complete ranges, exact typed cause and trace. -/
theorem schedules_body_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.schedules_body_equivalent leftWf rightWf octets a b

/-- The same complete supplied octets cannot also produce a successful
finished schedule under these limits. -/
theorem body_cutoff_no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (cutoff : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.body_cutoff_no_success leftWf rightWf octets cutoff succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

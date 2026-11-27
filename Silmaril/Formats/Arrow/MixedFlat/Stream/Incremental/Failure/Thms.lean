module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

/-- The exact emitted prefix replays against immutable pulls. The native
error identifies the original EOS marker and the feed error identifies the
first tail byte eight bytes later, at the same next batch ordinal. -/
theorem tail_exact {limits : Incremental.Limits} {wire : KBytes}
    (result : TailFailure limits wire) : TailAgreement limits wire result :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.tail_exact result

/-- Two admitted schedules that encounter the tail have the same checked
schema, ordered events, absolute ranges and original typed feed error. -/
theorem schedules_tail_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : TailFailure limits left) (b : TailFailure limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.schedules_tail_equivalent
    leftWf rightWf octets a b

/-- A tail failure rules out successful finalization of the same complete
octets under the same incremental limits. -/
theorem tail_no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : TailFailure limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.tail_no_success
    leftWf rightWf octets failed succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

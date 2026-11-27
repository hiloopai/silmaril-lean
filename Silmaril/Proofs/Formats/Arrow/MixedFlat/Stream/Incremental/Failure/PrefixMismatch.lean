module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Field.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.PrefixMismatch

theorem prefix_mismatch_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run :=
  Field.field_exact run.toField

theorem schedules_mismatch_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Field.schedules_field_equivalent leftWf rightWf octets a.toField b.toField

theorem mismatch_no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Field.field_no_success leftWf rightWf octets failed.toField succeeded

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

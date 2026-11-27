module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

open Arrow.Framing.Incremental (Window)
open MixedFlat.Stream (BatchRange)

/-- Recover the complete original frame at a typed field rejection, including
the metadata, running budget checks and exact column cause. -/
theorem feed_field_wire {size packed : Nat} {cursor : Cursor} {chunk : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {ordinal offset index : Nat}
    {cause : MixedFlat.ColumnError}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (phase : cursor.phase = .records fields running)
    (failed : feed cursor chunk = .error (.batch ordinal offset (.record (.decode (.field index cause))))) :
    ordinal = running.ordinal ∧ offset = cursor.messageOffset ∧
      ∃ range, range.offset = offset ∧
        FieldFailureWire cursor.limits (.leaf size packed) fields running range index cause :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.feed_field_wire held incoming phase failed

/-- A rejected field on an admitted frame gives the same immutable record error. -/
theorem record_field_error {limits : Incremental.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {index : Nat}
    {cause : MixedFlat.ColumnError}
    (wire : FieldFailureWire limits input fields running range index cause) :
    MixedFlat.Stream.readRecord limits.mixed input fields running.rows range.offset range.metadataSize =
      .error (.decode (.field index cause)) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.record_field_error wire

/-- The immutable pull and eager suffix stop at the original indexed field error. -/
theorem field_terminal {limits : Incremental.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {running : Running} {range : BatchRange} {index : Nat}
    {cause : MixedFlat.ColumnError}
    (wire : FieldFailureWire limits input fields running range index cause) :
    let remaining := limits.mixed.observation.ipc.batches - running.ordinal
    MixedFlat.Stream.Events.readNext limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.message running.ordinal range.offset (.decode (.field index cause))) ∧
    MixedFlat.Stream.readBatches limits.mixed input fields remaining running.ordinal running.rows range.offset =
      .error (.batch running.ordinal (.decode (.field index cause))) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.field_terminal wire

/-- The complete published prefix replays on the immutable reader, followed
by the exact view prefix mismatch in the original complete frame. -/
theorem prefix_mismatch_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.prefix_mismatch_exact run

/-- Admitted schedules for the same octets and limits which reach the mismatch
have the same complete batches, ranges and terminal cause. -/
theorem schedules_mismatch_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.schedules_mismatch_equivalent leftWf rightWf octets a b

/-- The same octets and limits exclude a successful completed schedule. -/
theorem mismatch_no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.mismatch_no_success leftWf rightWf octets failed succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

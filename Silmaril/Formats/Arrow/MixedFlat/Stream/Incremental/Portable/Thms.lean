module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable

/-- The packed proof reference preserves the original native carrier octets. -/
theorem reference_octets {wire : KBytes} (wf : wire.wf = true) :
    (reference wire).toList = wire.toList :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.reference_octets wf

/-- Well-formed byte representations of the same octets use the same reference. -/
theorem reference_congr {left right : KBytes} (leftWf : left.wf = true) (rightWf : right.wf = true)
    (octets : left.toList = right.toList) : reference left = reference right :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.reference_congr leftWf rightWf octets

/-- A successful schedule yields the exact immutable eager records and pull trace. -/
theorem completed_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Completed limits wire) :
    run.endOffset = wire.len ∧
    MixedFlat.Stream.read limits.mixed (reference wire) = .ok ⟨run.fields, run.batches.map Delivered.record⟩ ∧
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) = run.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.completed_exact run

/-- Read EOS within the original carrier at the successful schedule end. -/
theorem original_eos {limits : Incremental.Limits} {wire : KBytes}
    (wf : wire.wf = true) (run : Completed limits wire) :
    ∃ offset, offset + 8 = run.endOffset ∧ readEnvelope limits.mixed.observation.ipc wire offset = .ok .eos :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.original_eos wf run

/-- Any two successful schedules for the same octets give the same absolute
record ranges, projected trace and final offset. Projection can reorder,
repeat or omit checked positions. -/
theorem schedules_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Completed limits left) (b : Completed limits right) (projection : Projection) :
    a.endOffset = b.endOffset ∧ a.ranges = b.ranges ∧ a.project projection = b.project projection :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.schedules_equivalent
    leftWf rightWf octets a b projection

/-- After the packed reference passes the ordered writer readback check, every
successful schedule recovers the exact input fields, batch observation and EOS.
The original carrier and packed reference have identical octets. -/
theorem writer_readback {limits : Incremental.Limits} {wire : KBytes}
    {fields : List MixedFlat.Field} {batches : List OrderedWriter.BatchInput}
    {shape : List MixedFlat.Field → Bool} (written : OrderedWriter.emit limits.mixed fields batches shape = .ok wire)
    (checked : checkWriterReadback limits.mixed wire fields batches = true)
    (run : Completed limits wire) :
    (reference wire).toList = wire.toList ∧
    run.fields = fields ∧
    (run.batches.map fun batch => StreamWriter.observeBatch batch.record) =
      batches.map OrderedWriter.BatchInput.observe ∧
    ∃ offset, offset + 8 = run.endOffset ∧ readEnvelope limits.mixed.observation.ipc wire offset = .ok .eos :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.writer_readback written checked run

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable

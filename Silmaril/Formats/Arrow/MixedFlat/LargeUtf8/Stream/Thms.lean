module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Thms
import Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream

theorem readRecord_sound {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {fields : List Field} {rowsBefore offset size : Nat} {batch : Batch}
    (read : readRecord limits framing input fields rowsBefore offset size = .ok batch) :
    RecordWire limits framing input fields rowsBefore offset size batch :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.readRecord_sound read

/-- Preserve the exact schema and all completed records at their original
ranges. The trace ends at exact EOS or at the checked first failure. -/
theorem read_sound {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {observed : Observed} (read : read limits framing input = .ok observed) :
    StreamWire limits framing input observed :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.read_sound read

theorem TraceWire.error_ordinal {limits : MixedFlat.Limits} {framing : Framing} {input : KBytes}
    {fields : List Field} {remaining ordinal rowsBefore offset failed failedOffset : Nat}
    {batches : List Batch} {cause : Cause}
    (wire : TraceWire limits framing input fields remaining ordinal rowsBefore offset batches
      (.error failed failedOffset cause)) :
    failed = ordinal + batches.length :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.error_ordinal wire

/-- Every assigned descriptor selects exactly its original carrier window
within the checked record body. -/
theorem original_buffer {limits : Arrow.Limits} {input body : KBytes} {range : Range}
    {fields : List MixedFlat.Field} {metadata : MixedFlat.Metadata} (inputWf : input.wf = true)
    (read : Arrow.readBody limits input range.bodyStart range.bodyLength = .ok body)
    (plan : MixedFlat.Plan fields metadata body) {group : MixedFlat.Group metadata.batch.rowCount}
    (assigned : group ∈ plan.assignment.groups) {buffer : Buffer} (member : buffer ∈ group.buffers) :
    range.bodyStart + buffer.offset + buffer.length ≤ range.next ∧ range.next ≤ input.len ∧
    (Body.sliceBuffer body buffer).len = buffer.length ∧
    (Body.sliceBuffer body buffer).toList =
      (input.toList.drop (range.bodyStart + buffer.offset)).take buffer.length :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.original_buffer inputWf read plan assigned member

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream

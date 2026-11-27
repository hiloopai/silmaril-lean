module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Wire

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch

/-- A checked RecordBatch partitions the complete original descriptor vectors,
and each region lies in the exact body of its original frame. -/
theorem Frame.wire {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : FrameWire frame :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.frame_wire frame

/-- The first batch is bound to the checked schema in the same IPC carrier. -/
theorem First.wire {limits : Limits} {input : KBytes} (first : First limits input) :
    ∃ size, first.offset = 8 + size ∧
      EnvelopeWire limits.schema.ipc input.toList 0 (.metadata size) ∧
      (input.slice 8 size).toList = (input.toList.drop 8).take size ∧
      SchemaWire limits.schema (input.slice 8 size) first.schema ∧ FrameWire first.batch :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.first_wire first

/-- A checked buffer slice is the exact absolute byte range of the IPC carrier. -/
theorem Frame.region_exact {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) {cursor : Cursor} {buffer : Buffer}
    (wire : BufferWire frame.carrier cursor buffer) :
    frame.bodyStart + buffer.offset + buffer.length ≤ frame.next ∧
      (Body.sliceBuffer frame.body buffer).len = buffer.length ∧
      (Body.sliceBuffer frame.body buffer).toList =
        (input.toList.drop (frame.bodyStart + buffer.offset)).take buffer.length :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.region_exact frame wire

/-- The child length in the List witness is the original nonnegative terminal word. -/
theorem OffsetPrefix.last_word {offsets : KBytes} {length final : Nat}
    (wire : OffsetPrefix offsets length final) :
    offsets.readLE (4 * length) 4 = some final ∧ final < 2^31 :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.offset_last_word wire

/-- Every original adjacent List offset pair is ordered and bounded by its
terminal word, including those under a null parent. -/
theorem OffsetPrefix.window {offsets : KBytes} {length final : Nat}
    (wire : OffsetPrefix offsets length final) {index : Nat} (range : index < length) :
    ∃ lo hi, offsets.readLE (4 * index) 4 = some lo ∧
      offsets.readLE (4 * (index + 1)) 4 = some hi ∧ lo ≤ hi ∧ hi ≤ final ∧ final < 2^31 :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.offset_window wire range

end Silmaril.Formats.Arrow.RecursiveSchema.Batch

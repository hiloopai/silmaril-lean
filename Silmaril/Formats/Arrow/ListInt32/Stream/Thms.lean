module

public import Silmaril.Formats.Arrow.ListInt32.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.ListInt32.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.ListInt32.Stream

/-- A slot uses the original parent bit and the ordered child interval between its signed offsets. -/
theorem readRow_wire {bitmap offsets : KBytes} {children : Array (Option Int32)}
    {index : Nat} {row : Row} (h : readRow bitmap offsets children index = .ok row) :
    RowWire bitmap offsets children index row :=
  Proofs.Formats.Arrow.ListInt32.Stream.readRow_wire h

/-- All parent and child slots retain their checked counts and original logical buffer contents. -/
theorem readRows_wire {layout : Layout} {body : KBytes} {rows : List Row}
    (h : readRows layout body = .ok rows) : RowsWire layout body rows :=
  Proofs.Formats.Arrow.ListInt32.Stream.readRows_wire h

/-- A record uses the original ordered nodes, descriptors and body, within both budgets. -/
theorem readRecord_wire {limits : Limits} {input : KBytes}
    {rowsBefore childrenBefore offset size : Nat} {batch : Batch}
    (h : readRecord limits input rowsBefore childrenBefore offset size = .ok batch) :
    RecordWire limits input rowsBefore childrenBefore offset size batch :=
  Proofs.Formats.Arrow.ListInt32.Stream.readRecord_wire h

/-- The record sequence consumes the exact carrier through modern EOS. -/
theorem readBatches_wire {limits : Limits} {input : KBytes}
    {fuel index rowsBefore childrenBefore offset : Nat} {batches : List Batch}
    (h : readBatches limits input fuel index rowsBefore childrenBefore offset = .ok batches) :
    BatchesWire limits input fuel rowsBefore childrenBefore offset batches :=
  Proofs.Formats.Arrow.ListInt32.Stream.readBatches_wire h

/-- Every observed parent in the required profile is present. -/
theorem checkParents_required {batches : List Batch} (h : checkParents false batches = .ok ()) :
    ∀ batch ∈ batches, ∀ row ∈ batch.rows, row.isSome = true :=
  Proofs.Formats.Arrow.ListInt32.Stream.checkParents_required h

/-- The checked schema selects the parent flag and the record witness reaches exact EOS. -/
theorem readFor_wire {parentNullable : Bool} {limits : Limits} {input : KBytes} {observed : Observed}
    (h : readFor parentNullable limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      ListInt32.readSchemaFor parentNullable limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits input limits.ipc.batches 0 0 (8 + size) observed.batches ∧
      checkParents parentNullable observed.batches = .ok () :=
  Proofs.Formats.Arrow.ListInt32.Stream.readFor_wire h

/-- The same checked schema and ordered frames determine the observation. -/
theorem read_wire {limits : Limits} {input : KBytes} {observed : Observed}
    (h : read limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      ListInt32.readSchema limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits input limits.ipc.batches 0 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.ListInt32.Stream.read_wire h

/-- An accepted record advances to a bounded successor through both exact sub-slices. -/
theorem record_ranges {limits : Limits} {input : KBytes}
    {rowsBefore childrenBefore offset size : Nat} {batch : Batch}
    (wf : input.wf = true) (envelope : readEnvelope limits.ipc input offset = .ok (.metadata size))
    (wire : RecordWire limits input rowsBefore childrenBefore offset size batch) :
    offset < batch.next ∧ batch.next ≤ input.len ∧
    (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size ∧
    ∃ body : KBytes, body.len = batch.bodyLength ∧
      body.toList = (input.toList.drop (offset + 8 + size)).take batch.bodyLength :=
  Proofs.Formats.Arrow.ListInt32.Stream.record_ranges wf envelope wire

/-- Every accepted record consumes fuel, including a zero-row record. -/
theorem batches_length_le {limits : Limits} {input : KBytes} {fuel rows children offset : Nat}
    {batches : List Batch} (wire : BatchesWire limits input fuel rows children offset batches) :
    batches.length ≤ fuel :=
  Proofs.Formats.Arrow.ListInt32.Stream.batches_length_le wire

end Silmaril.Formats.Arrow.ListInt32.Stream

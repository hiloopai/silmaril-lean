module

public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered.Framing

public section

namespace Silmaril.Formats.Arrow.TimestampStream.Ordered

/-- The original Schema frame retains the little-endian field sequence. -/
theorem readSchema_wire {limits : Limits} {input : KBytes} {fields : List Field} {start : Nat}
    (read : readSchema limits input = .ok (fields, start)) :
    ∃ size schema,
      readEnvelope limits input 0 = .ok (.metadata size) ∧
      SchemaReader.readMessage limits (input.slice 8 size) = .ok schema ∧ schema.endianness = .little ∧
      (schema.fields.zipIdx.mapM fun (field, i) => bindField field i) = .ok fields ∧ start = 8 + size :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.readSchema_wire read

/-- Every original column decodes to the shared record row count. -/
theorem columnsWire_aligned {limits : Limits} {rows : Nat} {body : KBytes} {fields : List Field}
    {nodes : List FieldNode} {buffers : List Buffer} {columns : List Column}
    (wire : ColumnsWire limits rows body fields nodes buffers columns) :
    (⟨rows, columns⟩ : Batch).Aligned fields :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.columnsWire_aligned wire

/-- The checked batch retains the exact original extent and consumes the nodes and buffer pairs in order. -/
theorem decodeBatch_wire {limits : Limits} {fields : List Field} {batch : RecordBatch}
    {length : Nat} {body : KBytes} {decoded : Batch}
    (read : decodeBatch limits fields batch length body = .ok decoded) :
    BatchWire limits fields batch length body decoded :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.decodeBatch_wire read

/-- The checked layout yields one aligned column per field, including a zero-width batch. -/
theorem batchWire_aligned {limits : Limits} {fields : List Field} {batch : RecordBatch}
    {length : Nat} {body : KBytes} {decoded : Batch}
    (wire : BatchWire limits fields batch length body decoded) : decoded.Aligned fields :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.batchWire_aligned wire

/-- The record span and body are those of the original input frame. -/
theorem readBatch_wire {limits : Limits} {input : KBytes} {fields : List Field}
    {offset size : Nat} {decoded : Batch} {next : Nat}
    (read : readBatch limits input fields offset size = .ok (decoded, next)) :
    ∃ batch length body,
      readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
      readBody limits input (offset + 8 + size) length = .ok body ∧
      BatchWire limits fields batch length body decoded ∧ next = offset + 8 + size + length :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.readBatch_wire read

/-- The original frame suffix ends at exact EOS. -/
theorem readBatches_iff (limits : Limits) (input : KBytes) (fields : List Field)
    (remaining index offset : Nat) (batches : List Batch) :
    readBatches limits input fields remaining index offset = .ok batches ↔
      BatchesWire limits input fields remaining offset batches :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.readBatches_iff limits input fields remaining index offset batches

/-- Successful reading retains the original Schema and exact ordered batch suffix. -/
theorem read_iff (limits : Limits) (input : KBytes) (result : Stream) :
    read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.fields, start) ∧
          BatchesWire limits input result.fields limits.batches start result.batches :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.read_iff limits input result

/-- Every batch in the checked stream has the same field count and exact per-column row count. -/
theorem batchesWire_aligned {limits : Limits} {input : KBytes} {fields : List Field}
    {remaining offset : Nat} {batches : List Batch}
    (wire : BatchesWire limits input fields remaining offset batches) : ∀ batch ∈ batches, batch.Aligned fields :=
  Proofs.Formats.Arrow.TimestampStream.Ordered.batchesWire_aligned wire

end Silmaril.Formats.Arrow.TimestampStream.Ordered

module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream

/-- The original parent validity bit controls row presence, independently of either child. -/
theorem readRow_wire {field : StructInt32.Field} {bitmap : KBytes} {left right : Array (Option Int32)}
    {index : Nat} {row : Row} (read : readRow field bitmap left right index = .ok row) :
    RowWire field bitmap left right index row :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRowFor_wire read

/-- A null parent hides both original child slots. -/
theorem readRow_absent {field : StructInt32.Field} {bitmap : KBytes} {left right : Array (Option Int32)}
    {index : Nat} (absent : Body.validAt bitmap index = some false) :
    readRow field bitmap left right index = .ok none := by
  simp [readRowFor, absent]

/-- Two null children under a valid parent still form a present row. -/
theorem readRow_present_nulls {field : StructInt32.Field} {bitmap : KBytes}
    {left right : Array (Option Int32)} {index : Nat}
    (present : Body.validAt bitmap index = some true)
    (lhs : left[index]? = some none) (rhs : right[index]? = some none)
    (leftNullable : field.left.nullable = true) (rightNullable : field.right.nullable = true) :
    readRow field bitmap left right index = .ok (some (none, none)) := by
  simp [readRowFor, present, lhs, rhs, missingRequiredFor, leftNullable, rightNullable]

/-- Ordered rows retain the parent bitmap and both original checked column observations. -/
theorem readRows_wire {field : StructInt32.Field} {layout : Layout} {body : KBytes} {rows : List Row}
    (read : readRows field layout body = .ok rows) : RowsWire field layout body rows :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRowsFor_wire (width := .int32) read

/-- The original frame supplies three equal-size nodes and five ordered buffers under the configured limits. -/
theorem readRecord_wire {limits : ObservationLimits} {field : StructInt32.Field} {input : KBytes}
    {rowsBefore offset size : Nat} {batch : Batch}
    (read : readRecord limits field input rowsBefore offset size = .ok batch) :
    RecordWire limits field input rowsBefore offset size batch :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRecordFor_wire (width := .int32) read

/-- Successful reading witnesses the positional schema and every original frame through exact EOS. -/
theorem read_wire {limits : ObservationLimits} {input : KBytes} {observed : Observed}
    (checked : Stream.read limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      StructInt32.readSchema limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits observed.field input limits.ipc.batches 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.StructInt32.Stream.readFor_wire (width := .int32) checked

/-- The wide leaf uses the exact original signed little-endian word prefix
and its independent bitmap, including physical slots under null parents. -/
theorem readWideColumn_wire {node : FieldNode} {bitmap values : KBytes} {slots : List (Option Int64)}
    (read : readWideColumn node bitmap values = .ok slots) : WideColumnWire node bitmap values slots :=
  Proofs.Formats.Arrow.StructInt32.Stream.readWideColumn_wire read

/-- The selected leaf decoder is tied to the original depth-first child buffers. -/
theorem readRowsFor_wire {width : StructInt32.RightWidth} {field : StructInt32.Field}
    {layout : Layout} {body : KBytes} {rows : List (RowFor width.Value)}
    (read : readRowsFor width field layout body = .ok rows) : RowsWireFor width field layout body rows :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRowsFor_wire read

/-- Both explicit profiles use the original positional schema and the same
record framing and exact EOS. -/
theorem readFor_wire {width : StructInt32.RightWidth} {limits : ObservationLimits} {input : KBytes}
    {observed : Observed width.Value} (checked : readFor width limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      StructInt32.readSchemaFor width limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWireFor width limits observed.field input limits.ipc.batches 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.StructInt32.Stream.readFor_wire checked

/-- The original schema reader selects the same strict signed Int32 width in both positions. -/
theorem readSchemaFor_int32 (limits : Arrow.Limits) (input : KBytes) :
    StructInt32.readSchemaFor .int32 limits input = StructInt32.readSchema limits input := rfl

/-- Profile selection at Int32 is exactly the strict original reader. -/
theorem readFor_int32 (limits : ObservationLimits) (input : KBytes) :
    readFor .int32 limits input = Stream.read limits input := rfl

end Silmaril.Formats.Arrow.StructInt32.Stream

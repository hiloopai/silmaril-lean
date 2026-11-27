module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Correctness

public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream

/-- The original parent validity bit controls row presence, independently of either child. -/
theorem readRow_wire {field : StructInt32.Field} {bitmap : KBytes} {left right : Array (Option Int32)}
    {index : Nat} {row : Row} (read : readRow field bitmap left right index = .ok row) :
    RowWire field bitmap left right index row :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRow_wire read

/-- A null parent hides both original child slots. -/
theorem readRow_absent {field : StructInt32.Field} {bitmap : KBytes} {left right : Array (Option Int32)}
    {index : Nat} (absent : Body.validAt bitmap index = some false) :
    readRow field bitmap left right index = .ok none := by
  simp [readRow, absent]

/-- Two null children under a valid parent still form a present row. -/
theorem readRow_present_nulls {field : StructInt32.Field} {bitmap : KBytes}
    {left right : Array (Option Int32)} {index : Nat}
    (present : Body.validAt bitmap index = some true)
    (lhs : left[index]? = some none) (rhs : right[index]? = some none)
    (leftNullable : field.left.nullable = true) (rightNullable : field.right.nullable = true) :
    readRow field bitmap left right index = .ok (some (none, none)) := by
  simp [readRow, present, lhs, rhs, missingRequired, leftNullable, rightNullable]

/-- Ordered rows retain the parent bitmap and both original checked column observations. -/
theorem readRows_wire {field : StructInt32.Field} {layout : Layout} {body : KBytes} {rows : List Row}
    (read : readRows field layout body = .ok rows) : RowsWire field layout body rows :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRows_wire read

/-- The original frame supplies three equal-size nodes and five ordered buffers under the configured limits. -/
theorem readRecord_wire {limits : ObservationLimits} {field : StructInt32.Field} {input : KBytes}
    {rowsBefore offset size : Nat} {batch : Batch}
    (read : readRecord limits field input rowsBefore offset size = .ok batch) :
    RecordWire limits field input rowsBefore offset size batch :=
  Proofs.Formats.Arrow.StructInt32.Stream.readRecord_wire read

/-- Successful reading witnesses the positional schema and every original frame through exact EOS. -/
theorem read_wire {limits : ObservationLimits} {input : KBytes} {observed : Observed}
    (checked : Stream.read limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      StructInt32.readSchema limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits observed.field input limits.ipc.batches 0 (8 + size) observed.batches :=
  Proofs.Formats.Arrow.StructInt32.Stream.read_wire checked

end Silmaril.Formats.Arrow.StructInt32.Stream

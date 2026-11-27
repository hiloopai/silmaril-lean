module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Projection
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Typing
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Totality
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.Wire

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows

/-- The indexed reader agrees with the independent logical slot relation. -/
theorem readCell_wire {depth slot : Nat} {column : Semantics.Column} {cell : Cell}
    (read : readCell depth (IndexedColumn.ofColumn column) slot = .ok cell) :
    CellWire column slot cell :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.readCell_wire read

theorem project_wire {depth : Nat} {physical : Semantics.Observation}
    {logical : Observation} (read : project depth physical = .ok logical) :
    ProjectionWire physical logical :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.project_wire read

/-- Each logical row has its original row index and ordered physical columns. -/
theorem ProjectionWire.row_at {physical : Semantics.Observation}
    {logical : Observation} (wire : ProjectionWire physical logical) {index : Nat} {row : Row}
    (selected : logical.rows[index]? = some row) :
    CellsWire (physical.columns.map fun column => (column, index)) row :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.row_at wire selected

/-- An absent parent returns immediately, for any physical children. -/
theorem readCell_null {depth slot : Nat} {presence : Semantics.Presence}
    {payload : IndexedPayload} {children : List IndexedColumn}
    (reached : Reached presence slot) (absent : presence.valid[slot]? = some false) :
    readCell (depth + 1) (.node presence payload children) slot = .ok none := by
  simp [readCell, Reached] at reached ⊢
  simp [reached, absent, pure, Except.pure]

/-- A selected signed value is the interpretation of its original word,
at the exact byte position within the checked body region. -/
theorem signedWord_at {α : Type} {width count slot : Nat} {interpret : List UInt8 → α}
    {bytes : KBytes} {words : List α} {value : α}
    (wire : Semantics.SignedWords width count interpret bytes words)
    (selected : words[slot]? = some value) :
    value = interpret ((bytes.toList.drop (width * slot)).take width) :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.signedWord_at wire selected

/-- The bit used by projection is the original logical validity bit. -/
theorem validity_at {body : KBytes} {node : FieldNode} {buffer : Buffer}
    {nullable valid : Bool} {visible : Array Bool} {presence : Semantics.Presence} {slot : Nat}
    (wire : Semantics.PresenceWire body node buffer nullable visible presence)
    (selected : presence.valid[slot]? = some valid) :
    Body.validAt (Body.sliceBuffer body buffer) slot = some valid :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.validity_at wire selected

theorem RowFits.length {fields : List Field} {row : Row} (fits : RowFits fields row) :
    row.length = fields.length :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.row_length fits

/-- Checked row typing applies to each original positional cell. -/
theorem RowFits.cell_at {fields : List Field} {row : Row} (fits : RowFits fields row)
    {index : Nat} (fieldBound : index < fields.length) (cellBound : index < row.length) :
    CellFits fields[index] row[index] :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.row_cell_at fits fieldBound cellBound

/-- Successful native projection is aligned to the original schema and
checked physical bits, signed words and List offset windows. -/
theorem decode_wire {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {logical : Observation}
    (read : decode frame = .ok logical) : ObservationWire frame logical :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.decode_wire read

theorem readFirst_wire {limits : Batch.Limits} {input : KBytes} {first : First limits input}
    {logical : Observation} (read : readFirst limits input = .ok (first, logical)) :
    ObservationWire first.batch logical :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.readFirst_wire read

/-- A checked physical batch always projects. Its witness supplies every
reachable slot and bounds every visible List window. -/
theorem project_total {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    {frame : Frame limits schema input offset} {physical : Semantics.Observation}
    (wire : Semantics.ObservationWire frame physical) :
    ∃ logical, project limits.schema.depth physical = .ok logical :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows.project_total wire

theorem decode_source_error {limits : Batch.Limits} {schema : Schema} {input : KBytes}
    {offset : Nat} {frame : Frame limits schema input offset} {cause : Semantics.Error}
    (error : Semantics.decode frame = .error cause) :
    decode frame = .error (.source cause) := by
  simp [decode, error, Except.mapError, bind, Except.bind]

theorem readFirst_source_error {limits : Batch.Limits} {input : KBytes} {cause : Semantics.Error}
    (error : Semantics.readFirst limits input = .error cause) :
    readFirst limits input = .error (.source cause) := by
  simp [readFirst, error, Except.mapError, bind, Except.bind]

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows

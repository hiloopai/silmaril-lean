module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Defs
public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Thms

/-! Positional typed Arrow Events for the checked recursive V5 stream. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

@[expose] public section

open Silmaril.Relational

abbrev Value (field : Field) := {value : Batch.Rows.Value // Batch.Rows.CellFits field (some value)}
abbrev Signature := Scan.Schema (Option String) Field
abbrev EventStream := Arrow.Events.EventStream (Option String) Value Stream.Error
abbrev BatchEvent (signature : Signature) := Arrow.Events.Batch signature Value
abbrev Trace (signature : Signature) := Arrow.Events.Trace signature Value Stream.Error

def fieldName : Field → Option String
  | .node name _ _ _ => name

/-- Each original declaration occupies its own position, including absent,
empty and repeated names. The full recursive declaration is the type index. -/
def signature (fields : List Field) : Signature :=
  let fields := fields.toArray
  ⟨fields.size, fun i => let field := fields[i]; (fieldName field, field)⟩

def declarations (source : Signature) : List (Option String × Field) :=
  List.ofFn source.kind

def cell (field : Field) : (raw : Batch.Rows.Cell) →
    Batch.Rows.CellFits field raw → Option (Value field)
  | none, _ => none
  | some present, checked => some ⟨present, checked⟩

def ofRow (fields : List Field) (row : Batch.Rows.Row) (fits : Batch.Rows.RowFits fields row) :
    Scan.Row (signature fields) Value :=
  let cells := row.toArray
  fun i =>
    have fieldBound : i.val < fields.length := by simpa [signature] using i.isLt
    have bound : i.val < row.length := by rwa [fits.length]
    let raw := cells[i.val]'(by simpa [cells] using bound)
    cell ((signature fields).kind i).2 raw (by
      simpa [signature, raw, cells] using fits.cell_at fieldBound bound)

def eraseRow {source : Signature} (row : Scan.Row source Value) : Batch.Rows.Row :=
  List.ofFn fun i => (row i).map Subtype.val

def rowsOfBatch (fields : List Field) (batch : Batch.Rows.Observation)
    (fits : ∀ row ∈ batch.rows, Batch.Rows.RowFits fields row) :
    Scan.Table (signature fields) Value :=
  batch.rows.attach.map fun row => ofRow fields row.val (fits _ row.property)

/-- Use the shared transposition, which preserves the row count at width zero. -/
def ofBatch (fields : List Field) (batch : Batch.Rows.Observation)
    (fits : ∀ row ∈ batch.rows, Batch.Rows.RowFits fields row) : BatchEvent (signature fields) :=
  AlignedColumns.ofRows (rowsOfBatch fields batch fits)

def eraseBatch {source : Signature} (event : BatchEvent source) : Batch.Rows.Observation :=
  ⟨event.rowCount, event.toRows.map eraseRow⟩

def terminal : Stream.End → Arrow.Events.Termination Stream.Error
  | .eos .. => .eos
  | .failed ordinal offset cause => .readError (.failed ordinal offset cause)

def ofTrace {limits : Batch.Limits} {input : KBytes} (trace : Stream.Trace)
    (wire : Stream.TraceWire limits input trace) : Trace (signature trace.schema.fields) :=
  ⟨trace.batches.attach.map (fun record =>
    ofBatch trace.schema.fields record.val.observed (by
      exact (wire.chain.record_of_mem record.property).rows.2)),
    terminal trace.terminal⟩

/-- Open and decode once. The original schema error stays outside the
event trace, and only the reached terminal failure becomes a read error. -/
def read (limits : Batch.Limits) (input : KBytes) : EventStream :=
  match original : Stream.readTrace limits input with
  | .error cause => .error (.schema cause)
  | .ok trace =>
    .ok ⟨signature trace.schema.fields, ofTrace (limits := limits) (input := input) trace (by exact RecursiveSchema.Stream.readTrace_wire original)⟩

/-- Logical positional projection of validated recursive events, with
the original error type and terminal outcome. -/
def projectTrace {source : Signature} {Failure : Type} (projection : Scan.Projection source)
    (trace : Arrow.Events.Trace source Value Failure) :
    Arrow.Events.Trace projection.schema Value Failure :=
  ⟨trace.batches.map projection.projectColumns, trace.termination⟩

def project {Failure : Type} (stream : Arrow.Events.EventStream (Option String) Value Failure)
    (projection : (source : Signature) → Scan.Projection source) :
    Arrow.Events.EventStream (Option String) Value Failure :=
  stream.map fun ⟨source, trace⟩ => ⟨(projection source).schema, projectTrace (projection source) trace⟩

def readProjected (limits : Batch.Limits) (input : KBytes)
    (projection : (source : Signature) → Scan.Projection source) : EventStream :=
  project (read limits input) projection

/-- The shared event result preserves every original schema position,
complete logical batch and reached terminal outcome. -/
structure StreamWire (limits : Batch.Limits) (input : KBytes) (source : Signature)
    (events : Trace source) : Prop where
  trace : ∃ original,
    Stream.readTrace limits input = .ok original ∧
    Stream.TraceWire limits input original ∧
    declarations source = original.schema.fields.map (fun field => (fieldName field, field)) ∧
    events.batches.map eraseBatch = original.batches.map Stream.Completed.observed ∧
    events.termination = terminal original.terminal

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

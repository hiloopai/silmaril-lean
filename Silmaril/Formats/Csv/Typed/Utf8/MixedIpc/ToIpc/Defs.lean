module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs

/-! Checked typed UTF-8 CSV to a single native mixed IPC record. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

inductive PrepareError where
  | unsupportedField (column : Nat) (field : Arrow.MixedFlat.Field)
  | cellKind (column : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : MixedIpc.Error)
  | prepare (cause : PrepareError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

def prepareValues {α : Type} (column : Nat) (extract : Cell → Option α)
    (slots : List (Option Cell)) : Except PrepareError (List (Option α)) :=
  slots.mapM fun
    | none => .ok none
    | some cell =>
      match extract cell with
      | some value => .ok (some value)
      | none => .error (.cellKind column)

def prepareColumn (column : Nat) (field : Arrow.MixedFlat.Field) (slots : List (Option Cell)) :
    Except PrepareError Arrow.MixedFlat.OrderedWriter.Column :=
  match field.kind with
  | .primitive .int32 =>
    (prepareValues column (fun
      | .primitive (.int32 n) => some n
      | _ => none) slots).map (.int32 field.name field.nullable)
  | .primitive .utf8 =>
    (prepareValues column (fun
      | .primitive (.utf8 t) => some t
      | _ => none) slots).map (.utf8 field.name field.nullable)
  | .view .utf8 =>
    (prepareValues column (fun
      | .utf8View t => some t
      | _ => none) slots).map (.utf8View field.name field.nullable)
  | _ => .error (.unsupportedField column field)

def fields (schema : Rows.Schema) : List Arrow.MixedFlat.Field :=
  List.ofFn fun i => (schema.kind i).1

/-- Transpose the ordered Scan rows into one RecordBatch input. The
explicit row count is retained at width zero and for an empty table. -/
def prepare (table : Rows.Table) : Except PrepareError Arrow.MixedFlat.OrderedWriter.BatchInput := do
  let columns := AlignedColumns.ofRows table.rows
  let compiled ← (List.finRange table.schema.width).mapM fun i =>
    prepareColumn i.val (table.schema.kind i).1 (columns.values i)
  return ⟨columns.rowCount, compiled⟩

/-- Finish checked typed CSV import before the writer runs. Every success
emits one RecordBatch, including for a header-only CSV, and modern EOS. -/
def convert (csv : MixedIpc.Limits) (ipc : Arrow.MixedFlat.Limits) (schema : Rows.Schema)
    (input : Csv.Bytes) : Except Error KBytes := do
  let table ← (MixedIpc.decode csv schema input).mapError Error.source
  let batch ← (prepare table).mapError Error.prepare
  (Arrow.MixedFlat.OrderedWriter.emitWith ipc (fields table.schema) [batch]
    (fun signature => signature.all MixedIpc.supported)).mapError Error.writer

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc

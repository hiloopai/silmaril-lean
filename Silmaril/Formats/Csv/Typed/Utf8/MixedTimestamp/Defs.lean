module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs
public import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Defs

/-! Ordered, explicitly declared INT32, UTF8 and exact TIMESTAMP ticks in typed UTF-8 CSV. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp

open Silmaril.Relational
open Arrow.MixedFlat.Timestamp (Stream Batch Column)
open Silmaril.Numeric.Timestamp (Ticks)

abbrev Field := Arrow.MixedFlat.Timestamp.Field
abbrev Limits := MixedIpc.Limits

def Cell (field : Field) : Type :=
  match field.kind with
  | .int32 => Int32
  | .utf8 => String
  | .timestamp metadata => Ticks metadata.kind metadata.unit

abbrev Schema := Typed.Schema Field

abbrev schemaOf (fields : List Field) : Schema :=
  ⟨fields.length, fun i => (fields.get i |>.name.toByteArray.data.toList, fields.get i)⟩

def codecs (field : Field) : CellCodec (Cell field) :=
  match field with
  | ⟨_, _, .int32⟩ => Codecs.int32
  | ⟨_, _, .utf8⟩ => Utf8.string
  | ⟨_, nullable, .timestamp metadata⟩ =>
    Arrow.TimestampStream.ToCsv.codecs ⟨metadata.unit, metadata.timezone, nullable⟩

inductive Error where
  | byteLimit (maximum actual : Nat)
  | rowLimit (maximum : Nat)
  | timezone (column : Nat) (actual : Option String)
  | csv (cause : Typed.Error)
  | row (index : Nat) (cause : Typed.Error)
  | requiredNull (row column : Nat)
  deriving DecidableEq, Repr

def checkSchema (schema : Schema) : Except Error Unit :=
  (List.finRange schema.width).forM fun i =>
    match (schema.kind i).2.kind with
    | .timestamp metadata =>
      if Arrow.TimestampStream.Ordered.supportedTimezone metadata.timezone then .ok ()
      else .error (.timezone i.val metadata.timezone)
    | _ => .ok ()

def checkRow (schema : Schema) (index : Nat) (row : Scan.Row schema Cell) : Except Error Unit :=
  match (List.finRange schema.width).find? (fun i => !(schema.kind i).2.nullable && (row i).isNone) with
  | none => .ok ()
  | some i => .error (.requiredNull index i.val)

def checkRows (schema : Schema) : Nat → Table schema Cell → Except Error Unit
  | _, [] => .ok ()
  | index, row :: rest => do
    checkRow schema index row
    checkRows schema (index + 1) rest

def encode (limits : Limits) (schema : Schema) (rows : Table schema Cell) : Except Error Csv.Bytes := do
  checkSchema schema
  if rows.length > limits.maxRows then throw (.rowLimit limits.maxRows)
  checkRows schema 0 rows
  let wire ← (Utf8.encode schema codecs rows).mapError .csv
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  return wire

/-- Use the shared bounded lexical row parser and typed cell decoder. Finish
each row's requiredness check before advancing to the next original record. -/
def readBody (schema : Schema) (maximum : Nat) : Nat → Nat → Csv.Bytes → Except Error (Table schema Cell)
  | _, _, [] => .ok []
  | 0, _, _ :: _ => .error (.rowLimit maximum)
  | fuel + 1, index, b :: bs => do
    let some (raw, rest) := Bounded.Internal.readRow (b :: bs) | throw (.row index .malformedWire)
    let row ← (Typed.Internal.importRow schema codecs raw).mapError (.row index)
    checkRow schema index row
    (readBody schema maximum fuel (index + 1) rest).map (row :: ·)

def decode (limits : Limits) (schema : Schema) (wire : Csv.Bytes) : Except Error (Table schema Cell) := do
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  checkSchema schema
  match wire with
  | [] => .error (.csv .missingHeader)
  | b :: bs =>
    let some (raw, rest) := Bounded.Internal.readRow (b :: bs) | .error (.csv .malformedWire)
    if raw = Typed.header schema then readBody schema limits.maxRows limits.maxRows 0 rest
    else .error (.csv .headerMismatch)

inductive ShapeError where
  | width (batch expected actual : Nat)
  | columnType (batch column : Nat)
  | rowCount (batch column expected actual : Nat)
  deriving DecidableEq, Repr

def columnCells : (field : Field) → Column → Option (List (Option (Cell field)))
  | ⟨_, _, .int32⟩, .int32 values => some values
  | ⟨_, _, .utf8⟩, .utf8 values => some values
  | ⟨_, _, .timestamp _⟩, .timestamp counts => some (counts.map (Option.map fun ticks => ⟨ticks⟩))
  | _, _ => none

def columnAt (fields : List Field) (batch : Batch) (index : Nat) (same : batch.columns.length = fields.length)
    (i : Fin fields.length) :
    Except ShapeError { values : List (Option (Cell (fields.get i))) // values.length = batch.rowCount } := do
  let column := batch.columns.get (i.cast same.symm)
  let some values := columnCells (fields.get i) column | throw (.columnType index i.val)
  if sized : values.length = batch.rowCount then
    return ⟨values, sized⟩
  else throw (.rowCount index i.val batch.rowCount values.length)

/-- Transpose only an aligned batch. Its explicit row count survives width zero. -/
def batchRows (fields : List Field) (batch : Batch) (index : Nat) :
    Except ShapeError (Table (schemaOf fields) Cell) :=
  if same : batch.columns.length = fields.length then do
    let columns ← Typed.Internal.collect (columnAt fields batch index same)
    let aligned : Scan.Columns (schemaOf fields) Cell :=
      ⟨batch.rowCount, fun i => (columns i).val, fun i => (columns i).property⟩
    return aligned.toRows
  else .error (.width index fields.length batch.columns.length)

def flatten (fields : List Field) (batches : List Batch) :
    Except ShapeError (Table (schemaOf fields) Cell) :=
  (batches.zipIdx.mapM fun (batch, index) => batchRows fields batch index).map List.flatten

def packColumn : (field : Field) → List (Option (Cell field)) → Column
  | ⟨_, _, .int32⟩, values => .int32 values
  | ⟨_, _, .utf8⟩, values => .utf8 values
  | ⟨_, _, .timestamp _⟩, values => .timestamp (values.map (Option.map (·.ticks)))

/-- CSV supplies logical rows. Re-emission uses exactly one new batch. -/
def streamOfRows (fields : List Field) (rows : Table (schemaOf fields) Cell) : Stream :=
  let aligned : Scan.Columns (schemaOf fields) Cell := AlignedColumns.ofRows rows
  ⟨fields, [⟨rows.length, List.ofFn fun i => packColumn (fields.get i) (aligned.values i)⟩]⟩

/-- Exact flattened row equality under an identical ordered field declaration. -/
def RowEquivalent (left right : Stream) : Prop :=
  ∃ same : left.fields = right.fields,
    ∃ rows : Table (schemaOf left.fields) Cell,
      flatten left.fields left.batches = .ok rows ∧
      flatten right.fields right.batches = .ok (same ▸ rows)

structure Output where
  fields : List Field
  wire : Csv.Bytes

inductive ExportError where
  | source (cause : Arrow.MixedFlat.Timestamp.Error)
  | shape (cause : ShapeError)
  | csv (cause : Error)
  deriving DecidableEq, Repr

inductive ImportError where
  | csv (cause : Error)
  | writer (cause : Arrow.MixedFlat.Timestamp.Writer.Error)
  deriving DecidableEq, Repr

def fromStream (limits : Limits) (stream : Stream) : Except ExportError Output := do
  if (stream.batches.map Batch.rowCount).sum > limits.maxRows then throw (.csv (.rowLimit limits.maxRows))
  let rows ← (flatten stream.fields stream.batches).mapError .shape
  let wire ← (encode limits (schemaOf stream.fields) rows).mapError .csv
  return ⟨stream.fields, wire⟩

def fromIpc (ipc : Arrow.ObservationLimits) (csv : Limits) (input : KBytes) : Except ExportError Output := do
  let stream ← (Arrow.MixedFlat.Timestamp.read ipc input).mapError .source
  fromStream csv stream

def toIpc (csv : Limits) (ipc : Arrow.ObservationLimits) (fields : List Field) (wire : Csv.Bytes) :
    Except ImportError KBytes := do
  let rows ← (decode csv (schemaOf fields) wire).mapError .csv
  (Arrow.MixedFlat.Timestamp.Writer.emit ipc (streamOfRows fields rows)).mapError .writer

namespace NamedTable

open Silmaril.Formats.Relational.NamedTable (Packed importCollected schemaMatches)

abbrev Database (Name : Type*) := Packed Name Csv.Field Cell

inductive ExportError where
  | missingName
  | schemaMismatch
  | csv (cause : Error)
  deriving DecidableEq, Repr

def importCsv {Name : Type*} [DecidableEq Name] (db : Database Name) (name : Name)
    (expected declared : List Field) (limits : Limits) (wire : Csv.Bytes) :
    Except (Relational.NamedTable.ImportError Error) (Database Name) :=
  importCollected db name (schemaOf expected)
    ((decode limits (schemaOf declared) wire).map fun rows => ⟨⟨schemaOf declared, rows⟩, .eos⟩)

def exportCsv {Name : Type*} (db : Database Name) (name : Name)
    (expected : List Field) (limits : Limits) : Except ExportError Output :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some table =>
    if schemaMatches (schemaOf expected) table.schema then
      ((encode limits table.schema table.rows).mapError .csv).map (fun wire => ⟨expected, wire⟩)
    else .error .schemaMismatch

end NamedTable

end Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp

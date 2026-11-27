module

public import Silmaril.Formats.Csv.Typed.Codecs.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs
public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs

/-! Checked native mixed IPC through ordered Scan rows to typed UTF-8 CSV. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

structure Limits where
  maxBytes : Nat := 128 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

inductive Error where
  | unsupportedField (column : Nat) (field : Arrow.MixedFlat.Field)
  | requiredNull (row column : Nat)
  | rowLimit (maximum : Nat)
  | byteLimit (maximum actual : Nat)
  | csv (cause : Typed.Error)
  deriving DecidableEq, Repr

inductive ScanError where
  | ipc (cause : Arrow.MixedFlat.Stream.Events.Error)
  | closed
  | alignment
  deriving DecidableEq, Repr

inductive ConvertError where
  | input (cause : ScanError)
  | output (cause : Error)
  deriving DecidableEq, Repr

/-- Preserve the ordered Arrow field descriptors alongside the UTF-8 wire.
Positive-width data cells use `N` for null and `T` followed by present text. -/
structure Output where
  schema : Rows.Schema
  wire : Csv.Bytes

def supported (field : Arrow.MixedFlat.Field) : Bool :=
  match field.kind with
  | .primitive .int32 | .primitive .utf8 | .view .utf8 => true
  | _ => false

/-- Names become UTF-8 CSV header fields. Each codec is selected by the full
descriptor at that position, including repeated names. -/
def csvSchema (schema : Rows.Schema) : Typed.Schema Arrow.MixedFlat.Field :=
  ⟨schema.width, fun i => ((schema.kind i).1.name.toByteArray.data.toList, (schema.kind i).1)⟩

def codecs (field : Arrow.MixedFlat.Field) : CellCodec Cell where
  print value :=
    match field.kind, value with
    | .primitive .int32, .primitive (.int32 n) => Codecs.int32.print n
    | .primitive .utf8, .primitive (.utf8 text) | .view .utf8, .utf8View text => Utf8.string.print text
    | _, _ => none
  parse text :=
    match field.kind with
    | .primitive .int32 => (Codecs.int32.parse text).map (Cell.primitive ∘ Arrow.Value.int32)
    | .primitive .utf8 => (Utf8.string.parse text).map (Cell.primitive ∘ Arrow.Value.utf8)
    | .view .utf8 => (Utf8.string.parse text).map Cell.utf8View
    | _ => none

def checkSchema (schema : Rows.Schema) : Except Error Unit :=
  match (List.finRange schema.width).find? (fun i => !supported (schema.kind i).1) with
  | some i => .error (.unsupportedField i.val (schema.kind i).1)
  | none => .ok ()

def checkRequired (schema : Rows.Schema) (rows : Scan.Table schema (fun _ => Cell)) :
    Except Error Unit :=
  match rows.zipIdx.findSome? (fun (row, index) =>
      ((List.finRange schema.width).find? (fun i => !(schema.kind i).1.nullable && (row i).isNone)).map
        (fun i => (index, i.val))) with
  | some (row, column) => .error (.requiredNull row column)
  | none => .ok ()

/-- Check the declared profile, row bound, and required cells before encoding.
The output byte bound is checked after encoding. -/
def encode (limits : Limits) (table : Rows.Table) : Except Error Csv.Bytes := do
  checkSchema table.schema
  if table.rows.length > limits.maxRows then throw (.rowLimit limits.maxRows)
  checkRequired table.schema table.rows
  let wire ← (Utf8.encode (csvSchema table.schema) codecs table.rows).mapError Error.csv
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  return wire

/-- Check the byte bound and exact declared schema before complete bounded
typed UTF-8 decoding. Retain required/nullable flags for the returned rows. -/
def decode (limits : Limits) (schema : Rows.Schema) (wire : Csv.Bytes) : Except Error Rows.Table := do
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  checkSchema schema
  let rows ← (Bounded.decode limits.maxRows (csvSchema schema) codecs wire).mapError fun
    | .csv cause => Error.csv cause
    | .rowLimit => Error.rowLimit limits.maxRows
  checkRequired schema rows
  return ⟨schema, rows⟩

/-- Reuse the exact native pull trace and Scan materializer. Any indexed
native failure retains its cause and produces no Scan table or CSV. -/
def readScan (limits : Arrow.MixedFlat.Limits) (wire : KBytes) : Except ScanError Rows.Table :=
  let events := Arrow.MixedFlat.Stream.Events.readAll limits wire
  match (complete events).bind Rows.toTable with
  | some table => .ok table
  | none =>
    match events with
    | .error cause => .error (.ipc cause)
    | .ok opened =>
      match opened.2.termination with
      | .readError cause | .closeError cause => .error (.ipc cause)
      | .closed => .error .closed
      | .eos => .error .alignment

def convert (ipc : Arrow.MixedFlat.Limits) (csv : Limits) (input : KBytes) : Except ConvertError Output := do
  let table ← (readScan ipc input).mapError ConvertError.input
  let wire ← (encode csv table).mapError ConvertError.output
  return ⟨table.schema, wire⟩

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc

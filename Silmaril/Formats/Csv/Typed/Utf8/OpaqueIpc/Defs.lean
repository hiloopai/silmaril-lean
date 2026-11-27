module

public import Silmaril.Formats.Csv.Typed.Codecs.Hex.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs
public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs

/-! Checked typed CSV interchange for one BinaryView or plain Binary IPC field. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

inductive Layout where
  | binaryView
  | binary
  deriving DecidableEq, Repr

structure Descriptor where
  name : String
  nullable : Bool
  layout : Layout
  deriving DecidableEq, Repr

abbrev Slots := List (Option (List UInt8))

structure Observation where
  field : Descriptor
  batches : List Slots
  deriving DecidableEq, Repr

structure IpcLimits where
  ipc : Arrow.Limits := {}
  view : Arrow.BinaryView.Column.Limits := {}

inductive ReadError where
  | view (cause : Arrow.BinaryView.Stream.Error)
  | binary (cause : Arrow.Binary.Stream.Error)
  | unsupportedView (name : String) (nullable : Bool)
  deriving DecidableEq, Repr

inductive WriteError where
  | view (cause : Arrow.BinaryView.StreamWriter.Error)
  | binary (cause : Arrow.Binary.StreamWriter.Error)
  deriving DecidableEq, Repr

/-- Read the selected modern IPC V5 profile through exact EOS. Both layouts
observe raw octets and keep the original record boundaries. -/
def readIpc (limits : IpcLimits) (layout : Layout) (input : KBytes) :
    Except ReadError Observation := do
  match layout with
  | .binaryView =>
    let source ← (Arrow.BinaryView.Stream.read limits.ipc limits.view input).mapError .view
    match source with
    | ⟨⟨name, nullable, .binary⟩, batches⟩ =>
      return ⟨⟨name, nullable, .binaryView⟩, batches.map (Arrow.BinaryView.StreamWriter.observe .binary)⟩
    | ⟨⟨name, nullable, .utf8⟩, _⟩ => throw (.unsupportedView name nullable)
  | .binary =>
    let source ← (Arrow.Binary.Stream.read limits.ipc .modern input).mapError .binary
    return ⟨⟨source.field.name, source.field.nullable, .binary⟩,
      source.batches.map (Arrow.Binary.StreamWriter.observe ∘ Arrow.Binary.Stream.Batch.values)⟩

def emitIpc (limits : IpcLimits) (field : Descriptor) (values : Slots) : Except WriteError KBytes :=
  let batch := values.map (Option.map (fun bytes => Arrow.Writer.emitWords 1 (bytes.map UInt8.toNat)))
  match field.layout with
  | .binaryView =>
    (Arrow.BinaryView.StreamWriter.emit limits.ipc limits.view ⟨field.name, field.nullable, .binary⟩
      [batch]).mapError .view
  | .binary =>
    (Arrow.Binary.StreamWriter.emit limits.ipc ⟨field.name, field.nullable⟩ [batch]).mapError .binary

structure CsvLimits where
  maxBytes : Nat := 128 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

inductive CsvError where
  | requiredNull (row : Nat)
  | rowLimit (maximum : Nat)
  | byteLimit (maximum actual : Nat)
  | csv (cause : Typed.Error)
  deriving DecidableEq, Repr

structure Output where
  field : Descriptor
  wire : Csv.Bytes
  deriving DecidableEq, Repr

def schema (field : Descriptor) : Typed.Schema Unit :=
  ⟨1, fun _ => (field.name.toUTF8.data.toList, ())⟩

def codecs (_ : Unit) : CellCodec (List UInt8) := Codecs.Hex.codec

def readRows {field : Descriptor} (rows : Typed.Table (schema field) (fun _ => List UInt8)) : Slots :=
  rows.map fun row => row ⟨0, Nat.zero_lt_succ 0⟩

def checkRequired (field : Descriptor) (values : Slots) : Except CsvError Unit :=
  if field.nullable then .ok () else
    match values.findIdx? Option.isNone with
    | some row => .error (.requiredNull row)
    | none => .ok ()

def encode (limits : CsvLimits) (field : Descriptor) (values : Slots) : Except CsvError Csv.Bytes := do
  if values.length > limits.maxRows then throw (.rowLimit limits.maxRows)
  checkRequired field values
  let wire ← (Utf8.encode (schema field) codecs (values.map fun cell _ => cell)).mapError .csv
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  return wire

def decode (limits : CsvLimits) (field : Descriptor) (wire : Csv.Bytes) : Except CsvError Slots := do
  if wire.length > limits.maxBytes then throw (.byteLimit limits.maxBytes wire.length)
  let rows ← (Bounded.decode limits.maxRows (schema field) codecs wire).mapError fun
    | .csv cause => CsvError.csv cause
    | .rowLimit => CsvError.rowLimit limits.maxRows
  let values := readRows rows
  checkRequired field values
  return values

inductive ToCsvError where
  | source (cause : ReadError)
  | csv (cause : CsvError)
  deriving DecidableEq, Repr

inductive FromCsvError where
  | csv (cause : CsvError)
  | writer (cause : WriteError)
  deriving DecidableEq, Repr

/-- Exhaust the original IPC source before encoding its flattened rows.
Carry the exact field descriptor outside the CSV bytes. -/
def toCsv (ipc : IpcLimits) (csv : CsvLimits) (layout : Layout) (input : KBytes) :
    Except ToCsvError Output := do
  let observed ← (readIpc ipc layout input).mapError .source
  let wire ← (encode csv observed.field observed.batches.flatten).mapError .csv
  return ⟨observed.field, wire⟩

/-- Decode the complete typed CSV before emitting a single RecordBatch,
including for a header-only input. The writer adds modern EOS. -/
def fromCsv (csv : CsvLimits) (ipc : IpcLimits) (field : Descriptor) (wire : Csv.Bytes) :
    Except FromCsvError KBytes := do
  let values ← (decode csv field wire).mapError .csv
  (emitIpc ipc field values).mapError .writer

end Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs

/-! Checked native V5 records for ordered INT32, BinaryView and Utf8View fields. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.OrderedWriter

inductive Column where
  | int32 (name : String) (nullable : Bool) (values : List (Option Int32))
  | binary (name : String) (nullable : Bool) (values : List (Option KBytes))
  | utf8View (name : String) (nullable : Bool) (values : List (Option String))

def Column.field : Column → Field
  | .int32 name nullable _ => ⟨name, nullable, .primitive .int32⟩
  | .binary name nullable _ => ⟨name, nullable, .view .binary⟩
  | .utf8View name nullable _ => ⟨name, nullable, .view .utf8⟩

def Column.observe : Column → Writer.ColumnObservation
  | .int32 _ _ values => .int32 (values.map (Option.map Arrow.Value.int32))
  | .binary _ _ values => .binaryView (values.map (Option.map KBytes.toList))
  | .utf8View _ _ values => .utf8View values

def Column.length : Column → Nat
  | .int32 _ _ values => values.length
  | .binary _ _ values => values.length
  | .utf8View _ _ values => values.length

structure BatchInput where
  rowCount : Nat
  columns : List Column

def BatchInput.fields (input : BatchInput) : List Field := input.columns.map Column.field

def BatchInput.observe (input : BatchInput) : StreamWriter.BatchObservation :=
  (input.rowCount, some (input.columns.map fun column => (column.field, column.observe)))

/-- The IPC budgets govern the number, order and repetition of these fields. -/
def supported (fields : List Field) : Bool :=
  fields.all (fun field => field.kind.isView || field.kind == .primitive .int32)

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | field (position : Nat) (cause : Writer.Error)
  | unsupportedSchema
  | schemaMismatch
  | metadata (cause : MetadataError)
  | metadataMismatch
  | binding (cause : MixedFlat.Error)
  | bindingMismatch
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | unsupportedSchema
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

structure PhysicalColumn where
  node : FieldNode
  count : Option Nat
  parts : List KBytes

/-- Each view column starts with a fresh local buffer index space. -/
def Column.compile (limits : MixedFlat.Limits) (rows : Nat) (column : Column) (position : Nat) :
    Except RecordError PhysicalColumn := do
  if column.length ≠ rows then throw (.field position (.rowCount position rows column.length))
  match column with
  | .int32 _ nullable values =>
    if !nullable && values.any Option.isNone then throw (.field position (.nullInRequired position))
    let native := Arrow.Writer.ColumnValues.int32 values
    return ⟨⟨native.length, native.nullCount⟩, none, native.emit⟩
  | .binary _ nullable values =>
    let view ← (BinaryView.Column.Writer.emitBinary limits.view nullable values).mapError
      (fun cause => .field position (.view position cause))
    return ⟨view.node, some view.buffers.payload.data.size, Writer.viewParts view.buffers⟩
  | .utf8View _ nullable values =>
    let view ← (BinaryView.Column.Writer.emitUtf8 limits.view nullable values).mapError
      (fun cause => .field position (.view position cause))
    return ⟨view.node, some view.buffers.payload.data.size, Writer.viewParts view.buffers⟩

def compile (limits : MixedFlat.Limits) (input : BatchInput) : Except RecordError (List PhysicalColumn) :=
  input.columns.zipIdx.mapM fun (column, position) => column.compile limits input.rowCount position

def descriptorGroups : List Nat → List Buffer → List (List Buffer)
  | [], _ => []
  | width :: widths, buffers => buffers.take width :: descriptorGroups widths (buffers.drop width)

def pack (rows : Nat) (columns : List PhysicalColumn) : Writer.Emitted :=
  let counts := columns.filterMap PhysicalColumn.count
  let (buffers, body) := Arrow.Writer.packBuffers 0 (columns.flatMap PhysicalColumn.parts)
  let batch := ⟨rows, columns.map PhysicalColumn.node, buffers⟩
  ⟨⟨batch, body.len, counts⟩, Writer.Wire.metadataWithCounts batch body.len counts, body⟩

/-- Counts and complete descriptor ranges are checked in field order.
A primitive position has no variadic word. An empty view has a zero word. -/
def bindings {fields : List Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) (columns : List PhysicalColumn) : Prop :=
  plan.assignment.groups.map Group.count = columns.map PhysicalColumn.count ∧
  plan.assignment.groups.map Group.buffers =
    descriptorGroups (columns.map (·.parts.length)) metadata.batch.buffers

instance {fields : List Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) (columns : List PhysicalColumn) : Decidable (bindings plan columns) := by
  unfold bindings
  infer_instance

structure Record (limits : MixedFlat.Limits) (input : BatchInput) where
  output : Writer.Emitted
  columns : List PhysicalColumn
  compiled : compile limits input = .ok columns
  packed : output = pack input.rowCount columns
  metadataRead : MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
    input.fields output.metadataBytes = .ok output.metadata
  plan : Plan input.fields output.metadata output.body
  bound : MixedFlat.bindBatch limits input.fields output.metadata output.body = .ok plan
  assigned : bindings plan columns

def checkRecord (limits : MixedFlat.Limits) (rows : Nat) (fields : List Field)
    (shape : List Field → Bool := fun _ => true) : Except RecordError Unit := do
  if !(shape fields && supported fields) then throw .unsupportedSchema
  let ipc := limits.observation.ipc
  if fields.length > ipc.fields then throw (.ipc (.limit .fields))
  if rows > ipc.rows then throw (.ipc (.limit .rows))
  if rows ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  (Body.checkBudget limits.observation fields.length rows).mapError .ipc

def checkSizes (limits : MixedFlat.Limits) (columns : List PhysicalColumn) : Except RecordError Unit := do
  let counts := columns.filterMap PhysicalColumn.count
  if counts.sum > limits.totalDataBuffers then throw (.metadata .totalDataBufferLimit)
  let parts := columns.flatMap PhysicalColumn.parts
  let size := Writer.Wire.metadataSizeWithCounts columns.length parts.length counts.length
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > limits.observation.ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))
  let body := (parts.map fun piece => piece.len + Arrow.Writer.padding piece.len).sum
  if body ≥ 2^63 then throw (.ipc (.malformed .bodyLength))
  if body > limits.observation.ipc.bodyBytes then throw (.ipc (.limit .bodyBytes))

/-- The metadata parser and descriptor binder certify the emitted record
before it can be framed. -/
def emitRecord (limits : MixedFlat.Limits) (input : BatchInput)
    (shape : List Field → Bool := fun _ => true) : Except RecordError (Record limits input) := do
  checkRecord limits input.rowCount input.fields shape
  match compiled : compile limits input with
  | .error cause => throw cause
  | .ok columns =>
    checkSizes limits columns
    let output := pack input.rowCount columns
    match parsed : MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
        input.fields output.metadataBytes with
    | .error cause => throw (.metadata cause)
    | .ok metadata =>
      if same : metadata = output.metadata then
        match bound : MixedFlat.bindBatch limits input.fields output.metadata output.body with
        | .error cause => throw (.binding cause)
        | .ok plan =>
          if assigned : bindings plan columns then
            return ⟨output, columns, compiled, rfl, same ▸ parsed, plan, bound, assigned⟩
          else throw .bindingMismatch
      else throw .metadataMismatch

namespace Wire

def fieldBytes (field : Field) : KBytes :=
  match field.kind with
  | .primitive kind => MetadataWriter.Wire.fieldBytes ⟨field.name, field.nullable, kind⟩
  | .view kind => StreamWriter.Wire.viewFieldBytes field.name field.nullable kind

def schema (fields : List Field) : KBytes :=
  MetadataWriter.Wire.messagePrefix 1 56 0 ++ MetadataWriter.Wire.schemaPayloadOf (fields.map fieldBytes)

def schemaSize (fields : List Field) : Nat :=
  let vectorEnd := 20 + fields.length * 4
  48 + vectorEnd + Arrow.Writer.padding vectorEnd + (fields.map fun field =>
    StreamWriter.Wire.fieldSize field.name).sum

end Wire

def emitSchema (ipc : Arrow.Limits) (fields : List Field)
    (shape : List Field → Bool := fun _ => true) : Except Error KBytes := do
  if !(shape fields && supported fields) then throw .unsupportedSchema
  if fields.length > ipc.fields then throw (.ipc (.limit .fields))
  let size := Wire.schemaSize fields
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))
  return Arrow.StreamWriter.envelopeBytes size ++ Wire.schema fields

/-- Frame checked records in the given order, including explicit zero-row
records, then append the modern EOS. -/
def serialize (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput)
    (shape : List Field → Bool := fun _ => true) : Except Error KBytes := do
  let ipc := limits.observation.ipc
  if batches.length > ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits.observation fields.length (batches.map (·.rowCount)).sum).mapError .ipc
  let header ← emitSchema ipc fields shape
  let records ← batches.zipIdx.mapM fun (batch, index) => do
    if batch.fields ≠ fields then throw (.record index .schemaMismatch)
    let record ← (emitRecord limits batch shape).mapError (.record index)
    let frame := record.output
    return Arrow.StreamWriter.envelopeBytes frame.metadataBytes.len ++ (frame.metadataBytes ++ frame.body)
  return header ++ records.foldr (· ++ ·) Arrow.StreamWriter.eos

/-- Certify the ordered fields and slots through the existing exact-EOS reader. -/
def emit (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput)
    (shape : List Field → Bool := fun _ => true) : Except Error KBytes := do
  let wire ← serialize limits fields batches shape
  let decoded ← (Stream.read limits wire).mapError .readback
  if decoded.fields = fields ∧ decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe then
    return wire
  else throw .readbackMismatch

end Silmaril.Formats.Arrow.MixedFlat.OrderedWriter

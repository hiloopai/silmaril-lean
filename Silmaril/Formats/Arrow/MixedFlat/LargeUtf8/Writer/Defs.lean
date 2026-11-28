module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
public import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs

/-! Checked mixed-flat records and modern V5 streams with native LargeUtf8. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer

inductive Column where
  | existing (column : OrderedWriter.Column)
  | largeUtf8 (name : String) (nullable : Bool) (values : Arrow.LargeUtf8.Column)

def Column.field : Column → Field
  | .existing column =>
    let field := column.field
    ⟨field.name, field.nullable, .existing field.kind⟩
  | .largeUtf8 name nullable _ => ⟨name, nullable, .largeUtf8⟩

inductive ColumnObservation where
  | existing (value : MixedFlat.Writer.ColumnObservation)
  | largeUtf8 (values : Arrow.LargeUtf8.Column)
  deriving DecidableEq

def Column.observe : Column → ColumnObservation
  | .existing column => .existing column.observe
  | .largeUtf8 _ _ values => .largeUtf8 values

def observeColumn : LargeUtf8.Column → ColumnObservation
  | .existing (.primitive values) => .existing (.int32 values)
  | .existing (.binaryView values) => .existing (.binaryView (values.map (Option.map KBytes.toList)))
  | .existing (.utf8View values) => .existing (.utf8View values)
  | .largeUtf8 values => .largeUtf8 values

structure BatchInput where
  rowCount : Nat
  columns : List Column

def BatchInput.fields (input : BatchInput) : List Field := input.columns.map Column.field

abbrev BatchObservation := Nat × List (Field × ColumnObservation)

def BatchInput.observe (input : BatchInput) : BatchObservation :=
  (input.rowCount, input.columns.map fun column => (column.field, column.observe))

def observeBatch (observed : LargeUtf8.Observed) : BatchObservation :=
  (observed.rowCount, observed.columns.map fun (field, column) => (field, observeColumn column))

inductive RecordError where
  | ordered (cause : OrderedWriter.RecordError)
  | largeUtf8 (position : Nat) (cause : Binary.StreamWriter.RecordError)
  | readback (cause : LargeUtf8.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (ordinal : Nat) (cause : RecordError)
  | schemaReadback (cause : Stream.SchemaError)
  | recordReadback (ordinal offset : Nat) (cause : Stream.Cause)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- LargeUtf8 uses validity, signed i64 UTF-8 byte offsets and data. Its
column never contributes a variadic count word. -/
def Column.compile (limits : MixedFlat.Limits) (rows : Nat) (position : Nat) :
    Column → Except RecordError OrderedWriter.PhysicalColumn
  | .existing column => (column.compile limits rows position).mapError .ordered
  | .largeUtf8 _ nullable values =>
    if values.length ≠ rows then
      .error (.ordered (.field position (.rowCount position rows values.length)))
    else do
      let node ← (Binary.StreamWriter.checkRecordSize .i64 limits.observation.ipc nullable values
        Arrow.Writer.utf8ByteCount).mapError (.largeUtf8 position)
      let parts := Binary.StreamWriter.columnPartsFor .i64 (Arrow.LargeUtf8.StreamWriter.encodeColumn values)
      return ⟨node, none, parts⟩

def compile (limits : MixedFlat.Limits) (input : BatchInput) :
    Except RecordError (List OrderedWriter.PhysicalColumn) :=
  input.columns.zipIdx.mapM fun (column, position) => column.compile limits input.rowCount position

structure Record (limits : MixedFlat.Limits) (input : BatchInput) where
  output : MixedFlat.Writer.Emitted
  physical : List OrderedWriter.PhysicalColumn
  compiled : compile limits input = .ok physical
  packed : output = OrderedWriter.pack input.rowCount physical
  metadataRead : LargeUtf8.readMetadata limits input.fields output.metadataBytes = .ok output.metadata
  readback : ∃ decoded, LargeUtf8.readParsed limits input.fields output.metadata output.body = .ok decoded ∧
    observeBatch decoded = input.observe

/-- Reuse the ordered metadata and body packer and certify the result with
the opt-in mixed reader before exposing the record. -/
def emitRecord (limits : MixedFlat.Limits) (input : BatchInput) :
    Except RecordError (Record limits input) := do
  (OrderedWriter.checkRecordWith limits input.rowCount (input.fields.map Field.layout)
    (fun _ => true)).mapError .ordered
  match compiled : compile limits input with
  | .error cause => throw cause
  | .ok physical =>
    (OrderedWriter.checkSizes limits physical).mapError .ordered
    let output := OrderedWriter.pack input.rowCount physical
    match parsed : LargeUtf8.readMetadata limits input.fields output.metadataBytes with
    | .error cause => throw (.ordered (.metadata cause))
    | .ok metadata =>
      if same : metadata = output.metadata then
        match read : LargeUtf8.readParsed limits input.fields output.metadata output.body with
        | .error cause => throw (.readback cause)
        | .ok decoded =>
          if agrees : observeBatch decoded = input.observe then
            return ⟨output, physical, compiled, rfl, same ▸ parsed, ⟨decoded, read, agrees⟩⟩
          else throw .readbackMismatch
      else throw (.ordered .metadataMismatch)

namespace Wire

open MetadataWriter.Wire

def fieldBytes (field : Field) : KBytes :=
  match field.kind with
  | .existing kind => OrderedWriter.Wire.fieldBytes ⟨field.name, field.nullable, kind⟩
  | .largeUtf8 =>
    fieldFragment field.name field.nullable (Binary.StreamWriter.Profile.tag .largeUtf8)
      (words [halfwords 4 4, 0, 8, 0, 0])

def schema (fields : List Field) : KBytes :=
  messagePrefix 1 56 0 ++ schemaPayloadOf (fields.map Wire.fieldBytes)

def schemaSize (fields : List Field) : Nat :=
  OrderedWriter.Wire.schemaSize (fields.map Field.layout)

end Wire

def emitSchema (ipc : Arrow.Limits) (fields : List Field) : Except Error KBytes := do
  if fields.length > ipc.fields then throw (.ipc (.limit .fields))
  let size := Wire.schemaSize fields
  let _ ← (Arrow.readPrefix ipc 0xffffffff size).mapError .ipc
  return Arrow.StreamWriter.envelopeBytes size ++ Wire.schema fields

/-- The stream fields are explicit even with no batches. A zero-column
batch still carries its declared row count. -/
def serialize (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error KBytes := do
  let ipc := limits.observation.ipc
  if batches.length > ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits.observation fields.length (batches.map (·.rowCount)).sum).mapError .ipc
  let header ← emitSchema ipc fields
  let records ← batches.zipIdx.mapM fun (batch, ordinal) => do
    if batch.fields ≠ fields then throw (.record ordinal (.ordered .schemaMismatch))
    let record ← (emitRecord limits batch).mapError (.record ordinal)
    let frame := record.output
    return Arrow.StreamWriter.envelopeBytes frame.metadataBytes.len ++ (frame.metadataBytes ++ frame.body)
  return header ++ records.foldr (· ++ ·) Arrow.StreamWriter.eos

def Agrees (fields : List Field) (batches : List BatchInput) (decoded : Stream.Observed) : Prop :=
  decoded.fields = fields ∧
    decoded.trace.batches.map (observeBatch ∘ Stream.Batch.observed) = batches.map BatchInput.observe

instance (fields : List Field) (batches : List BatchInput) (decoded : Stream.Observed) :
    Decidable (Agrees fields batches decoded) := by
  unfold Agrees
  infer_instance

/-- Publish only a modern stream whose exact ordered observation matches the
input and whose direct reader reaches exact EOS. -/
def emit (limits : MixedFlat.Limits) (fields : List Field) (batches : List BatchInput) :
    Except Error KBytes := do
  let wire ← serialize limits fields batches
  let decoded ← (Stream.read limits .modern wire).mapError .schemaReadback
  match decoded.trace.termination with
  | .error ordinal offset cause => .error (.recordReadback ordinal offset cause)
  | .eos _ =>
    if Agrees fields batches decoded then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer

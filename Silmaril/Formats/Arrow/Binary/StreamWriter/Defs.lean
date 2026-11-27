module

public import Silmaril.Formats.Arrow.Binary.Stream.Defs
public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! One plain Binary field in a modern Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.StreamWriter

namespace Wire

open MetadataWriter.Wire

def schemaFor (width : Binary.Offsets.Width) (name : String) (nullable : Bool) : KBytes :=
  let tag := match width with
    | .i32 => 4
    | .i64 => 19
  let emptyType := words [halfwords 4 4, 0, 8, 0, 0]
  messagePrefix 1 56 0 ++ schemaPayloadOf [fieldFragment name nullable tag emptyType]

def schema (field : Binary.Field) : KBytes := schemaFor .i32 field.name field.nullable

/-- The field fragment starts at byte 72 and includes a 53-byte prefix and
terminator before padding. -/
def schemaSizeFor (name : String) : Nat :=
  let fragment := 53 + name.utf8ByteSize
  72 + fragment + Arrow.Writer.padding fragment

def schemaSize (field : Binary.Field) : Nat := schemaSizeFor field.name

end Wire

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | nullInRequired
  | signedOffsetExtent (bytes : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (ordinal : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def valueSize (value : Option KBytes) : Nat := (value.getD KBytes.empty).len

def dataSize (values : Binary.Column) : Nat :=
  values.foldl (fun offset value => offset + valueSize value) 0

def bodySizeFor (width : Binary.Offsets.Width) (rows bytes : Nat) : Nat :=
  ([(rows + 7) / 8, width.bytes * (rows + 1), bytes].map
    (fun size => size + Arrow.Writer.padding size)).sum

def bodySize := bodySizeFor .i32

/-- Check the input before allocating body buffers. The terminal data offset
bounds every signed offset in the batch. -/
def checkRecordFor (width : Binary.Offsets.Width) (limits : Limits) (nullable : Bool)
    (values : Binary.Column) :
    Except RecordError FieldNode :=
  let rows := values.length
  if rows > limits.rows then .error (.ipc (.limit .rows))
  else
    let nulls := values.countP Option.isNone
    if !nullable && nulls != 0 then .error .nullInRequired
    else
      let bytes := dataSize values
      if bytes ≥ width.signedLimit then .error (.signedOffsetExtent bytes)
      else
        let paddedBytes := bodySizeFor width rows bytes
        if paddedBytes > limits.bodyBytes then .error (.ipc (.limit .bodyBytes))
        else if rows ≥ 2^63 ∨ paddedBytes ≥ 2^63 then .error (.ipc (.malformed .batchLayout))
        else if values.all (fun value => (value.map KBytes.wf).getD true) then .ok ⟨rows, nulls⟩
        else .error (.ipc (.malformed .source))

def checkRecord := checkRecordFor .i32

def offsetWords (values : Binary.Column) : List Nat :=
  values.scanl (fun offset value => offset + valueSize value) 0

/-- Null and empty slots repeat the current offset. A validity bit
distinguishes their observations. -/
def encodeColumn (width : Binary.Offsets.Width) (values : Binary.Column) : Binary.Buffers :=
  ⟨Arrow.Writer.emitBitmap values, Arrow.Writer.emitWords width.bytes (offsetWords values),
    BinaryView.Column.Writer.join (values.filterMap id)⟩

def columnPartsFor (width : Binary.Offsets.Width) (values : Binary.Column) : List KBytes :=
  let buffers := encodeColumn width values
  [buffers.validity, buffers.offsets, buffers.data]

def columnParts := columnPartsFor .i32

def emitRecordFor (width : Binary.Offsets.Width) (limits : Limits) (nullable : Bool)
    (values : Binary.Column) : Except RecordError KBytes := do
  let node ← checkRecordFor width limits nullable values
  let (descriptors, body) := Arrow.Writer.packBuffers 0 (columnPartsFor width values)
  let metadata : RecordBatch := ⟨node.length, [node], descriptors⟩
  (Arrow.StreamWriter.emitFrame limits ⟨.recordBatch metadata, body.len⟩ body).mapError .ipc

def emitRecord (limits : Limits) (field : Binary.Field) (values : Binary.Column) :
    Except RecordError KBytes :=
  emitRecordFor .i32 limits field.nullable values

def serializeFor (width : Binary.Offsets.Width) (limits : Limits) (name : String)
    (nullable : Bool) (batches : List Binary.Column) : Except Error KBytes :=
  if limits.fields = 0 then .error (.ipc (.limit .fields))
  else if batches.length > limits.batches then .error (.ipc (.limit .batches))
  else do
    let size := Wire.schemaSizeFor name
    let _ ← (Arrow.readPrefix limits 0xffffffff size).mapError .ipc
    let records ← batches.zipIdx.mapM fun (values, ordinal) =>
      (emitRecordFor width limits nullable values).mapError (.record ordinal)
    let schema := Arrow.StreamWriter.envelopeBytes size ++ Wire.schemaFor width name nullable
    return schema ++ (BinaryView.Column.Writer.join records ++ Arrow.StreamWriter.eos)

def serialize (limits : Limits) (field : Binary.Field) (batches : List Binary.Column) :
    Except Error KBytes :=
  serializeFor .i32 limits field.name field.nullable batches

def RecordBounds (width : Binary.Offsets.Width) (limits : Limits) (values : Binary.Column) : Prop :=
  values.length ≤ limits.rows ∧ dataSize values < width.signedLimit ∧
    bodySizeFor width values.length (dataSize values) ≤ limits.bodyBytes

def StreamBounds (width : Binary.Offsets.Width) (limits : Limits) (name : String)
    (batches : List Binary.Column) : Prop :=
  0 < limits.fields ∧ Wire.schemaSizeFor name ≤ limits.metadataBytes ∧
    batches.length ≤ limits.batches ∧ ∀ values ∈ batches, RecordBounds width limits values

/-- Canonical buffers use prefix sums of opaque byte lengths and no unused
data. Offsets include zero and the terminal position. -/
def ColumnWire (width : Binary.Offsets.Width) (values : Binary.Column)
    (buffers : Binary.Buffers) : Prop :=
  buffers.validity.len = (values.length + 7) / 8 ∧
    buffers.offsets.len = width.bytes * (values.length + 1) ∧
    buffers.data.len = dataSize values ∧
    buffers.data.toList = (values.filterMap id).flatMap KBytes.toList ∧
    (∀ index (within : index < values.length),
      Body.validAt buffers.validity index = some values[index].isSome) ∧
    ∀ index, index ≤ values.length →
      buffers.offsets.readLE (width.bytes * index) width.bytes = some (dataSize (values.take index))

/-- A record frame contains the canonical descriptor list and exactly its
packed body. The serialized metadata names the same node and descriptors. -/
def RecordWire (width : Binary.Offsets.Width) (limits : Limits) (values : Binary.Column)
    (wire : KBytes) : Prop :=
  let parts := columnPartsFor width values
  let packed := Arrow.Writer.packBuffers 0 parts
  let node : FieldNode := ⟨values.length, values.countP Option.isNone⟩
  let message : Message := ⟨.recordBatch ⟨values.length, [node], packed.1⟩, packed.2.len⟩
  let size := MetadataWriter.wireSize message
  RecordBounds width limits values ∧ ColumnWire width values (encodeColumn width values) ∧
    Arrow.Writer.PackedWire packed.2.toList 0 parts packed.1 ∧
    packed.2.len = bodySizeFor width values.length (dataSize values) ∧
    wire.wf = true ∧ wire.len = 8 + size + message.bodyLength ∧
    Arrow.readEnvelope limits wire 0 = .ok (.metadata size) ∧
    Arrow.readMessage limits (wire.slice 8 size) = .ok message ∧
    ∃ body, Arrow.readBody limits wire (8 + size) message.bodyLength = .ok body ∧
      body.toList = packed.2.toList

def SerializedWire (width : Binary.Offsets.Width) (limits : Limits) (name : String)
    (nullable : Bool) (batches : List Binary.Column) (wire : KBytes) : Prop :=
  StreamBounds width limits name batches ∧ ∃ records,
    List.Forall₂ (RecordWire width limits) batches records ∧
    wire = (Arrow.StreamWriter.envelopeBytes (Wire.schemaSizeFor name) ++
      Wire.schemaFor width name nullable) ++
      (BinaryView.Column.Writer.join records ++ Arrow.StreamWriter.eos)

def observe (column : Binary.Column) : List (Option (List UInt8)) :=
  column.map (Option.map KBytes.toList)

def Agrees (field : Binary.Field) (batches : List Binary.Column) (decoded : Stream.Observed) : Prop :=
  decoded.field = field ∧ decoded.batches.map (observe ∘ Stream.Batch.values) = batches.map observe

instance (field : Binary.Field) (batches : List Binary.Column) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Certify the emitted wire against the checked stream reader, including the
declared field, exact optional octets and every batch boundary. -/
def emit (limits : Limits) (field : Binary.Field) (batches : List Binary.Column) :
    Except Error KBytes := do
  let wire ← serialize limits field batches
  let decoded ← (Stream.read limits .modern wire).mapError .readback
  if Agrees field batches decoded then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.Binary.StreamWriter

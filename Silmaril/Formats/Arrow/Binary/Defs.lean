module

public import Silmaril.Formats.Arrow.Body.Defs
public import Mathlib.Data.List.Forall2

/-! # Checked plain Arrow Binary

One flat little-endian V5 field, with an optional validity bitmap, signed i32
offsets and opaque data. Both the physical reader and the paired IPC batch
reader are opt-in. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary

structure Buffers where
  validity : KBytes
  offsets : KBytes
  data : KBytes

abbrev Column := List (Option KBytes)

inductive Error where
  | schema (cause : SchemaError)
  | ipc (cause : Arrow.Error)
  | bodyLength (declared actual : Nat)
  | offsetMissing (index : Nat)
  | offsetNegative (index word : Nat)
  | offsetDescending (index previous current : Nat)
  | offsetOutsideData (index offset dataLength : Nat)
  deriving DecidableEq, Repr

structure Observed where
  field : Field
  values : Column

/-- Read a signed offset at its word index. Preserve the negative word in the
error and check the data bound before any slicing. -/
def readOffset (buffers : Buffers) (index : Nat) : Except Error Nat := do
  let some word := buffers.offsets.readLE (4 * index) 4 | throw (.offsetMissing index)
  if word ≥ 2^31 then .error (.offsetNegative index word)
  else if word > buffers.data.len then .error (.offsetOutsideData index word buffers.data.len)
  else .ok word

/-- Even a null slot must have a valid adjacent offset pair. A valid slot
with equal offsets returns present zero-length bytes. -/
def readSlot (buffers : Buffers) (index : Nat) : Except Error (Option KBytes) := do
  let lo ← readOffset buffers index
  let hi ← readOffset buffers (index + 1)
  if hi < lo then .error (.offsetDescending (index + 1) lo hi)
  else
    match Body.validAt buffers.validity index with
    | none => .error (.ipc (.malformed .validityBitmap))
    | some valid => .ok (if valid then some (buffers.data.slice lo (hi - lo)) else none)

def checkColumn (limits : Limits) (nullable : Bool) (node : FieldNode) (buffers : Buffers) :
    Except Error Unit := do
  if !buffers.validity.wf || !buffers.offsets.wf || !buffers.data.wf then
    throw (.ipc (.malformed .source))
  if node.length > limits.rows then throw (.ipc (.limit .rows))
  if buffers.validity.len + buffers.offsets.len + buffers.data.len > limits.bodyBytes then
    throw (.ipc (.limit .bodyBytes))
  if node.nullCount > node.length || (!nullable && node.nullCount != 0) then
    throw (.ipc (.malformed .validityBitmap))
  if ¬ Body.BitmapExtent buffers.validity node.length then
    throw (.ipc (.malformed .validityBitmap))

/-- Validate offset zero even for zero rows. Nonzero initial offsets and
trailing bytes are admitted as long as all logical windows fit. -/
def readColumn (limits : Limits) (nullable : Bool) (node : FieldNode) (buffers : Buffers) :
    Except Error Column := do
  checkColumn limits nullable node buffers
  let _ ← readOffset buffers 0
  let values ← (List.range node.length).mapM (readSlot buffers)
  if values.countP Option.isNone ≠ node.nullCount then .error (.ipc (.malformed .validityBitmap))
  else .ok values

/-- One node and three aligned, ordered, in-bounds descriptors in validity,
offsets, data order. Check all three before slicing the body. -/
def bindBody (limits : Limits) (batch : RecordBatch) (body : KBytes) :
    Except Error (FieldNode × Buffers) :=
  if !body.wf then .error (.ipc (.malformed .source))
  else if body.len > limits.bodyBytes then .error (.ipc (.limit .bodyBytes))
  else
    match batch.nodes, batch.buffers with
    | [node], [validity, offsets, data] =>
      if node.length = batch.rowCount ∧ BuffersFit body.len 0 [validity, offsets, data] then
        .ok (node, ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets,
          Body.sliceBuffer body data⟩)
      else .error (.ipc (.malformed .batchLayout))
    | _, _ => .error (.ipc (.malformed .batchLayout))

/-- Decode padded Schema and RecordBatch metadata and the exact corresponding
body. The caller supplies the pairing and outer IPC envelope. -/
def readBatch (limits : Limits) (schemaMetadata recordMetadata body : KBytes) :
    Except Error Observed := do
  let field ← (readSchema limits schemaMetadata).mapError .schema
  let message ← (Arrow.readMessage limits recordMetadata).mapError .ipc
  let .recordBatch batch := message.header | throw (.ipc (.malformed .schemaOrder))
  if message.bodyLength ≠ body.len then .error (.bodyLength message.bodyLength body.len)
  else if body.len % 8 ≠ 0 then .error (.ipc (.malformed .alignment))
  else
    let (node, buffers) ← bindBody limits batch body
    return ⟨field, ← readColumn limits field.nullable node buffers⟩

def OffsetWire (buffers : Buffers) (index offset : Nat) : Prop :=
  buffers.offsets.readLE (4 * index) 4 = some offset ∧ offset < 2^31 ∧ offset ≤ buffers.data.len

def SlotWire (buffers : Buffers) (index : Nat) (value : Option KBytes) : Prop :=
  ∃ lo hi valid, OffsetWire buffers index lo ∧ OffsetWire buffers (index + 1) hi ∧
    lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
    value = (if valid then some (buffers.data.slice lo (hi - lo)) else none)

def ColumnWire (node : FieldNode) (buffers : Buffers) (values : Column) : Prop :=
  (∃ initial, OffsetWire buffers 0 initial) ∧
    List.Forall₂ (SlotWire buffers) (List.range node.length) values ∧
    values.countP Option.isNone = node.nullCount

def BodyWire (batch : RecordBatch) (body : KBytes) (node : FieldNode) (buffers : Buffers) : Prop :=
  batch.nodes = [node] ∧ node.length = batch.rowCount ∧
    ∃ validity offsets data, batch.buffers = [validity, offsets, data] ∧
      BuffersFit body.len 0 [validity, offsets, data] ∧
      buffers = ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets,
        Body.sliceBuffer body data⟩

def BatchWire (limits : Limits) (schemaMetadata recordMetadata body : KBytes)
    (observed : Observed) : Prop :=
  readSchema limits schemaMetadata = .ok observed.field ∧ body.len % 8 = 0 ∧
    ∃ batch node buffers,
      Arrow.readMessage limits recordMetadata = .ok ⟨.recordBatch batch, body.len⟩ ∧
      BodyWire batch body node buffers ∧
      checkColumn limits observed.field.nullable node buffers = .ok () ∧
      ColumnWire node buffers observed.values

end Silmaril.Formats.Arrow.Binary

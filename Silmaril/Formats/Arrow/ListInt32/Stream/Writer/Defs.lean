module

public import Silmaril.Formats.Arrow.ListInt32.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Canonical native V5 IPC emission for one nullable List<Int32> field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.ListInt32.Stream.Writer

namespace Wire

open MetadataWriter.Wire

/-- The parent fragment places its 16-byte vtable before the 20-byte table,
then the empty List type, singleton child vector and field name. -/
def parentSize (name : String) : Nat :=
  let size := 57 + name.utf8ByteSize
  size + Arrow.Writer.padding size

def parentFragmentFor (parentNullable : Bool) (name : String) : KBytes :=
  let nameBytes := Arrow.Writer.emitWords 1 (name.toByteArray.data.toList.map UInt8.toNat)
  -- The vector element at byte 48 references the child table, 12 bytes into its fragment.
  let childOffset := parentSize name + 12 - 48
  pad (words [halfwords 16 20, halfwords 4 8, halfwords 9 12, halfwords 0 16,
      16, 32, parentNullable.toNat + 12 * 256, 12, 12, halfwords 4 4, 4, 1, childOffset, nameBytes.len] ++
    (nameBytes ++ KBytes.zeros 1))

def parentFragment := parentFragmentFor true

def childField (field : ListInt32.Field) : Arrow.Field :=
  ⟨field.childName, true, .int32⟩

/-- The Schema vector at payload byte 16 points to the parent table at
payload byte 40. The child reuses the checked primitive field layout. -/
def schemaFor (parentNullable : Bool) (field : ListInt32.Field) : KBytes :=
  messagePrefix 1 56 0 ++
    (words [halfwords 8 8, halfwords 0 4, 8, 4, 1, 20] ++
      (parentFragmentFor parentNullable field.name ++ fieldBytes (childField field)))

def schema := schemaFor true

def schemaSize (field : ListInt32.Field) : Nat :=
  let childSize := 53 + field.childName.utf8ByteSize
  72 + parentSize field.name + childSize + Arrow.Writer.padding childSize

end Wire

def childCount (rows : List Row) : Nat :=
  (rows.map (fun row => (row.getD []).length)).sum

def childSlots (rows : List Row) : List (Option Int32) :=
  rows.flatMap (·.getD [])

def offsetWords (rows : List Row) : List Nat :=
  rows.scanl (fun offset row => offset + (row.getD []).length) 0

/-- Null parents use empty physical spans. Parent validity distinguishes
them from empty lists. The child retains its own nullable INT32 slots. -/
def parts (rows : List Row) : List KBytes :=
  Arrow.Writer.emitBitmap rows :: Arrow.Writer.emitWords 4 (offsetWords rows) ::
    (Arrow.Writer.ColumnValues.int32 (childSlots rows)).emit

def sizes (rows children : Nat) : List Nat :=
  [(rows + 7) / 8, 4 * (rows + 1), (children + 7) / 8, 4 * children]

def bodySize (rows children : Nat) : Nat :=
  ((sizes rows children).map fun size => size + Arrow.Writer.padding size).sum

def metadata (rows : List Row) (buffers : List Buffer) : RecordBatch :=
  let children := childSlots rows
  ⟨rows.length, [⟨rows.length, rows.countP Option.isNone⟩,
    ⟨children.length, children.countP Option.isNone⟩], buffers⟩

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | offsetOverflow
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | rowLimit
  | childLimit
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Guard logical counts and the padded body size before allocating
the byte buffers. Offsets are signed 32-bit, including the final one. -/
def checkRecord (ipc : Arrow.Limits) (rows children : Nat) : Except RecordError Unit := do
  if ipc.fields < 2 then return ← throw (.ipc (.limit .fields))
  if ipc.rows < rows then return ← throw (.ipc (.limit .rows))
  if 2^63 ≤ rows then return ← throw (.ipc (.malformed .flatbuffer))
  if 2^31 ≤ children then return ← throw .offsetOverflow
  let size := bodySize rows children
  if 2^63 ≤ size then return ← throw (.ipc (.malformed .bodyLength))
  if ipc.bodyBytes < size then return ← throw (.ipc (.limit .bodyBytes))
  if ipc.metadataBytes < 200 then return ← throw (.ipc (.limit .metadataBytes))

def emitSchemaFor (parentNullable : Bool) (ipc : Arrow.Limits) (field : ListInt32.Field) : Except Error KBytes := do
  if ipc.fields = 0 then throw (.ipc (.limit .fields))
  let size := Wire.schemaSize field
  if 2^31 ≤ size then throw (.ipc (.malformed .metadataLength))
  if ipc.metadataBytes < size then throw (.ipc (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ Wire.schemaFor parentNullable field

def emitSchema := emitSchemaFor true

/-- Share the V5 record message writer and the common aligned buffer packer. -/
def emitRecord (ipc : Arrow.Limits) (rows : List Row) : Except RecordError KBytes := do
  checkRecord ipc rows.length (childCount rows)
  let (buffers, body) := Arrow.Writer.packBuffers 0 (parts rows)
  (StreamWriter.emitFrame ipc ⟨.recordBatch (metadata rows buffers), body.len⟩ body).mapError .ipc

def serializeFor (parentNullable : Bool) (limits : Stream.Limits) (field : ListInt32.Field) (batches : List (List Row)) :
    Except Error KBytes := do
  if limits.ipc.batches < batches.length then return ← throw (.ipc (.limit .batches))
  if limits.totalRows < (batches.map List.length).sum then return ← throw .rowLimit
  if limits.totalChildren < (batches.map childCount).sum then return ← throw .childLimit
  let schema ← emitSchemaFor parentNullable limits.ipc field
  let records ← batches.zipIdx.mapM fun (rows, index) => (emitRecord limits.ipc rows).mapError (.record index)
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

def serialize := serializeFor true

def Agrees (field : ListInt32.Field) (batches : List (List Row)) (decoded : Stream.Observed) : Prop :=
  decoded.field = field ∧ decoded.batches.map Stream.Batch.rows = batches ∧
    decoded.batches.map Stream.Batch.childCount = batches.map childCount

instance (field : ListInt32.Field) (batches : List (List Row)) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Certify the exact field, batch boundaries, nullable rows and child totals
using the existing checked LIST reader over the complete emitted carrier. -/
def emitFor (parentNullable : Bool) (limits : Stream.Limits) (field : ListInt32.Field) (batches : List (List Row)) :
    Except Error KBytes := do
  let wire ← serializeFor parentNullable limits field batches
  let decoded ← (Stream.readFor parentNullable limits wire).mapError .readback
  if Agrees field batches decoded then return wire else throw .readbackMismatch

def emit := emitFor true

end Silmaril.Formats.Arrow.ListInt32.Stream.Writer

module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Native V5 IPC emission for the fixed nullable Struct<Int32, Int32> profile. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream.Writer

namespace Wire

open MetadataWriter.Wire

def childField (child : StructInt32.Child) : Arrow.Field :=
  ⟨child.name, child.nullable, .int32⟩

def childSize (child : StructInt32.Child) : Nat :=
  let size := 53 + child.name.utf8ByteSize
  size + Arrow.Writer.padding size

def parentSize (name : String) : Nat :=
  let size := 61 + name.utf8ByteSize
  size + Arrow.Writer.padding size

/-- Relative to the parent fragment, the Struct table is at byte 40,
the child references are at 48 and 52, and the name starts at 56.
Each reference targets the table 12 bytes into its primitive fragment. -/
def parentFragment (field : StructInt32.Field) : KBytes :=
  let name := Arrow.Writer.emitWords 1 (field.name.toByteArray.data.toList.map UInt8.toNat)
  let children := parentSize field.name
  pad (words [halfwords 16 20, halfwords 4 8, halfwords 9 12, halfwords 0 16,
      16, 36, 1 + 13 * 256, 12, 12, halfwords 4 4, 4, 2,
      children + 12 - 48, children + childSize field.left + 12 - 52, name.len] ++ (name ++ KBytes.zeros 1))

/-- A top-level singleton Schema vector references the parent table,
followed by the two depth-first primitive child fragments. -/
def schema (field : StructInt32.Field) : KBytes :=
  messagePrefix 1 56 0 ++
    (words [halfwords 8 8, halfwords 0 4, 8, 4, 1, 20] ++
      (parentFragment field ++ fieldBytes (childField field.left) ++ fieldBytes (childField field.right)))

def schemaSize (field : StructInt32.Field) : Nat :=
  72 + parentSize field.name + childSize field.left + childSize field.right

end Wire

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | requiredChild (position row : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Hidden slots are emitted as null for optional children and zero for
required children. The reader ignores both kinds of hidden payload. -/
def childSlots (nullable : Bool) (project : Children → Option Int32) (rows : List Row) : List (Option Int32) :=
  rows.map fun row => row.elim (if nullable then none else some 0) project

def bodySize (rows : Nat) : Nat :=
  let bitmap := (rows + 7) / 8
  let words := 4 * rows
  3 * (bitmap + Arrow.Writer.padding bitmap) + 2 * (words + Arrow.Writer.padding words)

def checkRecord (ipc : Arrow.Limits) (rowCount : Nat) : Except RecordError Unit := do
  if ipc.fields < 3 then throw (.ipc (.limit .fields))
  if ipc.rows < rowCount then throw (.ipc (.limit .rows))
  if 2^63 ≤ rowCount then throw (.ipc (.malformed .flatbuffer))
  let size := bodySize rowCount
  if 2^63 ≤ size then throw (.ipc (.malformed .bodyLength))
  if ipc.bodyBytes < size then throw (.ipc (.limit .bodyBytes))
  if ipc.metadataBytes < 232 then throw (.ipc (.limit .metadataBytes))

def emitSchema (ipc : Arrow.Limits) (field : StructInt32.Field) : Except Error KBytes := do
  if ipc.fields < 3 then throw (.ipc (.limit .fields))
  let size := Wire.schemaSize field
  if 2^31 ≤ size then throw (.ipc (.malformed .metadataLength))
  if ipc.metadataBytes < size then throw (.ipc (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ Wire.schema field

/-- Pack the parent bitmap and the original two child positions using the
shared fixed-width encoder and aligned RecordBatch frame writer. -/
def emitRecord (ipc : Arrow.Limits) (field : StructInt32.Field) (rows : List Row) :
    Except RecordError KBytes := do
  checkRecord ipc rows.length
  rows.zipIdx.forM fun (row, index) => do
    if let some position := row.bind (missingRequired field) then
      throw (.requiredChild position index)
  let left := childSlots field.left.nullable Prod.fst rows
  let right := childSlots field.right.nullable Prod.snd rows
  let parts := Arrow.Writer.emitBitmap rows ::
    ((Arrow.Writer.ColumnValues.int32 left).emit ++ (Arrow.Writer.ColumnValues.int32 right).emit)
  let (buffers, body) := Arrow.Writer.packBuffers 0 parts
  let node := fun {α : Type} (values : List (Option α)) =>
    (⟨values.length, values.countP Option.isNone⟩ : FieldNode)
  let metadata : RecordBatch := ⟨rows.length, [node rows, node left, node right], buffers⟩
  (StreamWriter.emitFrame ipc ⟨.recordBatch metadata, body.len⟩ body).mapError .ipc

def serialize (limits : ObservationLimits) (field : StructInt32.Field) (batches : List (List Row)) :
    Except Error KBytes := do
  if limits.ipc.batches < batches.length then throw (.ipc (.limit .batches))
  (Body.checkBudget limits 3 (batches.map List.length).sum).mapError .ipc
  let schema ← emitSchema limits.ipc field
  let records ← batches.zipIdx.mapM fun (rows, index) => (emitRecord limits.ipc field rows).mapError (.record index)
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

def Agrees (field : StructInt32.Field) (batches : List (List Row)) (decoded : Stream.Observed) : Prop :=
  decoded.field = field ∧ decoded.batches.map Batch.rows = batches

instance (field : StructInt32.Field) (batches : List (List Row)) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Certify names, child flags, all logical rows and exact batch boundaries
with the independent checked reader through EOS. -/
def emit (limits : ObservationLimits) (field : StructInt32.Field) (batches : List (List Row)) :
    Except Error KBytes := do
  let wire ← serialize limits field batches
  let decoded ← (Stream.read limits wire).mapError .readback
  if Agrees field batches decoded then return wire else throw .readbackMismatch

end Silmaril.Formats.Arrow.StructInt32.Stream.Writer

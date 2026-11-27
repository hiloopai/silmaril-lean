module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Native V5 IPC emission for the fixed nullable Struct<Int32, Int32> profile. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream.Writer

open StructInt32 (RightWidth)
open Silmaril.Formats.Parquet

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

def rightFragment (width : RightWidth) (child : StructInt32.Child) : KBytes :=
  match width with
  | .int32 => fieldBytes (childField child)
  | .int64 => fieldFragment child.name child.nullable 2 (words [halfwords 8 12, halfwords 4 8, 8, 64, 1])

/-- A top-level singleton Schema vector references the parent table,
followed by the two depth-first primitive child fragments. -/
def schemaFor (width : RightWidth) (field : StructInt32.Field) : KBytes :=
  messagePrefix 1 56 0 ++
    (words [halfwords 8 8, halfwords 0 4, 8, 4, 1, 20] ++
      (parentFragment field ++ fieldBytes (childField field.left) ++ rightFragment width field.right))

abbrev schema := schemaFor .int32

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
def childSlotsFor {α β : Type} (zero : β) (nullable : Bool) (project : ChildrenFor α → Option β)
    (rows : List (RowFor α)) : List (Option β) :=
  rows.map fun row => row.elim (if nullable then none else some zero) project

abbrev childSlots := @childSlotsFor Int32 Int32 0

def zero : (width : RightWidth) → width.Value
  | .int32 => 0
  | .int64 => 0

/-- Reuse the existing raw signed codec and leave validity independent. -/
def rightParts : (width : RightWidth) → List (Option width.Value) → List KBytes
  | .int32, slots => (Arrow.Writer.ColumnValues.int32 slots).emit
  | .int64, slots =>
    let bytes := Plain.encodeInt64 (slots.map (·.getD 0))
    [Arrow.Writer.emitBitmap slots, Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat)]

def bodySize (rows : Nat) : Nat :=
  let bitmap := (rows + 7) / 8
  let words := 4 * rows
  3 * (bitmap + Arrow.Writer.padding bitmap) + 2 * (words + Arrow.Writer.padding words)

def bodySizeFor (width : RightWidth) (rows : Nat) : Nat :=
  match width with
  | .int32 => bodySize rows
  | .int64 =>
    let bitmap := (rows + 7) / 8
    let left := 4 * rows
    3 * (bitmap + Arrow.Writer.padding bitmap) + (left + Arrow.Writer.padding left) + 8 * rows

def checkRecordFor (width : RightWidth) (ipc : Arrow.Limits) (rowCount : Nat) : Except RecordError Unit := do
  if ipc.fields < 3 then throw (.ipc (.limit .fields))
  if ipc.rows < rowCount then throw (.ipc (.limit .rows))
  if 2^63 ≤ rowCount then throw (.ipc (.malformed .flatbuffer))
  let size := bodySizeFor width rowCount
  if 2^63 ≤ size then throw (.ipc (.malformed .bodyLength))
  if ipc.bodyBytes < size then throw (.ipc (.limit .bodyBytes))
  if ipc.metadataBytes < 232 then throw (.ipc (.limit .metadataBytes))

abbrev checkRecord := checkRecordFor .int32

def emitSchemaFor (width : RightWidth) (ipc : Arrow.Limits) (field : StructInt32.Field) : Except Error KBytes := do
  if ipc.fields < 3 then throw (.ipc (.limit .fields))
  let size := Wire.schemaSize field
  if 2^31 ≤ size then throw (.ipc (.malformed .metadataLength))
  if ipc.metadataBytes < size then throw (.ipc (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ Wire.schemaFor width field

abbrev emitSchema := emitSchemaFor .int32

/-- Pack the parent bitmap and the original two child positions using the
shared fixed-width encoder and aligned RecordBatch frame writer. -/
def emitRecordFor (width : RightWidth) (ipc : Arrow.Limits) (field : StructInt32.Field)
    (rows : List (RowFor width.Value)) :
    Except RecordError KBytes := do
  checkRecordFor width ipc rows.length
  rows.zipIdx.forM fun (row, index) => do
    if let some position := row.bind (missingRequiredFor field) then
      throw (.requiredChild position index)
  let left := childSlotsFor (0 : Int32) field.left.nullable Prod.fst rows
  let right := childSlotsFor (zero width) field.right.nullable Prod.snd rows
  let parts := Arrow.Writer.emitBitmap rows ::
    ((Arrow.Writer.ColumnValues.int32 left).emit ++ rightParts width right)
  let (buffers, body) := Arrow.Writer.packBuffers 0 parts
  let node := fun {α : Type} (values : List (Option α)) =>
    (⟨values.length, values.countP Option.isNone⟩ : FieldNode)
  let metadata : RecordBatch := ⟨rows.length, [node rows, node left, node right], buffers⟩
  (StreamWriter.emitFrame ipc ⟨.recordBatch metadata, body.len⟩ body).mapError .ipc

abbrev emitRecord := emitRecordFor .int32

def serializeFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field)
    (batches : List (List (RowFor width.Value))) :
    Except Error KBytes := do
  if limits.ipc.batches < batches.length then throw (.ipc (.limit .batches))
  (Body.checkBudget limits 3 (batches.map List.length).sum).mapError .ipc
  let schema ← emitSchemaFor width limits.ipc field
  let records ← batches.zipIdx.mapM fun (rows, index) => (emitRecordFor width limits.ipc field rows).mapError (.record index)
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

abbrev serialize := serializeFor .int32

def AgreesFor {α : Type} (field : StructInt32.Field) (batches : List (List (RowFor α)))
    (decoded : Stream.Observed α) : Prop :=
  decoded.field = field ∧ decoded.batches.map Batch.rows = batches

abbrev Agrees := @AgreesFor Int32

instance {α : Type} [DecidableEq α] (field : StructInt32.Field) (batches : List (List (RowFor α)))
    (decoded : Stream.Observed α) :
    Decidable (AgreesFor field batches decoded) := by
  unfold AgreesFor
  infer_instance

/-- Certify names, child flags, all logical rows and exact batch boundaries
with the independent checked reader through EOS. -/
def emitFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field)
    (batches : List (List (RowFor width.Value))) :
    Except Error KBytes := do
  let wire ← serializeFor width limits field batches
  let decoded ← (Stream.readFor width limits wire).mapError .readback
  letI : DecidableEq width.Value := by cases width <;> infer_instance
  if AgreesFor field batches decoded then return wire else throw .readbackMismatch

/-- The strict two-Int32 writer. -/
abbrev emit := emitFor .int32

end Silmaril.Formats.Arrow.StructInt32.Stream.Writer

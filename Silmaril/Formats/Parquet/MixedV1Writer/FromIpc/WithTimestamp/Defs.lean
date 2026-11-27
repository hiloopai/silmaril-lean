module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Defs
public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
public import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs

/-! Checked mixed INT32, STRING and modern INT64 TIMESTAMP Parquet PLAIN V1. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp

open Arrow.MixedFlat.Timestamp (Stream Field Batch Column)

structure Limits where
  readback : FlatProjection.Events.Limits := {}
  maxInputBytes : Nat := 256 * 1024 * 1024

inductive PageError where
  | primitive (cause : MixedV1Writer.Error)
  | timestamp (cause : Timestamp.FromIpc.Error)
  deriving DecidableEq, Repr

inductive Error where
  | inputByteLimit
  | source (cause : Arrow.MixedFlat.Timestamp.Error)
  | emptySchema
  | fieldLimit (maximum actual : Nat)
  | invalidName (position : Nat) (name : String)
  | duplicateName (position : Nat) (name : String)
  | annotation (position : Nat) (cause : Timestamp.FromIpc.Error)
  | groupLimit
  | totalRows
  | groupRowLimit (group maximum actual : Nat)
  | columnCount (group expected actual : Nat)
  | columnType (group position : Nat)
  | rowCount (group position expected actual : Nat)
  | requiredNull (group position : Nat)
  | page (group position : Nat) (cause : PageError)
  | chunkLimit (group position maximum actual : Nat)
  | fileLimit
  | footer (cause : FlatInt32Writer.Compact.Error)
  | extent
  | readback (cause : FlatProjection.Events.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def Limits.primitiveFile (limits : Limits) : Plain.ByteArray.File.Limits :=
  let primitive := limits.readback.primitive
  ⟨primitive.column.snapshot, primitive.column.column, primitive.column.maxFileBytes,
    primitive.maxFileRows, primitive.column.maxValueBytes⟩

def Limits.bytePage (limits : Limits) : PlainByteArrayV1Writer.Limits :=
  Plain.ByteArray.Utf8.FromIpc.Limits.page {file := limits.primitiveFile}

inductive LeafPlan where
  | int32 (field : Field)
  | utf8 (field : Field)
  | timestamp (binding : Arrow.TimestampBatch.Binding) (descriptor : Timestamp.Descriptor)

def LeafPlan.index : LeafPlan → FlatInt32Writer.Compact.TypedColumnIndex
  | .int32 field => ⟨1, ⟨field.name, field.nullable, ⟨0, 0⟩⟩⟩
  | .utf8 field => ⟨6, ⟨field.name, field.nullable, ⟨0, 0⟩⟩⟩
  | .timestamp field _ => ⟨2, ⟨field.name, field.nullable, ⟨0, 0⟩⟩⟩

def LeafPlan.write (leaf : LeafPlan) : FlatInt32Writer.Compact.Write Unit :=
  let index := leaf.index.column
  match leaf with
  | .int32 _ => FlatInt32Writer.Compact.leaf index
  | .utf8 _ => Plain.ByteArray.Utf8.FromIpc.stringLeaf index
  | .timestamp _ descriptor => Timestamp.FromIpc.Internal.leaf descriptor index

def planLeaf (position : Nat) (field : Field) : Except Error LeafPlan :=
  match field.kind with
  | .int32 => .ok (.int32 field)
  | .utf8 => .ok (.utf8 field)
  | .timestamp metadata => do
    let binding := field.timestampBinding metadata
    let descriptor ← (Timestamp.FromIpc.descriptor binding).mapError (.annotation position)
    return .timestamp binding descriptor

/-- Names must be nonempty, NUL-free and distinct in IPC field order. -/
def bindFields (nameBytes : Nat) : List (Field × Nat) → List String → Except Error (List LeafPlan)
  | [], _ => .ok []
  | (field, position) :: rest, names => do
    if field.name.isEmpty || field.name.contains (Char.ofNat 0) || field.name.utf8ByteSize > nameBytes then
      throw (.invalidName position field.name)
    if names.contains field.name then throw (.duplicateName position field.name)
    let leaf ← planLeaf position field
    let tail ← bindFields nameBytes rest (field.name :: names)
    return leaf :: tail

def ordinals (source : Stream) : Array Nat := Array.range source.fields.length

def checkBudget (limits : Limits) (source : Stream) : Except Error Unit := do
  let policy := limits.readback
  let compact := policy.primitive.column.snapshot.footer.compact
  let width := source.fields.length
  if width = 0 then throw .emptySchema
  let fieldCap := min policy.primitive.maxFields (compact.maxCollectionSize - 1)
  if width > fieldCap then throw (.fieldLimit fieldCap width)
  if source.batches.length > min policy.maxGroups compact.maxCollectionSize then throw .groupLimit
  let rows := (source.batches.map Batch.rowCount).sum
  if rows > policy.primitive.maxFileRows || rows ≥ 2^63 then throw .totalRows

inductive PagePlan where
  | int32 (input : PlainV1Writer.Input) (size : Nat)
  | utf8 (input : PlainByteArrayV1Writer.Input) (size : Nat)
  | timestamp (plan : Timestamp.FromIpc.Internal.PagePlan)

def PagePlan.size : PagePlan → Nat
  | .int32 _ size | .utf8 _ size => size
  | .timestamp plan => plan.size

def PagePlan.emit (limits : Limits) (optional : Bool) : PagePlan → Except PageError Bytes
  | .int32 input _ =>
    (PlainV1Writer.emit limits.bytePage.page input).map (·.wire) |>.mapError (.primitive ∘ .intPage)
  | .utf8 input _ =>
    (PlainByteArrayV1Writer.emit limits.bytePage input).map (·.wire) |>.mapError (.primitive ∘ .bytePage)
  | .timestamp plan => (Timestamp.FromIpc.Internal.emitPage optional plan).mapError .timestamp

def columnLength : Column → Nat
  | .int32 values => values.length
  | .utf8 values => values.length
  | .timestamp counts => counts.length

def planPage (limits : Limits) (group position : Nat) (leaf : LeafPlan) (column : Column) :
    Except Error PagePlan := do
  match leaf, column with
  | .int32 field, .int32 values =>
    let input ← (FromIpc.prepareInt field.nullable group values).mapError (fun _ => .requiredNull group position)
    let size ← (FlatInt32Writer.measuredPage limits.bytePage.page input).mapError
      (fun _ => .page group position (.primitive .intBudget))
    return .int32 input size
  | .utf8 field, .utf8 values =>
    let raw := values.map (Option.map Plain.ByteArray.Utf8.FromIpc.Internal.textBytes)
    let input ← (FromIpc.prepareBytes field.nullable group raw).mapError (fun _ => .requiredNull group position)
    let size ← (MixedV1Writer.measuredBytePage limits.bytePage input).mapError (.page group position ∘ .primitive)
    return .utf8 input size
  | .timestamp field _, .timestamp counts =>
    let slots : Arrow.TimestampBatch.Column field := counts.map (Option.map fun ticks => ⟨ticks⟩)
    let plan ← (Timestamp.FromIpc.Internal.planPage limits.readback.timestamp field slots group).mapError
      (fun cause => match cause with
        | .requiredNull _ => .requiredNull group position
        | other => .page group position (.timestamp other))
    return .timestamp plan
  | _, _ => throw (.columnType group position)

structure ColumnPlan where
  index : FlatInt32Writer.Compact.TypedColumnIndex
  page : PagePlan

structure GroupPlan where
  rows : Nat
  columns : List ColumnPlan

def planGroup (limits : Limits) (leaves : List LeafPlan) (batch : Batch) (group : Nat) :
    Except Error GroupPlan := do
  if batch.columns.length ≠ leaves.length then throw (.columnCount group leaves.length batch.columns.length)
  let policy := limits.readback.primitive.column.column
  if policy.maxRows < batch.rowCount then throw (.groupRowLimit group policy.maxRows batch.rowCount)
  let columns ← (leaves.zip batch.columns).zipIdx.mapM fun ((leaf, column), position) => do
    if columnLength column ≠ batch.rowCount then
      throw (.rowCount group position batch.rowCount (columnLength column))
    let page ← planPage limits group position leaf column
    if leaf.index.physical ≠ 2 && page.size > policy.maxChunkBytes then
      throw (.chunkLimit group position policy.maxChunkBytes page.size)
    return ⟨leaf.index, page⟩
  return ⟨batch.rowCount, columns⟩

/-- Place the measured chunks in the same order as their schema leaves. -/
def placeColumns : Nat → List ColumnPlan → Nat × List FlatInt32Writer.Compact.TypedColumnIndex
  | offset, [] => (offset, [])
  | offset, column :: rest =>
    let next := offset + column.page.size
    let (stop, tail) := placeColumns next rest
    (stop, { column.index with column.span := ⟨offset, next⟩ } :: tail)

def placeGroups : Nat → List GroupPlan → Nat × List (Nat × List FlatInt32Writer.Compact.TypedColumnIndex)
  | offset, [] => (offset, [])
  | offset, group :: rest =>
    let (next, columns) := placeColumns offset group.columns
    let (stop, tail) := placeGroups next rest
    (stop, (group.rows, columns) :: tail)

structure Plan where
  groups : List GroupPlan
  dataStop : Nat
  footer : Bytes

def fileLimit (limits : Limits) : Nat := min limits.primitiveFile.maxFileBytes (2^63 - 1)

def footerLimit (limits : Limits) (dataStop : Nat) : Nat :=
  min (min limits.primitiveFile.snapshot.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - dataStop - 8)

/-- Check the measured data and bounded footer before allocating page bodies. -/
def preflight (limits : Limits) (source : Stream) : Except Error Plan := do
  checkBudget limits source
  let leaves ← bindFields limits.primitiveFile.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx []
  let groups ← source.batches.zipIdx.mapM fun (batch, group) => planGroup limits leaves batch group
  let (dataStop, indices) := placeGroups 4 groups
  if dataStop + 8 > fileLimit limits then .error .fileLimit
  else
    let cap := footerLimit limits dataStop
    let footer ← (FlatInt32Writer.Compact.encodeGroupsTyped cap (leaves.map LeafPlan.write) indices).mapError .footer
    if footer.length > cap then .error .extent
    else .ok ⟨groups, dataStop, footer⟩

def emitGroup (limits : Limits) (group : GroupPlan) (ordinal : Nat) : Except Error (List Bytes) :=
  group.columns.zipIdx.mapM fun (column, position) => do
    let wire ← (column.page.emit limits column.index.column.optional).mapError (.page ordinal position)
    if wire.length ≠ column.page.size then throw .extent
    return wire

def assemble (plan : Plan) (groups : List (List Bytes)) : Bytes :=
  let data := Bytes.ofList (groups.flatten.flatMap Bytes.toList)
  let prefixBytes := (Footer.magic.append data).append plan.footer
  (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 plan.footer.length))).append Footer.magic

def serialize (limits : Limits) (source : Stream) : Except Error Bytes := do
  let plan ← preflight limits source
  let groups ← plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup limits group ordinal
  if 4 + (groups.flatten.map Bytes.length).sum ≠ plan.dataStop then throw .extent
  return assemble plan groups

def FooterMatches (checked : FlatProjection.Events.Checked) (source : Stream) : Prop :=
  checked.snapshot.metadata.schema.length = source.fields.length + 1 ∧
    checked.snapshot.metadata.rowGroups.map (·.numRows) = source.batches.map (Int.ofNat ∘ Batch.rowCount) ∧
    checked.snapshot.metadata.numRows = Int.ofNat (source.batches.map Batch.rowCount).sum

instance (checked : FlatProjection.Events.Checked) (source : Stream) : Decidable (FooterMatches checked source) := by
  unfold FooterMatches
  infer_instance

/-- Certify every emitted field and original batch through the existing Parquet Events reader. -/
def certify (limits : Limits) (source : Stream) (wire : Bytes) : Except Error Unit := do
  let checked ← (FlatProjection.Events.openFile limits.readback wire (ordinals source)).mapError .readback
  let trace := checked.trace limits.readback
  match trace.termination with
  | .readError cause | .closeError cause => .error (.readback cause)
  | .closed => .error .readbackMismatch
  | .eos =>
    if FooterMatches checked source ∧ FlatProjection.Events.ToIpc.observation trace = source then .ok ()
    else .error .readbackMismatch

/-- Every explicit IPC batch gets one framed group. Schema-only streams have zero groups. -/
def emit (limits : Limits) (source : Stream) : Except Error Bytes := do
  let wire ← serialize limits source
  certify limits source wire
  return wire

/-- Exhaust the exact original IPC before applying any Parquet writer admission. -/
def convert (ipc : Arrow.ObservationLimits) (limits : Limits) (input : KBytes) : Except Error Bytes :=
  if limits.maxInputBytes < input.len then .error .inputByteLimit
  else do
    let source ← (Arrow.MixedFlat.Timestamp.read ipc input).mapError .source
    emit limits source

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp

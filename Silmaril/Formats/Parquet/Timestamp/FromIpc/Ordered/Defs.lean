module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Defs

/-! Native ordered flat INT64 TIMESTAMP PLAIN V1 from a checked Arrow IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered

open FlatInt32Writer
open Arrow.TimestampStream.Ordered (Stream Batch Column Field)

structure Limits where
  writer : FromIpc.Limits := {}
  maxFields : Nat := 64

inductive Error where
  | inputByteLimit
  | source (cause : Arrow.TimestampStream.Ordered.Error)
  | emptySchema
  | fieldLimit (maximum actual : Nat)
  | invalidName (position : Nat) (name : String)
  | duplicateName (position : Nat) (name : String)
  | annotation (position : Nat) (cause : FromIpc.Error)
  | groupLimit
  | totalRows
  | columnCount (group expected actual : Nat)
  | rowCount (group position expected actual : Nat)
  | page (group position : Nat) (cause : FromIpc.Error)
  | fileLimit
  | footer (cause : Compact.Error)
  | extent
  | readback (cause : Leaf.Projection.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def readbackLimits (limits : Limits) : Leaf.Projection.Limits :=
  { input :=
      { snapshot := limits.writer.snapshot
        leaf := limits.writer.leaf
        maxFileBytes := limits.writer.maxFileBytes
        maxGroups := limits.writer.maxGroups
        maxTotalRows := limits.writer.maxTotalRows }
    maxFields := limits.maxFields }

def ordinals (source : Stream) : Array Nat :=
  Array.ofFn fun (i : Fin source.fields.length) => i.val + 1

structure LeafPlan where
  field : Field
  descriptor : Timestamp.Descriptor

def LeafPlan.index (leaf : LeafPlan) : Compact.ColumnIndex :=
  ⟨leaf.field.name, leaf.field.nullable, ⟨0, 0⟩⟩

/-- Flat names are nonempty UTF-8 strings without a NUL, distinct in schema order. -/
def bindFields (nameBytes : Nat) : List (Field × Nat) → List String → Except Error (List LeafPlan)
  | [], _ => .ok []
  | (field, position) :: rest, names => do
    if field.name.isEmpty || field.name.contains (Char.ofNat 0) || field.name.utf8ByteSize > nameBytes then
      throw (.invalidName position field.name)
    if names.contains field.name then throw (.duplicateName position field.name)
    let descriptor ← (FromIpc.descriptor field).mapError (.annotation position)
    let tail ← bindFields nameBytes rest (field.name :: names)
    return ⟨field, descriptor⟩ :: tail

def checkBudget (limits : Limits) (source : Stream) : Except Error Unit := do
  let width := source.fields.length
  let compact := limits.writer.snapshot.footer.compact
  if width = 0 then throw .emptySchema
  let fieldCap := min limits.maxFields (compact.maxCollectionSize - 1)
  if width > fieldCap then throw (.fieldLimit fieldCap width)
  if source.batches.length > min limits.writer.maxGroups compact.maxCollectionSize then throw .groupLimit
  let rows := (source.batches.map Batch.rowCount).sum
  if rows > limits.writer.maxTotalRows || rows ≥ 2^63 then throw .totalRows

structure ColumnPlan where
  index : Compact.ColumnIndex
  page : FromIpc.Internal.PagePlan

structure GroupPlan where
  rows : Nat
  columns : List ColumnPlan

def planColumn (limits : Leaf.Limits) (group rows : Nat) (leaf : LeafPlan) (column : Column)
    (position : Nat) : Except Error ColumnPlan := do
  if column.length ≠ rows then throw (.rowCount group position rows column.length)
  let slots : Arrow.TimestampBatch.Column leaf.field := column.map (Option.map fun ticks => ⟨ticks⟩)
  let page ← (FromIpc.Internal.planPage limits leaf.field slots group).mapError (.page group position)
  return ⟨leaf.index, page⟩

def planGroup (limits : Leaf.Limits) (leaves : List LeafPlan) (batch : Batch) (group : Nat) :
    Except Error GroupPlan := do
  if batch.columns.length ≠ leaves.length then throw (.columnCount group leaves.length batch.columns.length)
  let columns ← (leaves.zip batch.columns).zipIdx.mapM fun ((leaf, column), position) =>
    planColumn limits group batch.rowCount leaf column position
  return ⟨batch.rowCount, columns⟩

/-- Place each measured page once, in its original field position. -/
def placeColumns : Nat → List ColumnPlan → Nat × List Compact.ColumnIndex
  | offset, [] => (offset, [])
  | offset, column :: rest =>
    let next := offset + column.page.size
    let (stop, tail) := placeColumns next rest
    (stop, { column.index with span := ⟨offset, next⟩ } :: tail)

def placeGroups : Nat → List GroupPlan → Nat × List (Nat × List Compact.ColumnIndex)
  | offset, [] => (offset, [])
  | offset, group :: rest =>
    let (next, columns) := placeColumns offset group.columns
    let (stop, tail) := placeGroups next rest
    (stop, (group.rows, columns) :: tail)

structure Plan where
  groups : List GroupPlan
  dataStop : Nat
  footer : Bytes

def fileLimit (limits : Limits) : Nat :=
  min limits.writer.maxFileBytes (2^63 - 1)

def footerLimit (limits : Limits) (dataStop : Nat) : Nat :=
  min (min limits.writer.snapshot.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - dataStop - 8)

/-- Bound the footer and measured file before allocating page bodies. -/
def preflight (limits : Limits) (source : Stream) : Except Error Plan := do
  checkBudget limits source
  let leaves ← bindFields limits.writer.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx []
  let groups ← source.batches.zipIdx.mapM fun (batch, group) => planGroup limits.writer.leaf leaves batch group
  let (dataStop, indices) := placeGroups 4 groups
  if dataStop + 8 > fileLimit limits then .error .fileLimit
  else
    let footerCap := footerLimit limits dataStop
    let writers := leaves.map fun leaf => FromIpc.Internal.leaf leaf.descriptor leaf.index
    let footer ← (Compact.encodeGroupsWriting 2 footerCap writers indices).mapError .footer
    if footer.length > footerCap then .error .extent
    else .ok ⟨groups, dataStop, footer⟩

def emitGroup (group : GroupPlan) (ordinal : Nat) : Except Error (List Bytes) :=
  group.columns.zipIdx.mapM fun (column, position) =>
    (FromIpc.Internal.emitPage column.index.optional column.page).mapError (.page ordinal position)

def assemble (plan : Plan) (groups : List (List Bytes)) : Bytes :=
  let data := Bytes.ofList (groups.flatten.flatMap Bytes.toList)
  let prefixBytes := (Footer.magic.append data).append plan.footer
  (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 plan.footer.length))).append Footer.magic

def serialize (limits : Limits) (source : Stream) : Except Error Bytes := do
  let plan ← preflight limits source
  let groups ← plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup group ordinal
  if 4 + (groups.flatten.map Bytes.length).sum ≠ plan.dataStop then throw .extent
  return assemble plan groups

def FooterMatches (checked : Leaf.Projection.Checked) (source : Stream) : Prop :=
  checked.snapshot.metadata.schema.length = source.fields.length + 1 ∧
    checked.snapshot.metadata.rowGroups.map (·.numRows) = source.batches.map (Int.ofNat ∘ Batch.rowCount) ∧
    checked.snapshot.metadata.numRows = Int.ofNat (source.batches.map Batch.rowCount).sum

instance (checked : Leaf.Projection.Checked) (source : Stream) : Decidable (FooterMatches checked source) := by
  unfold FooterMatches
  infer_instance

/-- Certify every field and row group through the existing ordered Parquet Events reader. -/
def certify (limits : Limits) (source : Stream) (wire : Bytes) : Except Error Unit := do
  let policy := readbackLimits limits
  let checked ← (Leaf.Projection.openFile policy wire (ordinals source)).mapError .readback
  let trace := checked.trace policy
  match trace.termination with
  | .readError cause | .closeError cause => .error (.readback cause)
  | .closed => .error .readbackMismatch
  | .eos =>
    if FooterMatches checked source ∧ Leaf.Projection.ToIpc.observation trace = source then .ok ()
    else .error .readbackMismatch

/-- Schema-only input has zero groups. Every explicit batch, even empty, has one framed group. -/
def emit (limits : Limits) (source : Stream) : Except Error Bytes := do
  let wire ← serialize limits source
  certify limits source wire
  return wire

/-- Consume the exact original IPC stream before invoking writer validation. -/
def convert (ipc : Arrow.Limits) (limits : Limits) (input : KBytes) : Except Error Bytes :=
  if limits.writer.maxInputBytes < input.len then .error .inputByteLimit
  else do
    let source ← (Arrow.TimestampStream.Ordered.read ipc input).mapError .source
    emit limits source

end Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered

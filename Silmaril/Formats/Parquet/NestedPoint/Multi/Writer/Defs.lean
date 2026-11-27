module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
public import Silmaril.Formats.Parquet.ListFile.Writer.Defs

/-! Write one unannotated optional group with required INT32 and optional INT64 leaves. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.Writer

open Arrow.StructInt32 (Field)
open NestedPoint (Row)
open NestedPoint.Multi (Kind)

structure Input where
  name : String
  leftName : String
  rightName : String
  groups : List (List Row)

def Input.field (input : Input) : Field :=
  ⟨input.name, ⟨input.leftName, false⟩, ⟨input.rightName, true⟩⟩

structure Limits where
  readback : ToIpc.SourceLimits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxGroups : Nat := 4096
  maxTotalRows : Nat := 1024 * 1024

def Limits.fileLimit (limits : Limits) : Nat :=
  min limits.maxFileBytes (2^63 - 1)

namespace PageEncoding

def levelPair : Row → Nat × Nat
  | none => (0, 0)
  | some (_, none) => (1, 1)
  | some (_, some _) => (1, 2)

def levels (kind : Kind) (rows : List Row) : List Nat :=
  match kind with
  | .signed => rows.map (Prod.fst ∘ levelPair)
  | .wide => rows.map (Prod.snd ∘ levelPair)

def values : (kind : Kind) → List Row → List kind.Value
  | .signed, rows => rows.filterMap (Option.map Prod.fst)
  | .wide, rows => rows.filterMap (fun row => row.bind Prod.snd)

def valueBytes : Kind → Nat
  | .signed => 4
  | .wide => 8

def plain : (kind : Kind) → List kind.Value → Bytes
  | .signed => Plain.encodeInt32
  | .wide => Plain.encodeInt64

def body (kind : Kind) (rows : List Row) : Bytes :=
  let definitions := ListFile.Writer.PageEncoding.runs kind.child.width (levels kind rows)
  (ListFile.Writer.PageEncoding.lengthPrefixed definitions).append (plain kind (values kind rows))

/-- For either level width, a singleton run consists of two octets. -/
def bodySize (kind : Kind) (rows : List Row) : Nat :=
  4 + 2 * rows.length + valueBytes kind * (values kind rows).length

def header (kind : Kind) (rows : List Row) : Page.Header :=
  let size := bodySize kind rows
  ⟨size, size, none, .dataV1 ⟨rows.length, 0, 3, 3⟩⟩

inductive Error where
  | budget
  | headerInteger
  | headerLimit
  | chunkLimit
  deriving DecidableEq, Repr

/-- Check header, level, row and chunk bounds before materializing a body. -/
def measure (limits : Multi.Limits) (kind : Kind) (rows : List Row) : Except Error Bytes := do
  let presence := limits.leaf.presence
  let framing := limits.leaf.framing
  let size := (header kind rows).compressedSize
  if limits.maxRows < rows.length || presence.levels.values < rows.length ||
      presence.levels.bytes < 2 * rows.length || presence.maxBodyBytes < size ||
      framing.maxPages = 0 then
    return ← throw .budget
  let some bytes := PlainV1Writer.encodeHeader rows.length size | throw .headerInteger
  if framing.maxHeaderBytes < bytes.length then return ← throw .headerLimit
  if limits.maxChunkBytes < bytes.length + size then return ← throw .chunkLimit
  return bytes

end PageEncoding

structure LeafPlan where
  span : Footer.Span
  header : Bytes

def LeafPlan.size (leaf : LeafPlan) : Nat := leaf.span.stop - leaf.span.start

structure GroupPlan where
  rows : List Row
  left : LeafPlan
  right : LeafPlan

def GroupPlan.size (group : GroupPlan) : Nat := group.left.size + group.right.size

def GroupPlan.rowCount (group : GroupPlan) : Nat := group.rows.length

def Input.path (input : Input) (kind : Kind) : List String :=
  [input.name, match kind with | .signed => input.leftName | .wide => input.rightName]

def LeafPlan.metadata (leaf : LeafPlan) (input : Input) (kind : Kind) (rows : Nat) : Footer.ColumnChunk :=
  ⟨0, ⟨kind.physical, [0, 3], input.path kind, 0, rows, leaf.size, leaf.size, leaf.span.start,
    none, none, none, none⟩, none, none, none, none⟩

def metadata (input : Input) (groups : List GroupPlan) : Footer.Metadata :=
  let schema : List Footer.SchemaElement := [
    FlatInt32Writer.Compact.schemaRoot 1,
    ⟨none, none, some .optional, input.name, some 2⟩,
    ⟨some .int32, none, some .required, input.leftName, none⟩,
    ⟨some .int64, none, some .optional, input.rightName, none⟩]
  let rowGroups : List Footer.RowGroup := groups.map fun group =>
    ⟨[group.left.metadata input .signed group.rowCount, group.right.metadata input .wide group.rowCount],
      group.size, group.rowCount, none, none⟩
  ⟨1, schema, (groups.map GroupPlan.rowCount).sum, rowGroups, none⟩

namespace Compact

open FlatInt32Writer.Compact (Write field integer octet text listHeader root)

def parent (name : String) : Write Unit := do
  field 3 5
  integer .i32 1
  field 1 8
  text name
  field 1 5
  integer .i32 2
  octet 0

def leaf (physical : Int) (optional : Bool) (name : String) : Write Unit := do
  field 1 5
  integer .i32 physical
  field 2 5
  integer .i32 (if optional then 1 else 0)
  field 1 8
  text name
  octet 0

def chunk (physical : Int) (rows : Nat) (parentName name : String) (plan : LeafPlan) : Write Unit := do
  field 2 6
  integer .i64 0
  field 1 12
  field 1 5
  integer .i32 physical
  field 1 9
  listHeader 5 2
  integer .i32 0
  integer .i32 3
  field 1 9
  listHeader 8 2
  text parentName
  text name
  field 1 5
  integer .i32 0
  field 1 6
  integer .i64 rows
  field 1 6
  integer .i64 plan.size
  field 1 6
  integer .i64 plan.size
  field 2 6
  integer .i64 plan.span.start
  octet 0
  octet 0

def footer (input : Input) (groups : List GroupPlan) : Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 4
  root 1
  parent input.name
  leaf 1 false input.leftName
  leaf 2 true input.rightName
  field 1 6
  integer .i64 (groups.map GroupPlan.rowCount).sum
  field 1 9
  listHeader 12 groups.length
  for group in groups do
    field 1 9
    listHeader 12 2
    chunk 1 group.rowCount input.name input.leftName group.left
    chunk 2 group.rowCount input.name input.rightName group.right
    field 1 6
    integer .i64 group.size
    field 1 6
    integer .i64 group.rowCount
    octet 0
  octet 0

def encode (limit : Nat) (input : Input) (groups : List GroupPlan) : Except FlatInt32Writer.Compact.Error Bytes :=
  ((footer input groups).run ⟨limit, .empty⟩).map (·.2.bytes)

end Compact

inductive Error where
  | name (position : Nat) (value : String)
  | duplicateChild (name : String)
  | schemaBudget
  | groupLimit
  | totalRows
  | fileLimit
  | measure (group column : Nat) (cause : PageEncoding.Error)
  | footer (cause : FlatInt32Writer.Compact.Error)
  | layout
  | openReadback (cause : ToIpc.OpenError)
  | groupReadback (group : Nat) (cause : Multi.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def checkInput (limits : Limits) (input : Input) : Except Error Unit := do
  let names := [input.name, input.leftName, input.rightName]
  for (name, position) in names.zipIdx do
    if name.isEmpty || name.contains (Char.ofNat 0) then throw (.name position name)
  if input.leftName = input.rightName then throw (.duplicateChild input.leftName)
  let compact := limits.readback.snapshot.footer.compact
  if compact.maxCollectionSize < 4 || compact.maxBinaryBytes < 6 ||
      names.any (fun name => compact.maxBinaryBytes < name.utf8ByteSize) then
    throw .schemaBudget
  if limits.maxGroups < input.groups.length || compact.maxCollectionSize < input.groups.length then
    throw .groupLimit
  let rows := (input.groups.map List.length).sum
  if limits.maxTotalRows < rows || 2^63 ≤ rows then throw .totalRows

def place (limits : Limits) : Nat → Nat → List (List Row) → Except Error (Nat × List GroupPlan)
  | offset, _, [] => .ok (offset, [])
  | offset, ordinal, rows :: rest => do
    let left ← (PageEncoding.measure limits.readback.group .signed rows).mapError (.measure ordinal 0)
    let right ← (PageEncoding.measure limits.readback.group .wide rows).mapError (.measure ordinal 1)
    let middle := offset + left.length + PageEncoding.bodySize .signed rows
    let stop := middle + right.length + PageEncoding.bodySize .wide rows
    if limits.fileLimit < stop + 8 then return ← throw .fileLimit
    let (dataStop, tail) ← place limits stop (ordinal + 1) rest
    return (dataStop, ⟨rows, ⟨⟨offset, middle⟩, left⟩, ⟨⟨middle, stop⟩, right⟩⟩ :: tail)

def encodeGroup (group : GroupPlan) : Except Error (List Bytes) := do
  let left := group.left.header.append (PageEncoding.body .signed group.rows)
  let right := group.right.header.append (PageEncoding.body .wide group.rows)
  if left.length ≠ group.left.size || right.length ≠ group.right.size then return ← throw .layout
  return [left, right]

structure Encoded where
  bytes : Bytes
  footer : Footer.Span
  groups : List GroupPlan

/-- Plan every chunk and the bounded footer before allocating any page body. -/
def serialize (limits : Limits) (input : Input) : Except Error Encoded := do
  checkInput limits input
  let (dataStop, groups) ← place limits 4 0 input.groups
  if limits.fileLimit < dataStop + 8 then return ← throw .fileLimit
  let footerLimit := min (min limits.readback.snapshot.footer.maxFooterBytes
      limits.readback.group.leaf.footer.maxFooterBytes) (min (2^32 - 1) (limits.fileLimit - dataStop - 8))
  let footer ← (Compact.encode footerLimit input groups).mapError .footer
  let pages ← groups.mapM encodeGroup
  let payload := Bytes.ofList (pages.flatten.flatMap Bytes.toList)
  if 4 + payload.length ≠ dataStop || footerLimit < footer.length then return ← throw .layout
  let bytes := (((Footer.magic.append payload).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨dataStop, dataStop + footer.length⟩, groups⟩

def certify (limits : Limits) (input : Input) (output : Encoded) : Except Error Unit := do
  if Footer.readFooter limits.readback.snapshot.footer output.bytes ≠
      .ok (output.footer, metadata input output.groups) then return ← throw .layout
  let checked ← (ToIpc.openFile limits.readback output.bytes).mapError .openReadback
  if ¬ (checked.field = input.field ∧ checked.snapshot.groupCount = input.groups.length) then
    return ← throw .readbackMismatch
  let decoded ← (List.range checked.snapshot.groupCount).mapM fun index =>
    (Multi.read limits.readback.group checked.snapshot index).mapError (.groupReadback index)
  if decoded ≠ input.groups then throw .readbackMismatch

/-- Publish the native file only after exact footer and group certification. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded := do
  let output ← serialize limits input
  certify limits input output
  return output

structure Readback (limits : Limits) (input : Input) (output : Encoded) : Prop where
  plans : output.groups.map GroupPlan.rows = input.groups
  footer : Footer.readFooter limits.readback.snapshot.footer output.bytes =
    .ok (output.footer, metadata input output.groups)
  groups : ∃ checked,
    ToIpc.openFile limits.readback output.bytes = .ok checked ∧
    ToIpc.OpenWire limits.readback output.bytes checked ∧
    checked.field = input.field ∧ checked.snapshot.groupCount = input.groups.length ∧
    (List.range checked.snapshot.groupCount).mapM (Multi.read limits.readback.group checked.snapshot) =
      .ok input.groups ∧
    List.Forall₂ (ToIpc.GroupWire limits.readback.group checked.snapshot)
      (List.range checked.snapshot.groupCount) input.groups
  events : ToIpc.readAll limits.readback output.bytes = .ok ⟨ToIpc.schema input.field,
    ⟨input.groups.map (Silmaril.Relational.AlignedColumns.ofRows ∘ ToIpc.rowsFor input.field), .eos⟩⟩

end Silmaril.Formats.Parquet.NestedPoint.Multi.Writer

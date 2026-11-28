module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs

/-! Bind a signed path of the checked tree to the shared physical
scanner. The path carries all original Struct and LIST sites. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree

open RecursiveSchema.Chunk (Address)

@[expose] public section

def Ancestor.wrap (child : ListPath.Shape) : Ancestor → ListPath.Shape
  | .struct site => .struct site child
  | .list site wrapper => .list ⟨site, wrapper⟩ child

def LeafPath.shape (path : LeafPath) : ListPath.Shape :=
  path.ancestors.foldr (fun ancestor child => ancestor.wrap child) (.signed path.site path.kind)

/-- The legacy LIST-led logical plan is available when the first site
is an original LIST. -/
def LeafPath.listPlan (path : LeafPath) : Option ListPath.Plan :=
  match path.shape with
  | .list outer child => some ⟨outer, child⟩
  | _ => none

inductive LeafError where
  | leaf (column : Nat)
  | representation (column : Nat)
  | group (ordinal : Nat)
  | columns (group expected actual : Nat)
  | column (address : Address) (cause : ListPath.Chunk.BindCause)
  | chunk (cause : ListPath.Chunk.Error)
  deriving DecidableEq, Repr

structure LeafBinding {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) (group column : Nat) where
  leaf : LeafPlan
  plan : ListPath.Shape
  rowGroup : Footer.RowGroup
  chunk : Footer.ColumnChunk
  span : Footer.Span
  selected : compiled.leaves[column]? = some leaf
  projected : plan = leaf.path.shape
  groupAt : snapshot.groupAt group = some rowGroup
  columns : rowGroup.columns.length = compiled.leaves.size
  columnAt : rowGroup.columns[column]? = some chunk
  path : chunk.metadata.pathInSchema = leaf.path.site.location.path
  physical : chunk.metadata.physicalType = leaf.path.kind.physical
  codec : ListPath.Chunk.Codec
  originalCodec : ListPath.Chunk.Codec.ofId chunk.metadata.codec = some codec
  encodings : ListPath.Chunk.ColumnEncoding chunk.metadata
  indexOffset : chunk.metadata.indexPageOffset = none
  unindexed : Repeated.Chunk.Unindexed chunk
  counts : 0 ≤ chunk.metadata.numValues ∧ 0 ≤ rowGroup.numRows
  originalSpan : Page.columnSpan snapshot.footer.start chunk.metadata = some span

def LeafBinding.carrier {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} (bound : LeafBinding compiled group column) :
    ListPath.Chunk.Carrier ListPath.Shape :=
  ⟨bound.plan, snapshot.bytes, bound.span, ⟨group, column, bound.leaf.path.site.location.path⟩,
    bound.chunk.metadata.numValues.toNat, bound.rowGroup.numRows.toNat, bound.chunk.metadata.totalCompressedSize,
    bound.chunk.metadata.totalUncompressedSize, bound.codec, bound.chunk.metadata⟩

end

private def lookup {α : Type} (value : Option α) (error : LeafError) :
    Except LeafError {found // value = some found} :=
  match value with
  | none => .error error
  | some found => .ok ⟨found, rfl⟩

private def guard (condition : Prop) [Decidable condition] (error : LeafError) : Except LeafError (PLift condition) :=
  if valid : condition then .ok ⟨valid⟩ else .error error

public def bindLeaf {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled limits snapshot) (group column : Nat) : Except LeafError (LeafBinding compiled group column) := do
  let ⟨leaf, selected⟩ ← lookup compiled.leaves[column]? (.leaf column)
  let plan := leaf.path.shape
  let ⟨rowGroup, groupAt⟩ ← lookup (snapshot.groupAt group) (.group group)
  let width := compiled.leaves.size
  let ⟨columns⟩ ← guard (rowGroup.columns.length = width) (.columns group width rowGroup.columns.length)
  let fail := LeafError.column ⟨group, column, leaf.path.site.location.path⟩
  let ⟨chunk, columnAt⟩ ← lookup rowGroup.columns[column]? (fail (.columns width))
  let metadata := chunk.metadata
  let ⟨⟨path, physical⟩⟩ ← guard (metadata.pathInSchema = leaf.path.site.location.path ∧
    metadata.physicalType = leaf.path.kind.physical) (fail .association)
  let ⟨codec, originalCodec⟩ ← lookup (ListPath.Chunk.Codec.ofId metadata.codec) (fail (.codec metadata.codec))
  let encodings ← ListPath.Chunk.bindEncoding metadata fail
  let ⟨indexOffset⟩ ← guard (metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← guard (Repeated.Chunk.Unindexed chunk) (fail .pageIndex)
  let ⟨counts⟩ ← guard (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨leaf, plan, rowGroup, chunk, span, selected, rfl, groupAt, columns, columnAt,
    path, physical, codec, originalCodec, encodings, indexOffset, unindexed, counts, originalSpan⟩

@[expose] public section

def LeafBinding.read {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} (bound : LeafBinding compiled group column)
    (caps : ListPath.Chunk.Limits) : Except ListPath.Chunk.Error ListPath.Chunk.Observation :=
  ListPath.Chunk.readCarrier caps bound.carrier bound.encodings (fun _ => .ok ())

def readLeaf {limits : Snapshot.Limits} {snapshot : Snapshot.Checked} (compiled : Compiled limits snapshot)
    (caps : ListPath.Chunk.Limits) (group column : Nat) : Except LeafError ListPath.Chunk.Observation := do
  let bound ← bindLeaf compiled group column
  (bound.read caps).mapError .chunk

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree

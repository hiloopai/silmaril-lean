module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs

/-! Native recursive signed Parquet files. A checked schema-only inverse
supplies the original positional leaf plans used for every group. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer

open Arrow.RecursiveSchema.Batch.Rows (Cell Row Observation)

@[expose] public section

structure Limits where
  schema : Schema.Limits := {}
  rows : Rows.Limits := {}
  maxGroups : Nat := 4096
  maxTotalRows : Nat := 1024 * 1024
  maxTotalSlots : Nat := 8 * 1024 * 1024
  maxTotalPages : Nat := 65536

structure Group where
  data : Observation
  /-- Optional per-leaf counts in physical preorder. The canonical empty
  group uses [0] for each leaf. Without cuts the group uses one page per leaf. -/
  cuts : Option (List (List Nat)) := none

structure Input where
  schema : Arrow.RecursiveSchema.Schema
  groups : List Group
  checksum : Bool := false

def Input.observations (input : Input) : List Observation := input.groups.map (·.data)

inductive Error where
  | schema (cause : Schema.Error)
  | groups (actual : Nat)
  | columns (actual : Nat)
  | totalRows (actual : Nat)
  | rowCount (group expected actual : Nat)
  | rows (group actual : Nat)
  | slots (group row actual : Nat)
  | totalSlots (group row actual : Nat)
  | projection (group row : Nat)
  | cutWidth (group expected actual : Nat)
  | cuts (group column : Nat)
  | chunk (group column : Nat) (cause : Chunk.Writer.Multi.Error)
  | footer (cause : Schema.Error)
  | openReadback (cause : Repeated.Error)
  | readback (cause : Rows.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def checkInput (limits : Limits) (input : Input) : Except Error Unit := do
  let count := input.groups.length
  if count > min limits.maxGroups limits.schema.snapshot.footer.compact.maxCollectionSize then
    throw (.groups count)
  let total := (input.groups.map (·.data.rowCount)).sum
  if total > limits.maxTotalRows || total ≥ 2^63 then throw (.totalRows total)
  for (group, ordinal) in input.groups.zipIdx do
    let actual := group.data.rows.length
    if actual ≠ group.data.rowCount then throw (.rowCount ordinal group.data.rowCount actual)
    if actual > limits.rows.chunk.maxRows then throw (.rows ordinal actual)

def countFields (visit : Field → Cell → Option Nat) : List Field → Row → Option Nat
  | [], [] => some 0
  | field :: fields, cell :: cells => do
    let count ← visit field cell
    let tail ← countFields visit fields cells
    return count + tail
  | _, _ => none

/-- Preflight the number of slots before expanding Lists or projecting a row.
Every element contributes one slot per leaf because a second repeated
ancestor is excluded by the compiler. -/
def countCell : Nat → Field → Cell → Option Nat
  | 0, _, _ => none
  | _ + 1, .leaf _, _ => some 1
  | _ + 1, .group _ children, none => some (children.flatMap Field.leaves).length
  | _ + 1, .list _ _ element, none => some element.leaves.length
  | depth + 1, .group _ children, some (.struct cells) => countFields (countCell depth) children cells
  | _ + 1, .list _ _ element, some (.list cells) => some (max 1 cells.length * element.leaves.length)
  | _, _, _ => none

structure Projection where
  slots : Nat
  columns : List (List Rows.Atom)

def project (limits : Limits) (fields : List Field) (group width already : Nat)
    (rows : List Row) : Except Error Projection := do
  let depth := limits.schema.snapshot.maxSchemaDepth - 1
  let reversed ← rows.zipIdx.foldlM (fun (acc : Projection) (row, ordinal) => do
    let some demand := countFields (countCell depth) fields row | throw (.projection group ordinal)
    let next := acc.slots + demand
    if next > limits.rows.maxSlots then throw (.slots group ordinal next)
    if already + next > limits.maxTotalSlots || already + next ≥ 2^63 then
      throw (.totalSlots group ordinal (already + next))
    let some projected := Rows.Projection.row depth fields row | throw (.projection group ordinal)
    if projected.length ≠ width || (projected.map List.length).sum ≠ demand then
      throw (.projection group ordinal)
    return ⟨next, List.zipWith (fun prior current => current.reverse ++ prior) acc.columns projected⟩)
    ⟨0, List.replicate width []⟩
  return ⟨reversed.slots, reversed.columns.map List.reverse⟩

abbrev Partition (atoms : List Rows.Atom) := { pages : List (List Rows.Atom) // pages.flatten = atoms }

def cutPages : List Nat → List Rows.Atom → List (List Rows.Atom) → Option (List (List Rows.Atom))
  | [], atoms, reversed => if atoms.isEmpty then some reversed.reverse else none
  | count :: rest, atoms, reversed =>
    let page := atoms.take count
    if count = 0 || page.length ≠ count then none
    else cutPages rest (atoms.drop count) (page :: reversed)

/-- An explicit partition must exhaust the supplied atoms in order. -/
def partition (atoms : List Rows.Atom) (cuts : Option (List Nat)) : Option (Partition atoms) :=
  match cuts, atoms with
  | none, atoms => some ⟨[atoms], by simp⟩
  | some [0], [] => some ⟨[[]], rfl⟩
  | some _, [] => none
  | some sizes, first :: rest => do
    let atoms := first :: rest
    let pages ← cutPages sizes atoms []
    if exact : pages.flatten = atoms then some ⟨pages, exact⟩ else none

structure Position where
  byte : Nat
  pages : Nat

def Position.initial : Position := ⟨4, 0⟩

def chunkLimits (limits : Limits) (cursor : Position) : Chunk.Limits :=
  { limits.rows.chunk with
    maxChunkBytes := min limits.rows.chunk.maxChunkBytes (limits.schema.fileBytes - cursor.byte - 8)
    framing.maxPages := min limits.rows.chunk.framing.maxPages (limits.maxTotalPages - cursor.pages) }

structure Placed where
  index : Schema.ColumnIndex
  wire : Bytes
  stop : Position

def place (start : Position) (leaf : Leaf) (written : Chunk.Writer.Multi.Output) : Placed :=
  let index := ⟨leaf.kind, leaf.site.location.path, written.numValues,
    start.byte + written.dataPageOffset, written.totalCompressedSize⟩
  ⟨index, written.wire, ⟨start.byte + written.wire.length, start.pages + written.frames.length⟩⟩

def writeColumn (limits : Limits) (checksum : Bool) (group column rows : Nat)
    (start : Position) (leaf : Leaf) (atoms : List Rows.Atom) (cuts : Option (List Nat)) :
    Except Error Placed := do
  let budget := chunkLimits limits start
  let pages := (cuts.map List.length).getD 1
  if pages > budget.framing.maxPages then throw (.chunk group column (.pageLimit pages budget.framing.maxPages))
  let some split := partition atoms cuts | throw (.cuts group column)
  let input : Chunk.Writer.Multi.Input := ⟨leaf, rows, split.val, checksum, group, column⟩
  let written ← (Chunk.Writer.Multi.emit budget input).mapError (.chunk group column)
  return place start leaf written

structure ColumnWire (limits : Limits) (checksum : Bool) (group column rows : Nat)
    (start : Position) (leaf : Leaf) (atoms : List Rows.Atom) (cuts : Option (List Nat))
    (placed : Placed) : Prop where
  original : ∃ (split : Partition atoms) (written : Chunk.Writer.Multi.Output) (packed : Chunk.Writer.Multi.Packed),
    partition atoms cuts = some split ∧
    let input : Chunk.Writer.Multi.Input := ⟨leaf, rows, split.val, checksum, group, column⟩
    let budget := chunkLimits limits start
    Chunk.Writer.Multi.emit budget input = .ok written ∧
    Chunk.Writer.Multi.Construction budget input packed ∧
    Chunk.Writer.Multi.Readback budget input packed written ∧
    placed = place start leaf written

structure GroupPack where
  index : Schema.GroupIndex
  payload : Bytes
  stop : Position
  slots : Nat

def writeGroup (limits : Limits) (checksum : Bool) (fields : List Field) (leaves : List Leaf)
    (index already : Nat) (start : Position) (group : Group) : Except Error GroupPack := do
  let width := leaves.length
  let rows := group.data.rows.length
  let projected ← project limits fields index width already group.data.rows
  let cuts ← match group.cuts with
    | none => pure (List.replicate width none)
    | some cuts =>
      if cuts.length = width then pure (cuts.map some)
      else throw (.cutWidth index width cuts.length)
  if projected.columns.length ≠ width then throw (.projection index 0)
  let (stop, payload, reversed) ← ((leaves.zip (projected.columns.zip cuts)).zipIdx).foldlM
    (fun (cursor, payload, reversed) ((leaf, atoms, sizes), column) => do
      let out ← writeColumn limits checksum index column rows cursor leaf atoms sizes
      return (out.stop, payload.append out.wire, out.index :: reversed))
    (start, Bytes.empty, [])
  return ⟨⟨rows, reversed.reverse⟩, payload, stop, projected.slots⟩

structure Packed where
  payload : Bytes
  groups : List Schema.GroupIndex

def pack (limits : Limits) (input : Input) (fields : List Field) (leaves : List Leaf) :
    Except Error Packed := do
  let width := leaves.length
  if width > limits.rows.maxColumns || width > limits.schema.snapshot.footer.compact.maxCollectionSize then
    throw (.columns width)
  let (_, _, payload, reversed) ← input.groups.zipIdx.foldlM
    (fun (cursor, used, payload, reversed) (group, index) => do
      let out ← writeGroup limits input.checksum fields leaves index used cursor group
      return (out.stop, used + out.slots, payload.append out.payload, out.index :: reversed))
    (Position.initial, 0, Bytes.empty, [])
  return ⟨payload, reversed.reverse⟩

structure Output where
  bytes : Bytes
  footer : Footer.Span
  metadata : Footer.Metadata

def serialize (limits : Limits) (input : Input) : Except Error Output := do
  checkInput limits input
  let schema ← (Schema.emit limits.schema input.schema).mapError .schema
  let packed ← pack limits input schema.source.schema.fields schema.source.schema.leaves.toList
  let framed ← (Schema.wrap limits.schema packed.payload schema.plan packed.groups).mapError .footer
  return ⟨framed.bytes, framed.footer, Schema.metadata schema.plan packed.groups⟩

def agrees (limits : Limits) (input : Input) (output : Output)
    (source : Repeated.Source limits.schema.snapshot output.bytes) : Bool :=
  Schema.equal limits.schema.snapshot.maxSchemaDepth input.schema source.schema.arrow &&
    decide (source.snapshot.footer = output.footer ∧ source.snapshot.metadata = output.metadata ∧
      source.snapshot.groupCount = input.groups.length)

/-- Verify the exact original file with the existing footer and row readers. -/
def certify (limits : Limits) (input : Input) (output : Output) : Except Error Unit := do
  let source ← (Repeated.openFile limits.schema.snapshot output.bytes).mapError .openReadback
  if agrees limits input output source then
    let recovered ← (Rows.readAll limits.rows source.schema).mapError .readback
    let equal := Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth
    if recovered.isEqv input.observations equal then .ok () else .error .readbackMismatch
  else .error .readbackMismatch

def emit (limits : Limits) (input : Input) : Except Error Output := do
  let output ← serialize limits input
  certify limits input output
  return output

structure Construction (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ (schema : Schema.Checked limits.schema) (packed : Packed),
    checkInput limits input = .ok () ∧ Schema.Wire limits.schema input.schema schema ∧
    pack limits input schema.source.schema.fields schema.source.schema.leaves.toList = .ok packed ∧
    Schema.wrap limits.schema packed.payload schema.plan packed.groups = .ok ⟨output.bytes, output.footer⟩ ∧
    output.metadata = Schema.metadata schema.plan packed.groups

structure Readback (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ source, Repeated.openFile limits.schema.snapshot output.bytes = .ok source ∧
    source.snapshot.bytes = output.bytes ∧ source.snapshot.footer = output.footer ∧
    source.snapshot.metadata = output.metadata ∧ source.schema.arrow = input.schema ∧
    source.snapshot.groupCount = input.groups.length ∧
    Rows.readAll limits.rows source.schema = .ok input.observations ∧
    List.Forall₂ (Rows.GroupWire limits.rows source.schema)
      (List.range source.snapshot.groupCount) input.observations

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer

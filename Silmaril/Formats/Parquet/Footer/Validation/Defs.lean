module

public import Silmaril.Formats.Parquet.Footer.Framing.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
import Std.Data.HashSet

/-! Semantic checks for the schema, row counts and in-file intervals of the footer profile. -/

public section

namespace Silmaril.Formats.Parquet.Footer

inductive ValidationError where
  | version
  | schema
  | schemaDepth
  | rowCount
  | columns
  | columnCountOrSize
  | pageInterval
  | indexInterval
  | bloomInterval
  deriving DecidableEq, Repr

/-- Interpret a positive-sized interval before the footer without signed wraparound
or saturating negative offsets. -/
@[expose] def checkDataSpan (footerStart : Nat) (offset size : Int) : Option Span :=
  if 4 ≤ offset ∧ 0 < size ∧ offset + size ≤ (footerStart : Int) then
    some ⟨offset.toNat, (offset + size).toNat⟩
  else none

private structure SchemaGroup where
  pathRev : List String
  remaining : Nat
  names : Std.HashSet String := {}

/-- Extract ordered physical leaves from a checked depth-first schema. The root
name is omitted from column paths. The legacy required root marker is admitted. -/
def schemaLeaves (maxDepth : Nat) (schema : List SchemaElement) :
    Except ValidationError (List (List String × PhysicalType)) := do
  let root :: nodes := schema | throw .schema
  let some count := root.numChildren | throw .schema
  if root.physicalType.isSome || root.typeLength.isSome || count ≤ 0 ||
      (root.repetition.isSome && root.repetition != some .required) then throw .schema
  if maxDepth = 0 then throw .schemaDepth
  go nodes [⟨[], count.toNat, {}⟩] []
where
  go (nodes : List SchemaElement) (groups : List SchemaGroup)
      (leaves : List (List String × PhysicalType)) :
      Except ValidationError (List (List String × PhysicalType)) := do
    let groups := groups.dropWhile (·.remaining == 0)
    match nodes, groups with
    | [], [] => pure leaves.reverse
    | node :: nodes, parent :: ancestors =>
      if parent.names.contains node.name || node.repetition.isNone then throw .schema
      if maxDepth ≤ groups.length then throw .schemaDepth
      let path := node.name :: parent.pathRev
      let parent := { parent with remaining := parent.remaining - 1, names := parent.names.insert node.name }
      let groups := parent :: ancestors
      match node.physicalType with
      | some type =>
        if node.numChildren.getD 0 ≠ 0 || (type == .fixedLenByteArray && node.typeLength.getD 0 ≤ 0) then
          throw .schema
        go nodes groups ((path.reverse, type) :: leaves)
      | none =>
        let count := node.numChildren.getD 0
        if count ≤ 0 || node.typeLength.isSome then throw .schema
        go nodes (⟨path, count.toNat, {}⟩ :: groups) leaves
    | _, _ => throw .schema

private def validateColumn (footerStart : Nat) (column : ColumnChunk) :
    Except ValidationError Unit := do
  let metadata := column.metadata
  if metadata.numValues < 0 || metadata.totalUncompressedSize < 0 then throw .columnCountOrSize
  let start := metadata.dictionaryPageOffset.getD metadata.dataPageOffset
  let some span := checkDataSpan footerStart start metadata.totalCompressedSize | throw .pageInterval
  if metadata.dataPageOffset < start || (span.stop : Int) ≤ metadata.dataPageOffset then throw .pageInterval
  if metadata.indexPageOffset.any (fun offset => offset < start || (span.stop : Int) ≤ offset) then
    throw .pageInterval
  checkOptionalSpan .indexInterval column.offsetIndexOffset column.offsetIndexLength
  checkOptionalSpan .indexInterval column.columnIndexOffset column.columnIndexLength
  match metadata.bloomFilterOffset, metadata.bloomFilterLength with
  | some offset, none => checkOptionalSpan .bloomInterval (some offset) (some 1)
  | offset, size => checkOptionalSpan .bloomInterval offset size
where
  checkOptionalSpan (error : ValidationError) (offset size : Option Int) : Except ValidationError Unit :=
    match offset, size with
    | none, none => pure ()
    | some start, some count =>
      if (checkDataSpan footerStart start count).isSome then pure () else throw error
    | _, _ => throw error

/-- Check the represented plaintext metadata. The caller supplies the start of the
footer from `locate` and a separate depth cap for flattened Parquet schemas. -/
def validate (footerStart maxSchemaDepth : Nat) (metadata : Metadata) : Except ValidationError Unit := do
  if metadata.version ≠ 1 && metadata.version ≠ 2 then throw .version
  let leaves ← schemaLeaves maxSchemaDepth metadata.schema
  let mut rows := 0
  for group in metadata.rowGroups do
    if group.numRows < 0 then throw .rowCount
    if group.totalByteSize < 0 then throw .columnCountOrSize
    rows := rows + group.numRows
    if group.columns.map (fun column => (column.metadata.pathInSchema, column.metadata.physicalType)) ≠ leaves then
      throw .columns
    for column in group.columns do
      validateColumn footerStart column
  if rows ≠ metadata.numRows then throw .rowCount

end Silmaril.Formats.Parquet.Footer

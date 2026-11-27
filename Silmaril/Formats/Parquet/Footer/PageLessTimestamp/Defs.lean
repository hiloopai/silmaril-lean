module

public import Silmaril.Formats.Parquet.Footer.PageLessInt32.Defs

/-! Exact no-frame row groups for packed flat Parquet TIMESTAMP sources. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Footer.PageLessTimestamp

open ThriftCompact
open Traversal (Reader Field)

inductive Error where
  | footer (cause : Footer.Error)
  | validation (cause : Footer.ValidationError)
  | raw (cause : PageLessInt32.Error)
  | schema
  | emptyColumns (index : Nat)
  | layout (index : Nat)
  | dataExtent
  deriving DecidableEq, Repr

/-- PyArrow's zero page offset is a sentinel. It represents no source bytes. -/
def noFrames (chunk : ColumnChunk) : Bool :=
  let col := chunk.metadata
  chunk.fileOffset == 0 && col.encodings == [3] && (col.codec == 0 || col.codec == 1) &&
    col.numValues == 0 && col.totalUncompressedSize == 0 && col.totalCompressedSize == 0 &&
    col.dataPageOffset == 0 && col.indexPageOffset.isNone && col.dictionaryPageOffset.isNone &&
    col.bloomFilterOffset.isNone && col.bloomFilterLength.isNone &&
    chunk.offsetIndexOffset.isNone && chunk.offsetIndexLength.isNone &&
    chunk.columnIndexOffset.isNone && chunk.columnIndexLength.isNone

def isPageLess (group : RowGroup) : Bool :=
  group.numRows == 0 && group.totalByteSize == 0 && group.fileOffset == some 0 &&
    group.totalCompressedSize == some 0 && !group.columns.isEmpty && group.columns.all noFrames

def flatSchema (schema : List SchemaElement) : Bool :=
  match schema with
  | [] => false
  | root :: leaves =>
    root.numChildren == some (Int.ofNat leaves.length) &&
      leaves.all (fun leaf => leaf.physicalType.isSome && leaf.numChildren.getD 0 == 0) &&
      leaves.any (fun leaf => leaf.physicalType == some .int64)

def matchesColumns (schema : List SchemaElement) (group : RowGroup) : Bool :=
  group.columns.map (fun col => (col.metadata.pathInSchema, some col.metadata.physicalType)) ==
    (schema.drop 1).map (fun leaf => ([leaf.name], leaf.physicalType))

namespace Internal

open PageLessInt32.Internal (field payload structFields)

/-- Inspect fields that the ordinary typed footer projection skips. -/
def checkEmptyChunk (reader : Reader) (index : Nat) (chunk : List Field) :
    Except PageLessInt32.Error Unit := do
  let failure := PageLessInt32.Error.emptyMetadata index
  if chunk.map (·.id) ≠ [2, 3] then throw failure
  let column ← field chunk 3 failure
  let metadata ← payload column .struct (structFields reader) failure
  if metadata.map (·.id) ≠ [1, 2, 3, 4, 5, 6, 7, 9, 13] then throw failure
  let stats ← field metadata 13 failure
  let [] ← payload stats .list (Traversal.readList reader .traversal .struct (structFields reader)) failure
    | throw failure

def checkEmptyRaw (reader : Reader) (index width : Nat) (group : List Field) :
    Except PageLessInt32.Error Unit := do
  let failure := PageLessInt32.Error.emptyMetadata index
  if ((group.filter (·.id != 7)).map (·.id)) ≠ [1, 2, 3, 5, 6] then throw failure
  let columns ← field group 1 failure
  let chunks ← payload columns .list (Traversal.readList reader .traversal .struct (structFields reader)) failure
  if chunks.length ≠ width then throw failure
  chunks.forM (checkEmptyChunk reader index)

def groupStop (reader : Reader) (footerStart : Nat) (schema : List SchemaElement)
    (index cursor : Nat) (group : RowGroup) (raw : List Field) : Except Error Nat := do
  (PageLessInt32.Internal.checkOrdinal reader index raw).mapError .raw
  if isPageLess group then
    if !matchesColumns schema group then throw (.emptyColumns index)
    (checkEmptyRaw reader index group.columns.length raw).mapError .raw
    return cursor
  else
    group.columns.foldlM (fun next chunk => do
      let column := chunk.metadata
      let start := column.dictionaryPageOffset.getD column.dataPageOffset
      let some span := checkDataSpan footerStart start column.totalCompressedSize | throw (.layout index)
      if span.start ≠ next then throw (.layout index)
      return span.stop) cursor

/-- The framed column chunks tile the data region in original footer order.
A verified page-less group has no interval and leaves this cursor unchanged. -/
def layout (reader : Reader) (footerStart : Nat) (schema : List SchemaElement) :
    Nat → Nat → List (RowGroup × List Field) → Except Error Nat
  | _, cursor, [] => .ok cursor
  | index, cursor, (group, raw) :: tail => do
    let stop ← groupStop reader footerStart schema index cursor group raw
    layout reader footerStart schema (index + 1) stop tail

end Internal

/-- Validate framed groups with the strict footer policy and retain the
unfiltered original footer in the caller's checked snapshot. -/
def validate (limits : Footer.Limits) (depth : Nat) (source : Bytes) (span : Span)
    (metadata : Metadata) : Except Error Unit := do
  if !(metadata.version == 2 && flatSchema metadata.schema) then Except.error .schema
  (Footer.validate span.start depth
    { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) }).mapError .validation
  let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
  let raw ← (PageLessInt32.Internal.groups reader).mapError .raw
  if raw.length ≠ metadata.rowGroups.length then Except.error (.raw .profile)
  let stop ← Internal.layout reader span.start metadata.schema 0 4 (metadata.rowGroups.zip raw)
  if stop ≠ span.start then Except.error .dataExtent

end Silmaril.Formats.Parquet.Footer.PageLessTimestamp

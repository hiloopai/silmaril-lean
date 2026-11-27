module

public import Silmaril.Formats.Parquet.Footer.PageLessTimestamp.Defs

/-! The pinned PyArrow no-page convention for recursive signed Parquet.
A zero offset is a sentinel. Framed chunks still cover the original data
region consecutively, in footer order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Footer.PageLessRecursive

open ThriftCompact.Traversal (Reader Field)

inductive Error where
  | validation (cause : Footer.ValidationError)
  | raw (cause : PageLessInt32.Error)
  | version
  | columns (group : Nat)
  | layout (group column : Nat)
  | dataExtent (expected actual : Nat)
  deriving DecidableEq, Repr

def isPageLess (group : RowGroup) : Bool :=
  PageLessTimestamp.isPageLess group &&
    group.columns.all (fun chunk => chunk.metadata.codec == 0)

def groupStop (reader : Reader) (footerStart : Nat)
    (leaves : List (List String × PhysicalType)) (index cursor : Nat)
    (group : RowGroup) (raw : List Field) : Except Error Nat := do
  (PageLessInt32.Internal.checkOrdinal reader index raw).mapError .raw
  if isPageLess group then
    if group.columns.map (fun col => (col.metadata.pathInSchema, col.metadata.physicalType)) ≠ leaves then
      throw (.columns index)
    (PageLessTimestamp.Internal.checkEmptyRaw reader index group.columns.length raw).mapError .raw
    return cursor
  else
    group.columns.zipIdx.foldlM (fun next (chunk, column) => do
      let metadata := chunk.metadata
      let start := metadata.dictionaryPageOffset.getD metadata.dataPageOffset
      let some span := checkDataSpan footerStart start metadata.totalCompressedSize
        | throw (.layout index column)
      if span.start ≠ next then throw (.layout index column)
      return span.stop) cursor

def layout (reader : Reader) (footerStart : Nat) (leaves : List (List String × PhysicalType)) :
    Nat → Nat → List (RowGroup × List Field) → Except Error Nat
  | _, cursor, [] => .ok cursor
  | index, cursor, (group, raw) :: rest => do
    let stop ← groupStop reader footerStart leaves index cursor group raw
    layout reader footerStart leaves (index + 1) stop rest

/-- Validate all ordinary ranges with the strict footer validator. Check the
omitted groups against the same ordered schema leaves and the exact raw
metadata convention, then require full coverage of the original data area. -/
def validate (limits : Footer.Limits) (depth : Nat) (source : Bytes) (span : Span)
    (metadata : Metadata) : Except Error Unit := do
  if metadata.version ≠ 2 then throw .version
  (Footer.validate span.start depth
    { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) }).mapError .validation
  let leaves ← (Footer.schemaLeaves depth metadata.schema).mapError .validation
  let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
  let raw ← (PageLessInt32.Internal.groups reader).mapError .raw
  if raw.length ≠ metadata.rowGroups.length then throw (.raw .profile)
  let stop ← layout reader span.start leaves 0 4 (metadata.rowGroups.zip raw)
  if stop ≠ span.start then throw (.dataExtent span.start stop)

end Silmaril.Formats.Parquet.Footer.PageLessRecursive

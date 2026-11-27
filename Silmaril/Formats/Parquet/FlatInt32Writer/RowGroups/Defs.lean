module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

/-! Assemble ordered native PLAIN V1 groups for one optional INT32 leaf. -/

public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer.RowGroups

inductive Error where
  | schemaOrCount
  | measure (index : Nat) (reason : FlatInt32Writer.Error)
  | page (index : Nat) (reason : PlainV1Writer.Error)
  | fileLimit
  | footer (reason : Compact.Error)
  | extent
  deriving DecidableEq, Repr

def fileLimit (limits : FlatInt32Writer.Limits) : Nat := min limits.maxFileBytes (2 ^ 63 - 1)

private def place (column : Compact.ColumnIndex) (start : Nat) :
    List (Nat × Nat) → List (Nat × List Compact.ColumnIndex)
  | [] => []
  | (rows, size) :: rest =>
    let stop := start + size
    (rows, [{column with span := ⟨start, stop⟩}]) :: place column stop rest

/-- Measure and place the existing INT32 pages, then encode the bounded
shared footer before allocating page bodies. Callers can check the result
with the flat INT32 snapshot reader. -/
def assemble (limits : FlatInt32Writer.Limits) (leaf : String) (groups : List (List (Option Int32))) :
    Except Error Bytes := do
  let compact := limits.footer.compact
  let counts := groups.map List.length
  if groups.isEmpty || groups.length > compact.maxCollectionSize || counts.sum ≥ 2 ^ 63 ||
      limits.maxColumns = 0 || compact.maxCollectionSize < 2 || leaf.utf8ByteSize > compact.maxBinaryBytes then
    throw .schemaOrCount
  let inputs := groups.map PlainV1Writer.Input.optional
  let sizes ← inputs.zipIdx.mapM fun (input, index) =>
    (FlatInt32Writer.measuredPage limits.page input).mapError (.measure index)
  let dataStop := 4 + sizes.sum
  if dataStop + 8 > fileLimit limits then throw .fileLimit
  let cap := min (min limits.footer.maxFooterBytes (2 ^ 32 - 1)) (fileLimit limits - dataStop - 8)
  let column : Compact.ColumnIndex := ⟨leaf, true, ⟨0, 0⟩⟩
  let footer ← (Compact.encodeGroups .unannotated cap [column] (place column 4 (counts.zip sizes))).mapError .footer
  let pages ← inputs.zipIdx.mapM fun (input, index) =>
    (PlainV1Writer.emit limits.page input).mapError (.page index)
  if pages.map (·.wire.length) ≠ sizes then throw .extent
  let data := Bytes.ofList (pages.flatMap (·.wire.toList))
  let prefixBytes := (Footer.magic.append data).append footer
  return (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic

end Silmaril.Formats.Parquet.FlatInt32Writer.RowGroups

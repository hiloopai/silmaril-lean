module

public import Silmaril.Formats.Parquet.Footer.PageLessRecursive.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.PageLessRecursive.Validation

namespace Silmaril.Formats.Parquet.Footer.PageLessRecursive

public theorem empty_counts {group : RowGroup} {chunk : ColumnChunk}
    (empty : isPageLess group = true) (member : chunk ∈ group.columns) :
    group.numRows = 0 ∧ chunk.metadata.numValues = 0 ∧ chunk.metadata.totalCompressedSize = 0 :=
  Proofs.Formats.Parquet.Footer.PageLessRecursive.empty_counts empty member

/-- An empty group's original column declarations and raw footer are checked
at its original ordinal. Its data cursor stays at the same byte. -/
public theorem groupStop_empty {reader : ThriftCompact.Traversal.Reader} {footerStart : Nat}
    {leaves : List (List String × PhysicalType)} {index cursor stop : Nat}
    {group : RowGroup} {raw : List ThriftCompact.Traversal.Field}
    (empty : isPageLess group = true)
    (accepted : groupStop reader footerStart leaves index cursor group raw = .ok stop) :
    stop = cursor ∧
      group.columns.map (fun col => (col.metadata.pathInSchema, col.metadata.physicalType)) = leaves ∧
      PageLessTimestamp.Internal.checkEmptyRaw reader index group.columns.length raw = .ok () :=
  Proofs.Formats.Parquet.Footer.PageLessRecursive.groupStop_empty empty accepted

end Silmaril.Formats.Parquet.Footer.PageLessRecursive

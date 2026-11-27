module

public import Silmaril.Formats.Parquet.Footer.PageLessRecursive.Defs

namespace Silmaril.Proofs.Formats.Parquet.Footer.PageLessRecursive

open Silmaril.Formats Parquet

public theorem empty_counts {group : Footer.RowGroup} {chunk : Footer.ColumnChunk}
    (empty : Footer.PageLessRecursive.isPageLess group = true)
    (member : chunk ∈ group.columns) :
    group.numRows = 0 ∧ chunk.metadata.numValues = 0 ∧ chunk.metadata.totalCompressedSize = 0 := by
  simp only [Footer.PageLessRecursive.isPageLess, Bool.and_eq_true,
    Footer.PageLessTimestamp.isPageLess, beq_iff_eq, List.all_eq_true] at empty
  have noFrames := empty.1.2 chunk member
  simp only [Footer.PageLessTimestamp.noFrames, Bool.and_eq_true, beq_iff_eq] at noFrames
  grind

open Footer.PageLessRecursive

public theorem groupStop_empty {reader : ThriftCompact.Traversal.Reader} {footerStart : Nat}
    {leaves : List (List String × Footer.PhysicalType)} {index cursor stop : Nat}
    {group : Footer.RowGroup} {raw : List ThriftCompact.Traversal.Field}
    (empty : isPageLess group = true)
    (accepted : groupStop reader footerStart leaves index cursor group raw = .ok stop) :
    stop = cursor ∧
      group.columns.map (fun col => (col.metadata.pathInSchema, col.metadata.physicalType)) = leaves ∧
      Footer.PageLessTimestamp.Internal.checkEmptyRaw reader index group.columns.length raw = .ok () := by
  cases ordinal : Footer.PageLessInt32.Internal.checkOrdinal reader index raw with
  | error cause => simp [groupStop, ordinal, Except.mapError, Except.bind, Bind.bind] at accepted
  | ok value =>
    cases value
    by_cases columns :
        group.columns.map (fun col => (col.metadata.pathInSchema, col.metadata.physicalType)) = leaves
    · cases checked : Footer.PageLessTimestamp.Internal.checkEmptyRaw reader index group.columns.length raw with
      | error cause =>
        simp [groupStop, empty, ordinal, columns, checked, Except.mapError, Except.bind, Bind.bind] at accepted
      | ok value =>
        cases value
        simp [groupStop, empty, ordinal, columns, checked, Except.mapError, Except.bind, Bind.bind,
          Pure.pure, Except.pure] at accepted
        exact ⟨accepted.symm, columns, rfl⟩
    · simp [groupStop, ordinal, empty, columns, Except.mapError, Except.bind, Bind.bind] at accepted

end Silmaril.Proofs.Formats.Parquet.Footer.PageLessRecursive

module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Thms
import Silmaril.Formats.Parquet.Footer.PageLessTimestamp.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Defs

open Silmaril.Formats.Parquet
open Timestamp.Leaf.MixedGroups

private def column : Footer.ColumnMetadata :=
  { physicalType := .int64
    encodings := [3]
    pathInSchema := ["ticks"]
    codec := 1
    numValues := 0
    totalUncompressedSize := 0
    totalCompressedSize := 0
    dataPageOffset := 0
    indexPageOffset := none
    dictionaryPageOffset := none
    bloomFilterOffset := none
    bloomFilterLength := none }

private def group (metadata : Footer.ColumnMetadata) : Footer.RowGroup :=
  ⟨[⟨0, metadata, none, none, none, none⟩], 0, 0, some 0, some 0⟩

#guard Footer.PageLessTimestamp.isPageLess (group column)
#guard !Footer.PageLessTimestamp.isPageLess {group column with numRows := 1}
#guard !Footer.PageLessTimestamp.isPageLess (group {column with numValues := 1})
#guard !Footer.PageLessTimestamp.isPageLess (group {column with totalCompressedSize := 1})
#guard !Footer.PageLessTimestamp.isPageLess (group {column with dataPageOffset := 4})
#guard !Footer.PageLessTimestamp.isPageLess (group {column with dictionaryPageOffset := some 4})
#guard !Footer.PageLessTimestamp.isPageLess (group {column with codec := 2})
#guard (PageLess.convert .modernOnly {} {maxFileBytes := 1} {} (.ofList [0, 1]) 1)
  matches .error (.fileByteLimit 1 2)

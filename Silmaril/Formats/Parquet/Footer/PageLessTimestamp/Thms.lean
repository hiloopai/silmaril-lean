module

public import Silmaril.Formats.Parquet.Footer.PageLessTimestamp.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.PageLessTimestamp.Validation

public section

namespace Silmaril.Formats.Parquet.Footer.PageLessTimestamp

open ThriftCompact.Traversal (Reader Field)

/-- Admitted no-frame groups have zero rows, values and storage, with sentinel offsets. -/
theorem pageLess_zero {group : RowGroup} (empty : isPageLess group = true) :
    group.numRows = 0 ∧ group.totalByteSize = 0 ∧ group.fileOffset = some 0 ∧
      group.totalCompressedSize = some 0 ∧ group.columns ≠ [] ∧
      ∀ col ∈ group.columns,
        col.metadata.numValues = 0 ∧ col.metadata.totalCompressedSize = 0 ∧
        col.metadata.totalUncompressedSize = 0 ∧ col.metadata.dataPageOffset = 0 ∧
        col.metadata.dictionaryPageOffset = none ∧ col.metadata.indexPageOffset = none :=
  Proofs.Formats.Parquet.Footer.PageLessTimestamp.pageLess_zero empty

/-- Framed groups pass strict validation and exactly tile the source data region. -/
theorem validate_wire {limits : Limits} {depth : Nat} {source : Bytes}
    {span : Span} {metadata : Metadata}
    (admitted : PageLessTimestamp.validate limits depth source span metadata = .ok ()) :
    Footer.validate span.start depth { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) } = .ok () ∧
      let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
      ∃ raw, PageLessInt32.Internal.groups reader = .ok raw ∧ raw.length = metadata.rowGroups.length ∧
        Internal.layout reader span.start metadata.schema 0 4 (metadata.rowGroups.zip raw) = .ok span.start :=
  Proofs.Formats.Parquet.Footer.PageLessTimestamp.validate_wire admitted

/-- An admitted no-frame group leaves the physical cursor unchanged. -/
theorem groupStop_empty {reader : Reader} {footerStart index cursor stop : Nat}
    {schema : List SchemaElement} {group : RowGroup} {raw : List Field}
    (empty : isPageLess group = true)
    (checked : Internal.groupStop reader footerStart schema index cursor group raw = .ok stop) :
    matchesColumns schema group = true ∧
      Internal.checkEmptyRaw reader index group.columns.length raw = .ok () ∧ stop = cursor :=
  Proofs.Formats.Parquet.Footer.PageLessTimestamp.groupStop_empty empty checked

/-- An original no-frame group matches the original schema and raw no-page convention. -/
theorem validate_empty {limits : Footer.Limits} {depth : Nat} {source : Bytes}
    {span : Span} {metadata : Metadata} {index : Nat} {group : RowGroup}
    (admitted : PageLessTimestamp.validate limits depth source span metadata = .ok ())
    (found : metadata.rowGroups[index]? = some group) (empty : isPageLess group = true) :
    matchesColumns metadata.schema group = true ∧
      let reader : Reader := ⟨fileBytes source span.start span.stop, limits.compact, limits.varintMode⟩
      ∃ raw fields, PageLessInt32.Internal.groups reader = .ok raw ∧
        raw[index]? = some fields ∧ Internal.checkEmptyRaw reader index group.columns.length fields = .ok () :=
  Proofs.Formats.Parquet.Footer.PageLessTimestamp.validate_empty admitted found empty

end Silmaril.Formats.Parquet.Footer.PageLessTimestamp

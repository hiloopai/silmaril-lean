module

public import Silmaril.Formats.Parquet.ListFile.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Writer.Body
import Silmaril.Proofs.Formats.Parquet.ListFile.Writer.File

public section

namespace Silmaril.Formats.Parquet.ListFile.Writer

open ListPage (Row)

/-- Every distinct list marker or element contributes one level slot. -/
theorem PageEncoding.entries_length (rows : List Row) : (PageEncoding.entries rows).length = PageEncoding.slotCount rows :=
  Proofs.Formats.Parquet.ListFile.Writer.entries_length rows

/-- The PLAIN suffix keeps every present child in original row and child order. -/
theorem PageEncoding.entries_values (rows : List Row) :
    (PageEncoding.entries rows).filterMap (·.2.2) = rows.flatMap (fun row => (row.getD []).filterMap id) :=
  Proofs.Formats.Parquet.ListFile.Writer.entries_values rows

/-- The exact body size includes both V1 level lengths and all PLAIN bytes. -/
theorem PageEncoding.body_length (rows : List Row) : (PageEncoding.body rows).length = PageEncoding.bodySize rows :=
  Proofs.Formats.Parquet.ListFile.Writer.body_length rows

/-- The written levels and scalar bytes witness the original ordered nested slots. -/
theorem PageEncoding.body_wire {rows : List Row} {limits : ListFile.Multi.Limits}
    (fits : PageEncoding.Fits limits rows) : ListPage.SlotsWire (PageEncoding.slotCount rows) (PageEncoding.body rows) (PageEncoding.entries rows) :=
  Proofs.Formats.Parquet.ListFile.Writer.body_wire fits

/-- Measurement checks page limits before allocating the body. -/
theorem PageEncoding.measure_fits {limits : ListFile.Multi.Limits} {rows : List Row} {headerBytes : Bytes}
    (h : PageEncoding.measure limits rows = .ok headerBytes) :
    PageEncoding.Fits limits rows ∧ headerBytes.length ≤ limits.file.framing.maxHeaderBytes ∧
      PlainV1Writer.encodeHeader (PageEncoding.slotCount rows) (PageEncoding.bodySize rows) = some headerBytes :=
  Proofs.Formats.Parquet.ListFile.Writer.measure_fits h

/-- A checked page retains its exact body and original complete rows. -/
theorem PageEncoding.encode_wire {limits : ListFile.Multi.Limits} {rows : List Row} {headerBytes : Bytes}
    {page : PlainV1Writer.Encoded} (h : PageEncoding.encode limits rows headerBytes = .ok page) :
    page.header = PageEncoding.header rows ∧ page.headerBytes = headerBytes ∧ page.body = PageEncoding.body rows ∧
      ListPage.decodeV1 limits.file.page 0 page.header rows.length page.body = .ok rows ∧
      ListPage.PageWire limits.file.page 0 page.header rows.length page.body rows :=
  Proofs.Formats.Parquet.ListFile.Writer.encode_wire h

/-- Input preflight enforces schema and aggregate resource bounds. -/
theorem checkInput_exact {limits : Limits} {input : Input}
    (h : checkInput limits input = .ok ()) :
    let compact := limits.readback.file.snapshot.footer.compact
    input.childName = "element" ∧ 4 ≤ compact.maxCollectionSize ∧
      max 7 input.name.utf8ByteSize ≤ compact.maxBinaryBytes ∧
      input.groups.length ≤ limits.maxGroups ∧ input.groups.length ≤ compact.maxCollectionSize ∧
      input.totalRows ≤ limits.maxTotalRows ∧ input.totalRows < 2^63 ∧
      input.totalSlots ≤ limits.maxTotalSlots :=
  Proofs.Formats.Parquet.ListFile.Writer.checkInput_exact h

/-- The output checks exact file and frame positions and one page per original group. -/
theorem emit_exact {limits : Limits} {input : Input} {output : Encoded}
    (h : emit limits input = .ok output) :
    checkInput limits input = .ok () ∧ output.Layout limits input ∧
    (∀ rows ∈ input.groups, PageEncoding.Fits limits.readback rows) ∧
    List.Forall₂ (fun rows group =>
      group.page.body = PageEncoding.body rows ∧
      ListPage.PageWire limits.readback.file.page 0 group.page.header rows.length group.page.body rows)
      input.groups output.groups ∧
    ∃ checked,
      ListFile.openFile limits.readback.file output.bytes = .ok checked ∧
      checked.shape.outer.name = input.name ∧ checked.shape.element.name = input.childName ∧
      checked.snapshot.groupCount = input.groups.length ∧
      readGroups limits.readback checked = .ok input.groups :=
  Proofs.Formats.Parquet.ListFile.Writer.emit_exact h

/-- The native reader recovers the original field names and every group in order. -/
theorem emit_readback {limits : Limits} {input : Input} {output : Encoded}
    (h : emit limits input = .ok output) :
    ∃ checked,
      ListFile.openFile limits.readback.file output.bytes = .ok checked ∧
      ListFile.OpenWire limits.readback.file output.bytes checked ∧
      checked.shape.outer.name = input.name ∧ checked.shape.element.name = input.childName ∧
      checked.snapshot.groupCount = input.groups.length ∧
      readGroups limits.readback checked = .ok input.groups ∧
      List.Forall₂ (Multi.GroupWire limits.readback.maxGroupSlots checked)
        (List.range checked.snapshot.groupCount) input.groups :=
  Proofs.Formats.Parquet.ListFile.Writer.emit_readback h

/-- The original frame consumes its complete footer-advertised chunk. -/
theorem emitted_frame {limits : Limits} {input : Input} {output : Encoded} {group : GroupPage}
    (h : emit limits input = .ok output) (member : group ∈ output.groups) :
    Page.Chain group.index.span group.index.span.start group.index.span.stop [group.frame] :=
  Proofs.Formats.Parquet.ListFile.Writer.emitted_frame h member

end Silmaril.Formats.Parquet.ListFile.Writer

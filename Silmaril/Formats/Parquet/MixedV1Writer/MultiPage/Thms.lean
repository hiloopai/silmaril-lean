module

public import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.MultiPage.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.MultiPage
open Silmaril.Formats

/-- Admission certifies the independent group, row, per-chunk and total page caps. -/
theorem admit_checked {limits : Limits} {input : Input} (accepted : admit limits input = .ok ()) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.file.maxGroups ∧
    input.groups.length ≤ limits.file.writer.footer.compact.maxCollectionSize ∧
    input.totalRows ≤ limits.file.maxTotalRows ∧ input.totalRows < 2 ^ 63 ∧
    input.ChunkPageBound limits ∧ input.totalPages ≤ limits.maxPages ∧ input.Valid limits :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.admit_checked accepted

/-- The actual byte carrier has the exact footer, page cuts and contiguous chunks. -/
theorem emit_checked {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emit order limits input = .ok output) :
    admit limits input = .ok () ∧ output.Checked order limits input ∧ certify limits input output = .ok () :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.emit_checked written

/-- Pair aligned slots after flattening each page partition independently. -/
theorem rows_exact {group : Group} {intField byteField : Int32ByteArrayGroup.Field}
    (matched : group.Matches intField byteField) :
    group.rows.length = group.rowCount ∧ group.rows.unzip = (group.intSlots, group.byteSlots) :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.rows_exact matched

/-- Every original group, including empty groups, reads back in footer order with exact slots. -/
theorem emit_indexed {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emit order limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.file.writer.readback output.bytes input.intField input.byteField =
        .ok opened ∧ opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.file.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.file.writer.readback i.val (input.groups.get i).rows ∧
        (input.groups.get i).rows.unzip = ((input.groups.get i).intSlots, (input.groups.get i).byteSlots) :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.emit_indexed written

/-- Actual checked frames start at the declared first page and exactly cover the chunk. -/
theorem column_chain {limits : Page.Limits} {file : Bytes} {footerStart : Nat}
    {column : Footer.ColumnMetadata} {span : Footer.Span} {pages : List EncodedPage}
    (checked : ColumnChecked limits file footerStart column span pages) :
    Page.Chain span span.start span.stop (frames span.start pages) :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.column_chain checked

/-- The checked chunk extent is the sum of its actual header and payload lengths. -/
theorem column_size {limits : Page.Limits} {file : Bytes} {footerStart : Nat}
    {column : Footer.ColumnMetadata} {span : Footer.Span} {pages : List EncodedPage}
    (checked : ColumnChecked limits file footerStart column span pages) :
    span.stop = span.start + (pages.map (fun page => page.headerBytes.length + page.body.length)).sum :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.column_size checked

/-- The two chunks adjoin at each indexed group before continuing with the next. -/
theorem contiguous_cons {order : Order} {start stop : Nat} {group : Chunks} {rest : List Chunks} :
    Contiguous order start (group :: rest) stop ↔
      let (first, second) := group.index.spans order
      first.start = start ∧ second.start = first.stop ∧ Contiguous order second.stop rest stop := by
  cases order <;> simp [Contiguous, contiguous, Compact.GroupIndex.spans, Order.arrange, and_assoc]

/-- Recutting either column while retaining its slots leaves the logical group unchanged. -/
theorem Group.rows_eq_of_slots {left right : Group}
    (integers : left.intSlots = right.intSlots) (octets : left.byteSlots = right.byteSlots) :
    left.rows = right.rows := by simp [Group.rows, integers, octets]

/-- The page ordinal has its original header at the sum of preceding wire lengths. -/
theorem frame_at (start : Nat) (pages : List EncodedPage) {ordinal : Nat} {page : EncodedPage}
    (selected : pages[ordinal]? = some page) :
    ∃ positioned, (frames start pages)[ordinal]? = some positioned ∧
      positioned = MixedV1Writer.frame
        ⟨start + ((pages.take ordinal).map (fun prev => prev.headerBytes.length + prev.body.length)).sum,
          start + ((pages.take ordinal).map (fun prev => prev.headerBytes.length + prev.body.length)).sum +
            page.headerBytes.length + page.body.length⟩ page :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.frame_at start pages selected

/-- A zero-row group has one zero-slot V1 page per chunk. -/
theorem empty_group {group : Group} {intField byteField : Int32ByteArrayGroup.Field}
    (matched : group.Matches intField byteField) (empty : group.rowCount = 0) :
    group.intCuts = [0] ∧ group.byteCuts = [0] ∧ group.rows = [] :=
  Proofs.Formats.Parquet.MixedV1Writer.MultiPage.empty_group matched empty

end Silmaril.Formats.Parquet.MixedV1Writer.MultiPage

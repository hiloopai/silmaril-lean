module

public import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms
import Silmaril.Formats.Parquet.Page.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.MultiPage

open Silmaril.Formats Silmaril.Formats.Parquet
open MixedV1Writer (Order)
open MixedV1Writer.MultiPage

theorem admit_checked {limits : Limits} {input : Input} (accepted : admit limits input = .ok ()) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.file.maxGroups ∧
    input.groups.length ≤ limits.file.writer.footer.compact.maxCollectionSize ∧
    input.totalRows ≤ limits.file.maxTotalRows ∧ input.totalRows < 2 ^ 63 ∧
    input.ChunkPageBound limits ∧ input.totalPages ≤ limits.maxPages ∧ input.Valid limits := by
  unfold admit at accepted
  split at accepted
  · contradiction
  rename_i groups
  split at accepted
  · contradiction
  rename_i rows
  split at accepted
  · contradiction
  rename_i chunk
  split at accepted
  · contradiction
  rename_i pages
  split at accepted
  · contradiction
  rename_i layout
  have groupBounds := not_or.mp groups
  have countBounds := not_or.mp groupBounds.2
  have rowBounds := not_or.mp rows
  exact ⟨groupBounds.1, Nat.le_of_not_gt countBounds.1, Nat.le_of_not_gt countBounds.2,
    Nat.le_of_not_gt rowBounds.1, Nat.lt_of_not_ge rowBounds.2, not_not.mp chunk,
    Nat.le_of_not_gt pages, not_not.mp layout⟩

theorem emit_checked {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emit order limits input = .ok output) :
    admit limits input = .ok () ∧ output.Checked order limits input ∧ certify limits input output = .ok () := by
  cases admission : admit limits input with
  | error cause => simp [emit, admission, Bind.bind, Except.bind] at written
  | ok result =>
    cases result
    cases assembled : assemble order limits input with
    | error cause => simp [emit, admission, assembled, Bind.bind, Except.bind] at written
    | ok candidate =>
      by_cases checked : candidate.Checked order limits input
      · cases certified : certify limits input candidate <;>
          simp_all [emit, Bind.bind, Except.bind, Except.mapError, Except.map]
      · simp [emit, admission, assembled, checked, Bind.bind, Except.bind] at written

private theorem intSlots_length (group : Group) : group.intSlots.length = group.rowCount := by
  have slots (page : PlainV1Writer.Input) : page.slots.length = page.numValues := by
    cases page <;> simp [PlainV1Writer.Input.slots, PlainV1Writer.Input.numValues]
  simp [Group.intSlots, Group.rowCount, Group.intCuts, List.length_flatMap, slots]

private theorem byteSlots_length (group : Group) : group.byteSlots.length = group.byteCuts.sum := by
  have slots (page : PlainByteArrayV1Writer.Input) : page.slots.length = page.numValues := by
    cases page <;> simp [PlainByteArrayV1Writer.Input.slots, PlainByteArrayV1Writer.Input.numValues]
  simp [Group.byteSlots, Group.byteCuts, List.length_flatMap, slots]

theorem rows_exact {group : Group} {intField byteField : Int32ByteArrayGroup.Field}
    (matched : group.Matches intField byteField) :
    group.rows.length = group.rowCount ∧ group.rows.unzip = (group.intSlots, group.byteSlots) := by
  have same := (intSlots_length group).trans (matched.1.trans (byteSlots_length group).symm)
  exact ⟨by simp [Group.rows, List.length_zip, ← same, intSlots_length], List.unzip_zip same⟩

theorem emit_indexed {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emit order limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.file.writer.readback output.bytes input.intField input.byteField =
        .ok opened ∧ opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.file.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.file.writer.readback i.val (input.groups.get i).rows ∧
        (input.groups.get i).rows.unzip = ((input.groups.get i).intSlots, (input.groups.get i).byteSlots) := by
  obtain ⟨admitted, _, certified⟩ := emit_checked written
  have valid := (admit_checked admitted).2.2.2.2.2.2.2
  cases opened : Int32ByteArrayGroup.openFile limits.file.writer.readback output.bytes
      input.intField input.byteField with
  | error cause => simp [certify, opened, Except.mapError, Bind.bind, Except.bind] at certified
  | ok checked =>
    by_cases count : checked.snapshot.groupCount = input.groups.length
    · have groups := MixedV1Writer.Multi.checkGroups_indexed limits.file.writer.readback checked
          (input.groups.map Group.observation) 0 (by
        simpa [certify, opened, count, Except.mapError, Bind.bind, Except.bind] using certified)
      refine ⟨checked, rfl, count, fun i => ?_⟩
      have read : checked.readGroup limits.file.writer.readback i.val = .ok (input.groups.get i).rows := by
        simpa [Group.observation, Group.rows, MixedV1Writer.Multi.Group.rows, PlainV1Writer.Input.slots,
          PlainByteArrayV1Writer.Input.slots] using groups ⟨i.val, by simp⟩
      have matched := valid.2.2.2.2.2.2 (input.groups.get i) (List.get_mem input.groups i)
      exact ⟨read, Int32ByteArrayGroup.readGroup_wire read, (rows_exact matched).2⟩
    · simp [certify, opened, count, Except.mapError, Bind.bind, Except.bind] at certified

theorem column_chain {limits : Page.Limits} {file : Bytes} {footerStart : Nat}
    {column : Footer.ColumnMetadata} {span : Footer.Span} {pages : List EncodedPage}
    (checked : ColumnChecked limits file footerStart column span pages) :
      Page.Chain span span.start span.stop (frames span.start pages) :=
  (Page.readChunk_chain checked.2.1).2.2

private theorem frameChain_stop {span : Footer.Span} (pages : List EncodedPage) {start stop : Nat}
    (chain : Page.Chain span start stop (frames start pages)) :
    stop = start + (pages.map (fun page => page.headerBytes.length + page.body.length)).sum := by
  induction pages generalizing start with
  | nil => cases chain; simp
  | cons page rest ih =>
    simp only [frames] at chain
    cases chain with
    | cons within next =>
      have tail := ih next
      simpa [MixedV1Writer.frame, Nat.add_assoc] using tail

theorem column_size {limits : Page.Limits} {file : Bytes} {footerStart : Nat}
    {column : Footer.ColumnMetadata} {span : Footer.Span} {pages : List EncodedPage}
    (checked : ColumnChecked limits file footerStart column span pages) :
    span.stop = span.start + (pages.map (fun page => page.headerBytes.length + page.body.length)).sum :=
  frameChain_stop pages (column_chain checked)

theorem frame_at (start : Nat) (pages : List EncodedPage) {ordinal : Nat} {page : EncodedPage}
    (selected : pages[ordinal]? = some page) :
    ∃ positioned, (frames start pages)[ordinal]? = some positioned ∧
      positioned = MixedV1Writer.frame
        ⟨start + ((pages.take ordinal).map (fun prev => prev.headerBytes.length + prev.body.length)).sum,
          start + ((pages.take ordinal).map (fun prev => prev.headerBytes.length + prev.body.length)).sum +
            page.headerBytes.length + page.body.length⟩ page := by
  induction pages generalizing start ordinal with
  | nil => simp at selected
  | cons first rest ih =>
    cases ordinal with
    | zero =>
      simp at selected
      subst page
      exact ⟨_, rfl, by simp⟩
    | succ n =>
      obtain ⟨positioned, atIndex, placed⟩ := ih (start + first.headerBytes.length + first.body.length)
        (by simpa using selected)
      refine ⟨positioned, by simpa [frames] using atIndex, ?_⟩
      simpa [List.take_succ_cons, Nat.add_assoc] using placed

private theorem emptyCuts {cuts : List Nat} (layout : ValidCuts cuts) (empty : cuts.sum = 0) :
    cuts = [0] := by
  rcases layout with zero | ⟨nonempty, positive⟩
  · exact zero
  · cases cuts with
    | nil => contradiction
    | cons head tail =>
      have headPositive := positive head (by simp)
      simp only [List.sum_cons] at empty
      omega

theorem empty_group {group : Group} {intField byteField : Int32ByteArrayGroup.Field}
    (matched : group.Matches intField byteField) (empty : group.rowCount = 0) :
    group.intCuts = [0] ∧ group.byteCuts = [0] ∧ group.rows = [] :=
  ⟨emptyCuts matched.2.1 empty, emptyCuts matched.2.2.1 (matched.1.symm.trans empty),
    List.length_eq_zero_iff.mp ((rows_exact matched).1.trans empty)⟩

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.MultiPage

module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

open Silmaril.Relational
open ListPage (Event State Row)

/-- Original CRC, absolute V2 level spans, bounded suffix and signed indexed slots agree. -/
theorem readFrame_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked entries budget frame = .ok events) :
    FrameWire limits checked entries frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readFrame_wire h

/-- A stored checksum refusal precedes V2 split, expansion and index lookup. -/
theorem readFrame_checksum_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 8)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.snappy.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked entries budget frame = .error (.checksum cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readFrame_checksum_error kind encoding slots expanded failed

/-- One original signed dictionary supplies every ordered V2 data frame and checked nested row. -/
theorem readGroup_wire {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readGroup_wire h

/-- Original V2 page counts sum to the footer slot and row totals and the reconstructed null count. -/
theorem readGroup_counts {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    ∃ chunk infos,
      ListFile.Multi.Snappy.DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = ListFile.Multi.Snappy.pageNulls (rows.flatMap ListPage.rowEvents) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readGroup_counts h

/-- After a successful prefix the first failing frame retains its original ordinal, offset and cause. -/
theorem readFrames_first_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {earlier rest : List Page.Frame} {frame : Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State} {cause : DictionaryV1.FrameError}
    (decoded : ListFile.Multi.Snappy.DictionaryV1.readFramesUsing (readFrame limits checked entries)
      ordinal budget state earlier = .ok (left, next))
    (failed : readFrame limits checked entries left frame = .error cause) :
    ListFile.Multi.Snappy.DictionaryV1.readFramesUsing (readFrame limits checked entries)
      ordinal budget state (earlier ++ frame :: rest) =
      .error (.frame (ordinal + earlier.length) frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readFrames_first_error decoded failed

/-- A leading dictionary refusal retains original frame zero and absolute offset. -/
theorem readGroup_dictionary_error {limits : DictionaryV1.Limits} {checked : ListFile.Checked} {ordinal expanded : Nat}
    {chunk : ListFile.Multi.Snappy.DictionaryV1.Chunk} {cause : DictionaryV1.FrameError}
    (selected : ListFile.Multi.Snappy.DictionaryV1.selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : ListFile.Multi.Snappy.DictionaryV1.readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.readGroup_dictionary_error selected slots rows failed

/-- The original indexed source failure retains previous groups ahead of native IPC admission. -/
theorem convert_first_error {limits : DictionaryV1.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : DictionaryV1.GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsWith DictionaryV1.SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.convert_first_error opened split earlier failed

/-- The checked V2 source and emitted native Arrow LIST agree through exact EOS. -/
theorem convert_readback {limits : DictionaryV1.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.convert_readback h

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

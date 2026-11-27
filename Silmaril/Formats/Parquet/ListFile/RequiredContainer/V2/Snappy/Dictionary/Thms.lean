module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Correctness
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Thms

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

open Silmaril.Relational
open ListPage (Event Row State)
open RequiredContainer (Checked)
open V2 (missingSlots)
open Snappy (StoredWire)
open ListFile.Multi.Snappy (Budget)
open ListFile.Multi.Snappy.DictionaryV1 (LookupWire Chunk selectChunk readEntries readFramesUsing)

/-- The page refuses any other V2 value encoding at its original header. -/
theorem readFrame_encoding_error {limits : Limits} {checked : Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} (kind : frame.value.kind = .dataV2 info)
    (encoding : info.encoding ≠ 8) :
    readFrame limits checked entries budget frame = .error (.dataEncoding info.encoding) := by
  simp [readFrame, kind, encoding]
  rfl

/-- A stored CRC refusal precedes suffix expansion, level decoding and dictionary lookup. -/
theorem readFrame_checksum_error {limits : Limits} {checked : Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 8)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (rows : info.numRows ≤ checked.limits.page.maxRows)
    (failed : Page.Checksum.verify limits.snappy.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked entries budget frame = .error (.v2 (.checksum cause)) := by
  simp [readFrame, Snappy.readSections, bodyLimits, kind, encoding, Nat.not_lt.mpr slots, Nat.not_lt.mpr expanded,
    Nat.not_lt.mpr rows, failed, Except.mapError, Bind.bind, Except.bind]

/-- The original CRC and selected dictionary suffix bind every supported V2 child value. -/
theorem readFrame_wire {limits : Limits} {checked : Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked entries budget frame = .ok events) :
    FrameWire limits checked entries frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.readFrame_wire h

/-- Raw levels begin at a row boundary and determine the exact dictionary lookup count. -/
theorem frame_levels {limits : Limits} {checked : Checked} {entries : Array Int32}
    {frame : Page.Frame} {events : List Event} (h : FrameWire limits checked entries frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire (bodyLimits limits) checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧
      LookupWire limits entries (info.numValues - info.numNulls) sections.scalars
        (events.filterMap (fun event => event.wire.2.2)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.frame_levels h

/-- One original leading dictionary supplies the original frame chain and its expansion cost. -/
theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.readGroup_wire h

/-- Original V2 pages account separately for slots, row starts and zero-value slots. -/
theorem group_counts {limits : Limits} {checked : Checked} {ordinal spent : Nat} {rows : List Row}
    (h : GroupWire limits checked ordinal rows spent) :
    (∀ row ∈ rows, row.isSome = true) ∧
    ∃ chunk infos,
      ListFile.Multi.Snappy.DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = missingSlots (rows.flatMap ListPage.rowEvents) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.group_counts h

/-- The leading dictionary refusal retains original frame zero and offset. -/
theorem readGroup_dictionary_error {limits : Limits} {checked : Checked} {ordinal expanded : Nat}
    {chunk : Chunk} {cause : FrameError}
    (selected : selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.readGroup_dictionary_error selected slots rows failed

/-- A successful prefix fixes the first failing data or stitch frame coordinates. -/
theorem readGroup_data_error {limits : Limits} {checked : Checked} {ordinal expanded : Nat}
    {chunk : Chunk} {entries : List Int32} {before after : List Page.Frame} {frame : Page.Frame}
    {left : Budget} {state : State} {cause : FrameError}
    (selected : selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (dictionary : readEntries limits checked expanded chunk.dictionary = .ok entries)
    (ordered : chunk.firstData :: chunk.rest = before ++ frame :: after)
    (earlier : readFramesUsing (readFrame limits checked entries.toArray) 1
      ⟨chunk.framed.chunk.metadata.numValues.toNat, expanded - chunk.dictionary.value.uncompressedSize⟩
      State.empty before = .ok (left, state))
    (failed : readFrame limits checked entries.toArray left frame = .error cause ∨
      ∃ events error, readFrame limits checked entries.toArray left frame = .ok events ∧
        state.feed events = .error error ∧ cause = .page error) :
    readGroup limits checked ordinal expanded = .error (.frame (1 + before.length) frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.readGroup_data_error selected slots rows dictionary ordered earlier failed

/-- Retain earlier completed groups and the indexed source failure ahead of IPC admission. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.RequiredContainer.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsWith ListFile.RequiredContainer.SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.RequiredContainer.rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.convert_first_error opened split earlier failed

/-- The native required LIST preserves names and nullable children through exact EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.convert_readback h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

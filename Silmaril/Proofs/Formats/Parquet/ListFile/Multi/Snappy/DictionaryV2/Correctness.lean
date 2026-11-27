module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy (Budget)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1
  (Limits SourceError GroupError FrameError readValues)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2
open Silmaril.Relational
open ListPage (Event State Row)

private theorem checksum_extent {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status} (h : Page.Checksum.verify cap source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame ∧ frame.value.compressedSize ≤ cap := by
  cases status with
  | absent =>
    obtain ⟨size, within, _⟩ := Page.Checksum.verify_absent_iff.mp h
    exact ⟨within, size⟩
  | valid crc =>
    obtain ⟨size, within, _⟩ := Page.Checksum.verify_valid_iff.mp h
    exact ⟨within, size⟩

private theorem exactSpans {checked : ListFile.Checked} {frame : Page.Frame} {info : Page.DataV2}
    {source stored : Bytes} {sections : ListFile.Multi.Snappy.V2Sections}
    (kind : frame.value.kind = .dataV2 info)
    (extent : Page.Checksum.PayloadWithin source frame) (storedSize : stored.length = frame.value.compressedSize)
    (body : ListFile.Multi.Snappy.V2BodyWire checked frame info stored sections) :
    ∃ spans, frame.v2Spans = some spans ∧
      spans.repetition.stop - spans.repetition.start = info.repetitionBytes ∧
      spans.definition.stop - spans.definition.start = info.definitionBytes := by
  obtain ⟨suffix, _, exact, _, _, _, _, _⟩ := body.exact
  have size := congrArg List.length exact
  simp only [Bytes.length_toList, List.length_append, storedSize, body.repetitionSize, body.definitionSize] at size
  have payloadWidth := extent.2.2.1
  let repetition := frame.payload.start + info.repetitionBytes
  let definition := repetition + info.definitionBytes
  have stop : definition ≤ frame.payload.stop := by dsimp [definition, repetition]; omega
  exact ⟨⟨⟨frame.payload.start, repetition⟩, ⟨repetition, definition⟩, ⟨definition, frame.payload.stop⟩⟩,
    by
      unfold Page.Frame.v2Spans
      rw [kind]
      change (if definition ≤ frame.payload.stop then some _ else none) = _
      rw [ite_eq_left stop],
    by simp [repetition], by simp [definition]⟩

public theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked entries budget frame = .ok events) :
    FrameWire limits checked entries frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i encoding
    split at h
    · contradiction
    rename_i slots
    split at h
    · contradiction
    rename_i expanded
    simp only [Except.mapError, Bind.bind, Except.bind] at h
    cases checksum : Page.Checksum.verify limits.snappy.maxStoredPageBytes checked.snapshot.bytes frame with
    | error e => simp [checksum] at h
    | ok status =>
      simp only [checksum] at h
      cases prepared : ListFile.Multi.Snappy.prepareV2 limits.snappy checked frame info
          (Page.Checksum.payloadBytes checked.snapshot.bytes frame) with
      | error e => simp [prepared] at h
      | ok sections =>
        simp only [prepared] at h
        cases decoded : ListPage.decodeSectionsUsing FrameError.page (readValues limits entries)
            checked.limits.page info.numValues sections.repetition sections.definition sections.scalars with
        | error e => simp [decoded] at h
        | ok result =>
          simp only [decoded] at h
          cases counted : ListFile.Multi.Snappy.checkV2Counts info result with
          | error e => simp [counted] at h
          | ok done =>
            cases done
            simp only [counted] at h
            obtain rfl := Except.ok.inj h
            obtain ⟨extent, cap⟩ := checksum_extent checksum
            obtain ⟨slice, storedSize⟩ := Page.Checksum.payload_exact extent
            have body := ListFile.Multi.Snappy.prepareV2_wire prepared
            obtain ⟨spans, splits, repSize, defSize⟩ := exactSpans kind extent storedSize body
            obtain ⟨boundary, rows, nulls⟩ := ListFile.Multi.Snappy.checkV2Counts_wire counted
            have wire := ListPage.decodeSectionsUsing_wire decoded
            obtain ⟨reps, defs, values, slotsInOrder, _, _, repLen, defLen, entryLen, selected, mask, ordered, eventWire⟩ :=
              wire.data
            obtain ⟨count, valueOrder⟩ := ListFile.Multi.Snappy.sectionCounts repLen defLen entryLen mask eventWire
            have lookup := ListFile.Multi.Snappy.DictionaryV1.readValues_wire selected
            rw [count, nulls, ← ordered, ← valueOrder] at lookup
            exact ⟨⟨status, _, info, sections, spans, checksum, slice, storedSize, storedSize ▸ cap,
              kind, not_not.mp encoding, splits, repSize, defSize, body, wire, boundary, rows, nulls, lookup⟩,
              wire.slotCount ▸ Nat.le_of_not_gt slots, Nat.le_of_not_gt expanded⟩
  · contradiction

public theorem readFrame_checksum_error {limits : Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 8)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.snappy.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked entries budget frame = .error (.checksum cause) := by
  simp [readFrame, kind, encoding, Nat.not_lt.mpr slots, Nat.not_lt.mpr expanded, failed,
    Except.mapError, Bind.bind, Except.bind]

public theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  ListFile.Multi.Snappy.DictionaryV1.readGroupUsing_wire (read := dataReader limits)
    (witness := dataWitness limits) (fun proof => readFrame_wire proof) h

private theorem headerTotals {limits : Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {frames : List Page.Frame} {pages : List (List Event)}
    (h : List.Forall₂ (FrameWire limits checked entries) frames pages) :
    ∃ infos,
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) frames infos ∧
      (infos.map (·.numValues)).sum = pages.flatten.length ∧
      (infos.map (·.numRows)).sum = ListFile.Multi.Snappy.pageRows pages.flatten ∧
      (infos.map (·.numNulls)).sum = ListFile.Multi.Snappy.pageNulls pages.flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl, rfl, rfl⟩
  | cons single tail ih =>
    obtain ⟨_, _, info, _, _, _, _, _, _, kind, _, _, _, _, _, sections, _, rows, nulls, _⟩ := single.data
    obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := ih
    refine ⟨info :: infos, .cons kind all, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, valueTotal, sections.slotCount]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, rowTotal, ← rows,
        ListFile.Multi.Snappy.pageRows, List.countP_append]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, nullTotal, ← nulls,
        ListFile.Multi.Snappy.pageNulls, List.countP_append]

public theorem readGroup_counts {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    ∃ chunk infos,
      ListFile.Multi.Snappy.DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = ListFile.Multi.Snappy.pageNulls (rows.flatMap ListPage.rowEvents) := by
  obtain ⟨chunk, _, pages, original, _, pageWires, slots, count, _, events, _⟩ := (readGroup_wire h).1.data
  obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := headerTotals pageWires
  rw [← events, ListFile.Multi.Snappy.pageRows_of_rows, count] at rowTotal
  exact ⟨chunk, infos, original, all, valueTotal.trans slots, rowTotal, by simpa [events] using nullTotal⟩

public theorem readFrames_first_error {limits : Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {earlier rest : List Page.Frame} {frame : Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State} {cause : FrameError}
    (decoded : ListFile.Multi.Snappy.DictionaryV1.readFramesUsing (readFrame limits checked entries)
      ordinal budget state earlier = .ok (left, next))
    (failed : readFrame limits checked entries left frame = .error cause) :
    ListFile.Multi.Snappy.DictionaryV1.readFramesUsing (readFrame limits checked entries)
      ordinal budget state (earlier ++ frame :: rest) =
      .error (.frame (ordinal + earlier.length) frame.header.start cause) := by
  rw [ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_append decoded]
  exact ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_read_error failed

public theorem readGroup_dictionary_error {limits : Limits} {checked : ListFile.Checked} {ordinal expanded : Nat}
    {chunk : ListFile.Multi.Snappy.DictionaryV1.Chunk} {cause : FrameError}
    (selected : ListFile.Multi.Snappy.DictionaryV1.selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : ListFile.Multi.Snappy.DictionaryV1.readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) := by
  simp [readGroup, ListFile.Multi.Snappy.DictionaryV1.readGroupUsing, selected,
    Nat.not_lt.mpr slots, Nat.not_lt.mpr rows, failed, Except.mapError, Bind.bind, Except.bind]

public theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsWith SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  ListFile.Multi.Snappy.convertWith_first_error (errors := ListFile.Multi.Snappy.DictionaryV1.errors)
    opened split earlier failed

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  ListFile.Multi.Snappy.convertWith_readback (errors := ListFile.Multi.Snappy.DictionaryV1.errors)
    (read := readGroup limits) (witness := GroupWire limits) (fun proof => readGroup_wire proof) h

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

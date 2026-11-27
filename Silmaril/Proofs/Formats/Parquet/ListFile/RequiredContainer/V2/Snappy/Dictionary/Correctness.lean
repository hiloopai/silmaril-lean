module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary.Defs
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open ListPage (Event Row State)
open ListFile.RequiredContainer (Checked)
open ListFile.RequiredContainer.V2 (rowStarts missingSlots sections_values event_counts_using rowStarts_of_rows)
open ListFile.RequiredContainer.V2.Snappy (StoredWire readSections_wire)
open ListFile.RequiredContainer.V2.Snappy.Dictionary
open ListFile.Multi.Snappy (Budget)
open ListFile.Multi.Snappy.DictionaryV1 (LookupWire Chunk selectChunk readEntries readFramesUsing readValues)

public theorem readFrame_wire {limits : Limits} {checked : Checked} {entries : Array Int32}
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
    split at h
    · contradiction
    rename_i rows
    simp only [Bind.bind, Except.bind] at h
    cases prepared : ListFile.RequiredContainer.V2.Snappy.readSections (bodyLimits limits) checked frame info with
    | error err => simp [prepared, Except.mapError] at h
    | ok sections =>
      simp only [prepared, Except.mapError] at h
      cases decoded : ListFile.RequiredContainer.decodeSectionsUsing ListFile.Multi.Snappy.DictionaryV1.FrameError.page (readValues limits entries)
          checked.limits.page info.numValues sections.repetition sections.definition sections.scalars with
      | error err => simp [decoded] at h
      | ok output =>
        simp only [decoded] at h
        cases counts : ListFile.Multi.Snappy.checkV2Counts info output with
        | error err => simp [counts] at h
        | ok done =>
          cases done
          simp only [counts] at h
          obtain rfl := Except.ok.inj h
          have physical := ListFile.RequiredContainer.decodeSectionsUsing_wire decoded
          obtain ⟨boundary, rowCount, absent⟩ := ListFile.Multi.Snappy.checkV2Counts_wire counts
          have lookup := sections_values physical
          change missingSlots output = info.numNulls at absent
          rw [absent] at lookup
          exact ⟨⟨info, sections, kind, not_not.mp encoding, Nat.le_of_not_gt rows,
            readSections_wire kind prepared, physical, boundary, rowCount, absent,
            ListFile.Multi.Snappy.DictionaryV1.readValues_wire lookup⟩,
            physical.count ▸ Nat.le_of_not_gt slots, Nat.le_of_not_gt expanded⟩
  · contradiction

public theorem frame_levels {limits : Limits} {checked : Checked} {entries : Array Int32}
    {frame : Page.Frame} {events : List Event} (h : FrameWire limits checked entries frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire (bodyLimits limits) checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧
      LookupWire limits entries (info.numValues - info.numNulls) sections.scalars
        (events.filterMap (fun event => event.wire.2.2)) := by
  obtain ⟨info, sections, kind, _, _, stored, physical, boundary, rows, nulls, lookup⟩ := h.data
  obtain ⟨reps, defs, repWire, defWire, repLength, defLength, rowTotal, nullTotal, ordered⟩ :=
    event_counts_using physical rows nulls
  refine ⟨info, sections, reps, defs, kind, stored, repWire, defWire, repLength, defLength, ?_,
    rowTotal, nullTotal, lookup⟩
  rw [← ordered]
  cases events with
  | nil => exact Or.inl rfl
  | cons event tail =>
    cases event with
    | nullList => exact Or.inr rfl
    | emptyList => exact Or.inr rfl
    | first item => exact Or.inr rfl
    | next item => contradiction

public theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  ListFile.Multi.Snappy.DictionaryV1.readGroupUsing_wire
    (read := fun checked _ => readFrame limits checked)
    (witness := fun checked _ => FrameWire limits checked) (fun proof => readFrame_wire proof) h

public theorem group_counts {limits : Limits} {checked : Checked} {ordinal spent : Nat} {rows : List Row}
    (h : GroupWire limits checked ordinal rows spent) :
    (∀ row ∈ rows, row.isSome = true) ∧
    ∃ chunk infos,
      ListFile.Multi.Snappy.DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = missingSlots (rows.flatMap ListPage.rowEvents) := by
  obtain ⟨chunk, entries, pages, original, _, evidence, slots, rowCount, _, ordered, _⟩ := h.data
  have counted (frame : Page.Frame) (events : List Event) (wire : FrameWire limits checked entries.toArray frame events) :
      ListFile.RequiredContainer.V2.Multi.CountedFrame frame events := by
    obtain ⟨_, _, kind, _, _, _, sections, _, rows, nulls, _⟩ := wire.data
    exact ListFile.RequiredContainer.V2.Multi.countedFrame kind sections rows nulls
  obtain ⟨infos, kinds, slotSum, rowSum, nullSum, present⟩ :=
    ListFile.RequiredContainer.V2.Multi.frameTotals (List.Forall₂.imp counted evidence)
  refine ⟨?_, chunk, infos, original, kinds, slotSum.trans slots, ?_, ?_⟩
  · intro row member
    cases row with
    | some items => rfl
    | none =>
      have invalid : Event.nullList ∈ pages.flatten := by
        rw [← ordered]
        exact List.mem_flatMap.mpr ⟨none, member, by simp [ListPage.rowEvents]⟩
      exact (present invalid).elim
  · rw [rowSum, ← ordered, rowStarts_of_rows, rowCount]
  · rw [nullSum, ordered]

public theorem readGroup_dictionary_error {limits : Limits} {checked : Checked} {ordinal expanded : Nat}
    {chunk : Chunk} {cause : FrameError}
    (selected : selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) := by
  simp [readGroup, ListFile.Multi.Snappy.DictionaryV1.readGroupUsing,
    ListFile.Multi.Snappy.DictionaryV1.readGroupWith, ListFile.Multi.Snappy.DictionaryV1.readSelectedGroupWith,
    selected, Nat.not_lt.mpr slots, Nat.not_lt.mpr rows, failed, Except.mapError, Bind.bind, Except.bind]

public theorem readGroup_data_error {limits : Limits} {checked : Checked} {ordinal expanded : Nat}
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
    readGroup limits checked ordinal expanded = .error (.frame (1 + before.length) frame.header.start cause) := by
  have prefixStep := ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_append (suffix := frame :: after) earlier
  simp only [readGroup, ListFile.Multi.Snappy.DictionaryV1.readGroupUsing,
    ListFile.Multi.Snappy.DictionaryV1.readGroupWith, ListFile.Multi.Snappy.DictionaryV1.readSelectedGroupWith,
    selected, Nat.not_lt.mpr slots, Nat.not_lt.mpr rows, ite_false, dictionary, Except.mapError, Bind.bind,
    Except.bind, ordered, prefixStep]
  rcases failed with decoded | ⟨events, error, decoded, feed, rfl⟩
  · simp [readFramesUsing, decoded, Except.mapError, Bind.bind, Except.bind]
  · simp [readFramesUsing, decoded, feed, Except.mapError, Bind.bind, Except.bind]

public theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.RequiredContainer.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsWith ListFile.RequiredContainer.SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.RequiredContainer.rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) := by
  simp [convert, opened, split, ListFile.Multi.Snappy.readGroupsWith_append earlier,
    ListFile.Multi.Snappy.readGroupsWith, failed]

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire := by
  cases opened : ListFile.RequiredContainer.openFile limits.snappy.parquet.file source with
  | error cause => simp [convert, opened] at h
  | ok checked =>
    cases read : ListFile.Multi.Snappy.readGroupsWith ListFile.RequiredContainer.SourceError.groupFailure (readGroup limits) checked
        limits.snappy.maxExpandedBytes (List.range checked.snapshot.groupCount) with
    | mk groups outcome =>
      cases outcome with
      | error cause => simp [convert, opened, read] at h
      | ok left =>
        simp only [convert, opened, read] at h
        cases emitted : Arrow.ListInt32.Stream.Writer.emitFor false limits.snappy.ipc
            (ListFile.RequiredContainer.fieldOf checked) groups with
        | error cause => simp [emitted, Except.mapError] at h
        | ok bytes =>
          obtain rfl := Except.ok.inj (by simpa only [emitted, Except.mapError] using h)
          obtain ⟨costs, original, costCount, cap⟩ :=
            ListFile.Multi.Snappy.readGroupsWith_wire (witness := GroupWire limits)
              (fun result => readGroup_wire result) read
          obtain ⟨decoded, size, native, agrees, wf, envelope, descriptor, batches, parents⟩ :=
            Arrow.ListInt32.Stream.Writer.emitFor_readback emitted
          exact ⟨checked, groups, costs, left, decoded, size, opened, ListFile.openFileFor_wire opened, read,
            original, costCount, cap, by simp [convert, opened, read],
            native, agrees, wf, envelope, descriptor, batches, parents⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

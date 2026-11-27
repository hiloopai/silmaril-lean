module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy
open Silmaril.Relational
open ListPage (Event State Row)

private theorem checksum_extent {limit : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status}
    (h : Page.Checksum.verify limit source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent => exact (Page.Checksum.verify_absent_iff.mp h).2.1
  | valid crc => exact (Page.Checksum.verify_valid_iff.mp h).2.1

public theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events) :
    FrameWire limits checked column frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    · rename_i encoding
      push Not at encoding
      split at h
      · contradiction
      · rename_i slots
        split at h
        · contradiction
        · rename_i expanded
          simp only [Except.mapError, Bind.bind, Except.bind] at h
          let source := checked.snapshot.bytes
          let stored := Page.Checksum.payloadBytes source frame
          cases checksum : Page.Checksum.verify limits.maxStoredPageBytes source frame with
          | error e => simp [source, checksum] at h
          | ok status =>
            simp only [source, checksum] at h
            cases decoded : Payload.decode (bounds limits checked budget frame) 1 stored.toList with
            | error e =>
              simp only [stored, source] at decoded
              simp [decoded] at h
            | ok output =>
              simp only [stored, source] at decoded
              simp only [decoded] at h
              cases decodedEvents : ListPage.decodeEvents checked.limits.page info.numValues (Bytes.ofList output) with
              | error e => simp [decodedEvents] at h
              | ok result =>
                simp only [decodedEvents] at h
                split at h
                · contradiction
                · rename_i boundary
                  obtain rfl := Except.ok.inj h
                  obtain ⟨codec, selected, denotes, _, storedCap, exact, _⟩ := Payload.decode_sound decoded
                  change some Payload.Codec.snappy = some codec at selected
                  obtain rfl := Option.some.inj selected
                  obtain ⟨slice, storedSize⟩ := Page.Checksum.payload_exact (checksum_extent checksum)
                  have wire := ListPage.decodeEvents_wire decodedEvents
                  refine ⟨⟨⟨status, stored, Bytes.ofList output, info, checksum, slice, storedSize,
                    storedCap, ?_, ?_, kind, encoding, wire⟩, ?_⟩, ?_, Nat.le_of_not_gt expanded⟩
                  · simpa [bounds] using denotes
                  · simpa [bounds] using exact
                  · intro indexed
                    simpa [indexed] using boundary
                  · rw [wire.slotCount]
                    exact Nat.le_of_not_gt slots
  · contradiction

public theorem readFrame_checksum_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV1} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV1 info)
    (encoding : info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked column budget frame = .error (.checksum cause) := by
  simp [readFrame, kind, encoding, Nat.not_lt.mpr slots, Nat.not_lt.mpr expanded, failed,
    Except.mapError, Bind.bind, Except.bind]

public theorem prepareV2_wire {container : ListFile.Container} {limits : Limits}
    {checked : ListFile.Checked container}
    {frame : Page.Frame} {info : Page.DataV2} {stored : Bytes} {sections : V2Sections}
    (h : prepareV2 limits checked frame info stored = .ok sections) :
    V2BodyWire checked frame info stored sections := by
  unfold prepareV2 at h
  dsimp only at h
  split at h
  · contradiction
  rename_i extent
  push Not at extent
  obtain ⟨storedSize, compressedFits, expandedFits⟩ := extent
  split at h
  · contradiction
  rename_i levelCap
  push Not at levelCap
  split at h
  · contradiction
  rename_i bodyCap
  let afterRep := stored.toList.drop info.repetitionBytes
  cases decoded : Payload.decode (v2Bounds limits checked frame info)
      (v2Codec info) (afterRep.drop info.definitionBytes) with
  | error e =>
    simp only [afterRep] at decoded
    simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
    contradiction
  | ok output =>
    simp only [afterRep] at decoded
    simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
    obtain rfl := Except.ok.inj h
    obtain ⟨codec, id, wire, inputLen, _, expandedLen, _⟩ := Payload.decode_sound decoded
    have inputSize : stored.toList.length = frame.value.compressedSize := by simpa using storedSize
    have repFits : info.repetitionBytes ≤ stored.toList.length := by
      unfold v2LevelBytes at compressedFits
      omega
    have defFits : info.definitionBytes ≤ afterRep.length := by
      simp only [afterRep, List.length_drop]
      unfold v2LevelBytes at compressedFits
      omega
    change output.length = frame.value.uncompressedSize - v2LevelBytes info at expandedLen
    refine ⟨?_, ?_, levelCap.1, levelCap.2, Nat.le_of_not_gt bodyCap,
      afterRep.drop info.definitionBytes, codec, ?_, inputLen, ?_, ?_, id, ?_⟩
    · exact (Bytes.length_ofList _).trans ((List.length_take).trans (Nat.min_eq_left repFits))
    · exact (Bytes.length_ofList _).trans ((List.length_take).trans (Nat.min_eq_left defFits))
    · simp only [Bytes.toList_ofList]
      rw [List.append_assoc]
      change stored.toList = stored.toList.take info.repetitionBytes ++
        (afterRep.take info.definitionBytes ++ afterRep.drop info.definitionBytes)
      rw [List.take_append_drop]
      exact (List.take_append_drop info.repetitionBytes stored.toList).symm
    · simpa only [Bytes.length_ofList] using expandedLen
    · rw [Bytes.length_ofList, expandedLen]
      exact Nat.add_sub_of_le expandedFits
    · exact (Bytes.toList_ofList output).symm ▸ wire

private theorem optionCounts {α : Type} (entries : List (Option α)) :
    entries.countP Option.isSome + entries.countP Option.isNone = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases entry <;> simp <;> omega

public theorem sectionCounts {slots : Nat} {events : List Event} {reps defs : List Nat}
    {entries : List (Option Int32)}
    (repLen : reps.length = slots) (defLen : defs.length = slots) (entryLen : entries.length = slots)
    (mask : entries.map Option.isSome = ListPage.valueMask defs)
    (eventsEq : events.map Event.wire = reps.zip (defs.zip entries)) :
    (ListPage.valueMask defs).count true = slots - pageNulls events ∧
      events.filterMap (fun event => event.wire.2.2) = entries.filterMap id := by
  have outer : (defs.zip entries).length ≤ reps.length := by simp [defLen, entryLen, repLen]
  have inner : entries.length ≤ defs.length := by simp [entryLen, defLen]
  have slotsEq : events.map (fun event => event.wire.2.2) = entries := by
    calc
      _ = ((events.map Event.wire).map Prod.snd).map Prod.snd := by simp [List.map_map, Function.comp_def]
      _ = entries := by rw [eventsEq, List.map_snd_zip outer, List.map_snd_zip inner]
  have nulls : pageNulls events = entries.countP Option.isNone := by
    rw [← slotsEq, List.countP_map]
    rfl
  have present : (ListPage.valueMask defs).count true = entries.countP Option.isSome := by
    rw [← mask, List.count_eq_countP, List.countP_map]
    simp [Function.comp_def]
  have partition := optionCounts entries
  refine ⟨by omega, ?_⟩
  simpa [List.filterMap_map, Function.comp_def] using congrArg (List.filterMap id) slotsEq

private theorem scalarBytes {slots : Nat} {rep defn scalars : Bytes} {events : List Event}
    (wire : ListPage.SectionsWire slots rep defn scalars events) :
    scalars.length = 4 * (slots - pageNulls events) := by
  obtain ⟨_, reps, defs, values, entries, _, _, repLen, defLen, entryLen,
    plain, mask, _, eventsEq⟩ := wire
  have count := (sectionCounts repLen defLen entryLen mask eventsEq).1
  change Plain.decodeFixedWidth 4 _ _ scalars = .ok values at plain
  unfold Plain.decodeFixedWidth at plain
  simp only [Nat.reduceEqDiff, ite_false] at plain
  split at plain
  · contradiction
  split at plain
  · contradiction
  omega

public theorem checkV2Counts_wire {info : Page.DataV2} {events : List Event}
    (h : checkV2Counts info events = .ok ()) :
    ListFile.Multi.startsWithinRow events = false ∧ pageRows events = info.numRows ∧ pageNulls events = info.numNulls := by
  unfold checkV2Counts at h
  split at h
  · contradiction
  rename_i boundary
  split at h
  · contradiction
  rename_i rows
  split at h
  · contradiction
  rename_i nulls
  exact ⟨Bool.eq_false_iff.mpr boundary, not_not.mp rows, not_not.mp nulls⟩

public theorem readV2Frame_wire {limits : Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readV2Frame limits checked budget frame = .ok events) :
    V2FrameWire limits checked frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  unfold readV2Frame at h
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
    cases checksum : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame with
    | error e => simp [checksum] at h
    | ok status =>
      simp only [checksum] at h
      cases prepared : prepareV2 limits checked frame info
          (Page.Checksum.payloadBytes checked.snapshot.bytes frame) with
      | error e => simp [prepared] at h
      | ok sections =>
        simp only [prepared] at h
        cases decoded : ListPage.decodeSections checked.limits.page info.numValues
            sections.repetition sections.definition sections.scalars with
        | error e => simp [decoded] at h
        | ok result =>
          simp only [decoded] at h
          cases counted : checkV2Counts info result with
          | error e => simp [counted] at h
          | ok done =>
            cases done
            simp only [counted] at h
            obtain rfl := Except.ok.inj h
            have extent := checksum_extent checksum
            obtain ⟨slice, storedSize⟩ := Page.Checksum.payload_exact extent
            have cap : frame.value.compressedSize ≤ limits.maxStoredPageBytes := by
              cases status with
              | absent => exact (Page.Checksum.verify_absent_iff.mp checksum).1
              | valid crc => exact (Page.Checksum.verify_valid_iff.mp checksum).1
            obtain ⟨boundary, rowCount, nullCount⟩ := checkV2Counts_wire counted
            have wire := ListPage.decodeSections_wire decoded
            exact ⟨⟨status, _, info, sections, checksum, slice, storedSize, storedSize ▸ cap,
              kind, not_not.mp encoding, prepareV2_wire prepared, wire, boundary,
              rowCount, nullCount, by simpa [nullCount] using scalarBytes wire⟩,
              wire.slotCount ▸ Nat.le_of_not_gt slots, Nat.le_of_not_gt expanded⟩
  · contradiction

public theorem readV2Frame_checksum_error {limits : Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 0)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readV2Frame limits checked budget frame = .error (.checksum cause) := by
  simp [readV2Frame, kind, encoding, Nat.not_lt.mpr slots, Nat.not_lt.mpr expanded, failed,
    Except.mapError, Bind.bind, Except.bind]

private theorem readFrameFor_wire {version : PageVersion} {limits : Limits} {checked : ListFile.Checked}
    {column : Footer.ColumnChunk} {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrameFor version limits checked column budget frame = .ok events) :
    FrameWireFor version limits checked column frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  cases version with
  | v1 => exact readFrame_wire h
  | v2 => exact readV2Frame_wire h

public theorem readFramesFor_wire {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFramesFor version limits checked column ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWireFor version limits checked column) frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  induction frames generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨[], .nil, by simp, by simp [expandedSize], ListPage.feed_nil state, by simp⟩
  | cons frame rest ih =>
    rw [readFramesFor] at h
    cases read : readFrameFor version limits checked column budget frame with
    | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at h
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h
        obtain ⟨pages, wire, count, bytes, nextFed, _⟩ := ih h
        obtain ⟨page, slotBound, byteBound⟩ := readFrameFor_wire read
        have combined : state.feed (events ++ pages.flatten) = .ok next := by
          rw [ListPage.feed_append, fed]
          exact nextFed
        refine ⟨events :: pages, .cons page wire, ?_, ?_, combined, ListPage.feed_wire combined⟩
        · simp only [List.flatten_cons, List.length_append, Budget.use] at count ⊢
          omega
        · simp only [expandedSize, List.map_cons, List.sum_cons, Budget.use] at bytes ⊢
          omega

private theorem readFramedGroupUsing_checked {limits : Limits} {checked : ListFile.Checked} {walk : GroupWalk}
    {framed : ListFile.FramedGroup} {expanded left : Nat} {rows : List Row}
    (h : readFramedGroupUsing limits checked walk framed expanded = .ok (rows, left)) :
    ∃ budget state,
      walk framed.chunk ⟨framed.chunk.metadata.numValues.toNat, expanded⟩ framed.frames = .ok (budget, state) ∧
      budget.slots = 0 ∧ budget.expanded = left ∧ state.finish = rows ∧
      rows.length = framed.group.numRows.toNat ∧
      framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
      framed.group.numRows.toNat ≤ checked.limits.page.maxRows := by
  unfold readFramedGroupUsing at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i slotCap
    split at h
    · contradiction
    · rename_i rowCap
      cases read : walk framed.chunk ⟨framed.chunk.metadata.numValues.toNat, expanded⟩ framed.frames with
      | error e => simp [read, Bind.bind, Except.bind] at h
      | ok result =>
        obtain ⟨budget, state⟩ := result
        simp only [read, Bind.bind, Except.bind] at h
        split at h
        · contradiction
        · rename_i noSurplus
          push Not at noSurplus
          split at h
          · contradiction
          · rename_i rowCount
            push Not at rowCount
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
            exact ⟨budget, state, rfl, noSurplus, rfl, rfl,
              rowCount, Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩

public theorem readGroupUsing_checked {limits : Limits} {checked : ListFile.Checked} {walk : GroupWalk}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroupUsing limits checked walk ordinal expanded = .ok (rows, left)) :
    ∃ framed budget state,
      ListFile.FramedGroupWire checked ordinal framed 1 ∧
      walk framed.chunk ⟨framed.chunk.metadata.numValues.toNat, expanded⟩ framed.frames = .ok (budget, state) ∧
      budget.slots = 0 ∧ budget.expanded = left ∧ state.finish = rows ∧
      rows.length = framed.group.numRows.toNat ∧
      framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
      framed.group.numRows.toNat ≤ checked.limits.page.maxRows := by
  unfold readGroupUsing at h
  cases selected : checked.frameGroupFor 1 ordinal with
  | error e => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    obtain ⟨budget, state, facts⟩ := readFramedGroupUsing_checked h
    exact ⟨framed, budget, state, ListFile.frameGroupFor_wire selected, facts⟩

public theorem readFramedGroupFor_wire {version : PageVersion} {limits : Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {framed : ListFile.FramedGroup} {rows : List Row}
    (origin : ListFile.FramedGroupWire checked ordinal framed 1)
    (h : readFramedGroupFor version limits checked framed expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) version ∧ left ≤ expanded := by
  obtain ⟨budget, state, read, noSurplus, remaining, rfl, rowCount, slotCap, rowCap⟩ :=
    readFramedGroupUsing_checked (walk := fun column budget => readFramesFor version limits checked column 0 budget State.empty) h
  obtain ⟨pages, wire, count, bytes, fed, order⟩ := readFramesFor_wire read
  change pages.flatten.length + budget.slots = _ at count
  change expandedSize framed.frames + budget.expanded = expanded at bytes
  exact ⟨⟨framed, pages, origin, wire, by simpa [noSurplus] using count, rowCount,
    ListPage.reconstruct_of_feed fed, by simpa [ListPage.finish_empty] using order, slotCap, rowCap, by omega⟩, by omega⟩

public theorem readGroupFor_wire {version : PageVersion} {limits : Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroupFor version limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) version ∧ left ≤ expanded := by
  unfold readGroupFor readGroupUsing at h
  cases selected : checked.frameGroupFor 1 ordinal with
  | error cause => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    exact readFramedGroupFor_wire (ListFile.frameGroupFor_wire selected) h

public theorem pageRows_of_rows (rows : List Row) :
    pageRows (rows.flatMap ListPage.rowEvents) = rows.length := by
  have one (row : Row) : pageRows (ListPage.rowEvents row) = 1 := by
    cases row with
    | none => rfl
    | some items =>
      cases items with
      | nil => rfl
      | cons item tail =>
        simp [pageRows, ListPage.rowEvents, ListPage.Event.wire, Function.comp_def]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [List.flatMap_cons]
    change (ListPage.rowEvents row ++ rest.flatMap ListPage.rowEvents).countP _ = rest.length + 1
    rw [List.countP_append]
    change pageRows (ListPage.rowEvents row) + pageRows (rest.flatMap ListPage.rowEvents) = rest.length + 1
    rw [one row, ih]
    omega

private theorem v2HeaderTotals {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frames : List Page.Frame} {pages : List (List Event)}
    (h : List.Forall₂ (FrameWireFor .v2 limits checked column) frames pages) :
    ∃ infos,
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) frames infos ∧
      (infos.map (·.numValues)).sum = pages.flatten.length ∧
      (infos.map (·.numRows)).sum = pageRows pages.flatten ∧
      (infos.map (·.numNulls)).sum = pageNulls pages.flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl, rfl, rfl⟩
  | cons single rest ih =>
    obtain ⟨_, _, info, _, _, _, _, _, kind, _, _, slots, _, rows, nulls, _⟩ := single.data
    obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := ih
    refine ⟨info :: infos, .cons kind all, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, valueTotal, slots.slotCount]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, rowTotal, ← rows, pageRows, List.countP_append]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, nullTotal, ← nulls, pageNulls, List.countP_append]

public theorem readV2Group_counts {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroupFor .v2 limits checked ordinal expanded = .ok (rows, left)) :
    ∃ framed infos,
      ListFile.FramedGroupWire checked ordinal framed 1 ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) framed.frames infos ∧
      (infos.map (·.numValues)).sum = framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = pageNulls (rows.flatMap ListPage.rowEvents) := by
  obtain ⟨framed, pages, framedWire, pageWires, slots, count, _, events, _⟩ := (readGroupFor_wire h).1.data
  obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := v2HeaderTotals pageWires
  rw [← events, pageRows_of_rows, count] at rowTotal
  exact ⟨framed, infos, framedWire, all, valueTotal.trans slots, rowTotal, by simpa [events] using nullTotal⟩

public theorem readFramesFor_append {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {budget left : Budget} {state next : State}
    (h : readFramesFor version limits checked column ordinal budget state earlier = .ok (left, next)) :
    readFramesFor version limits checked column ordinal budget state (earlier ++ suffix) =
      readFramesFor version limits checked column (ordinal + earlier.length) left next suffix := by
  induction earlier generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    simp
  | cons frame rest ih =>
    rw [readFramesFor] at h
    rw [List.cons_append, readFramesFor]
    cases read : readFrameFor version limits checked column budget frame with
    | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at h ⊢
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h ⊢
        simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using ih h

public theorem readFramesFor_read_error {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrameFor version limits checked column budget frame = .error cause) :
    readFramesFor version limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) := by
  simp [readFramesFor, h, Except.mapError, Bind.bind, Except.bind]

public theorem readFramesFor_feed_error {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : readFrameFor version limits checked column budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFramesFor version limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) := by
  simp [readFramesFor, decoded, failed, Except.mapError, Bind.bind, Except.bind]

private theorem readGroupsWith_wire {ε σ : Type} {wrap : Nat → ε → σ} {read : GroupReaderFor ε}
    {witness : ListFile.Checked → Nat → List Row → Nat → Prop} {checked : ListFile.Checked} {indices : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (sound : ∀ {checked ordinal expanded left rows}, read checked ordinal expanded = .ok (rows, left) →
      witness checked ordinal rows (expanded - left) ∧ left ≤ expanded)
    (h : readGroupsWith wrap read checked expanded indices = (groups, .ok left)) :
    ∃ costs,
      List.Forall₂ (fun ordinal (batch : List Row × Nat) => witness checked ordinal batch.1 batch.2)
        indices (groups.zip costs) ∧
      costs.length = groups.length ∧ costs.sum + left = expanded := by
  induction indices generalizing expanded groups with
  | nil =>
    obtain ⟨rfl, same⟩ := Prod.mk.inj h
    obtain rfl := Except.ok.inj same
    exact ⟨[], .nil, rfl, by simp⟩
  | cons ordinal rest ih =>
    rw [readGroupsWith] at h
    cases group : read checked ordinal expanded with
    | error e => simp [group] at h
    | ok result =>
      obtain ⟨rows, remaining⟩ := result
      simp only [group] at h
      cases tailRead : readGroupsWith wrap read checked remaining rest with
      | mk tail outcome =>
        rw [tailRead] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨costs, wire, counts, budget⟩ := ih tailRead
        obtain ⟨groupWire, bound⟩ := sound group
        refine ⟨(expanded - remaining) :: costs, .cons groupWire wire, by simp [counts], ?_⟩
        simp only [List.sum_cons]
        omega

public theorem readGroupsWith_append {ε σ : Type} {wrap : Nat → ε → σ} {read : GroupReaderFor ε} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroupsWith wrap read checked expanded before = (groups, .ok left)) :
    readGroupsWith wrap read checked expanded (before ++ after) =
      let tail := readGroupsWith wrap read checked left after
      (groups ++ tail.1, tail.2) := by
  induction before generalizing expanded groups with
  | nil =>
    obtain ⟨rfl, same⟩ := Prod.mk.inj h
    obtain rfl := Except.ok.inj same
    simp
  | cons ordinal rest ih =>
    rw [readGroupsWith] at h
    rw [List.cons_append, readGroupsWith]
    cases group : read checked ordinal expanded with
    | error e => simp [group] at h
    | ok result =>
      obtain ⟨rows, remaining⟩ := result
      simp only [group] at h ⊢
      cases tailRead : readGroupsWith wrap read checked remaining rest with
      | mk tail outcome =>
        rw [tailRead] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [ih tailRead]
        rfl

public theorem convertWith_first_error {ε σ ρ : Type} {errors : ConversionErrors ε σ ρ}
    {read : GroupReaderFor ε} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : ε}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsWith errors.groupFailure read checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : read checked ordinal left = .error cause) :
    (convertWith errors limits read source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (errors.groupFailure ordinal cause)⟩⟩ ∧
    (convertWith errors limits read source).wire = .error (errors.sourceFailure (errors.groupFailure ordinal cause)) := by
  unfold convertWith
  rw [opened]
  simp only [split, readGroupsWith_append earlier, readGroupsWith, failed, List.append_nil, and_self]

public theorem convertWith_readback {ε σ ρ : Type} {errors : ConversionErrors ε σ ρ}
    {read : GroupReaderFor ε} {limits : Limits}
    {witness : ListFile.Checked → Nat → List Row → Nat → Prop} {source : Bytes} {wire : KBytes}
    (sound : ∀ {checked ordinal expanded left rows}, read checked ordinal expanded = .ok (rows, left) →
      witness checked ordinal rows (expanded - left) ∧ left ≤ expanded)
    (h : (convertWith errors limits read source).wire = .ok wire) : ReadbackWith errors limits read witness source wire := by
  cases opened : ListFile.openFile limits.parquet.file source with
  | error e => simp [convertWith, opened] at h
  | ok checked =>
    cases groupsRead : readGroupsWith errors.groupFailure read checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount) with
    | mk groups outcome =>
      cases outcome with
      | error e => simp [convertWith, opened, groupsRead] at h
      | ok left =>
        simp only [convertWith, opened, groupsRead] at h
        cases written : Arrow.ListInt32.Stream.Writer.emit limits.ipc (ListFile.Multi.ToIpc.fieldOf checked) groups with
        | error e => simp [written, Except.mapError] at h
        | ok bytes =>
          obtain rfl := Except.ok.inj (by simpa only [written, Except.mapError] using h)
          obtain ⟨costs, witness, count, cap⟩ := readGroupsWith_wire (read := read) (witness := witness) (fun hp => sound hp) groupsRead
          obtain ⟨decoded, size, read, agrees, wf, envelope, schema, batches⟩ :=
            Arrow.ListInt32.Stream.Writer.emit_readback written
          exact ⟨checked, groups, costs, left, decoded, size, opened, ListFile.openFile_wire opened,
            groupsRead, witness, count, cap, by simp [convertWith, opened, groupsRead],
            read, agrees, wf, envelope, schema, batches⟩

public theorem readGroupsUsing_append {read : GroupReader} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroupsUsing read checked expanded before = (groups, .ok left)) :
    readGroupsUsing read checked expanded (before ++ after) =
      let tail := readGroupsUsing read checked left after
      (groups ++ tail.1, tail.2) :=
  readGroupsWith_append (wrap := SourceError.groupFailure) h

public theorem convertUsing_first_error {read : GroupReader} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsUsing read checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : read checked ordinal left = .error cause) :
    (convertUsing limits read source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convertUsing limits read source).wire = .error (.source (.groupFailure ordinal cause)) :=
  convertWith_first_error (errors := standardErrors) opened split earlier failed

public theorem convertUsing_readback {read : GroupReader} {limits : Limits}
    {witness : ListFile.Checked → Nat → List Row → Nat → Prop} {source : Bytes} {wire : KBytes}
    (sound : ∀ {checked ordinal expanded left rows}, read checked ordinal expanded = .ok (rows, left) →
      witness checked ordinal rows (expanded - left) ∧ left ≤ expanded)
    (h : (convertUsing limits read source).wire = .ok wire) : ReadbackUsing limits read witness source wire :=
  ⟨(convertWith_readback (errors := standardErrors) (read := read) (witness := witness) (fun proof => sound proof) h).data⟩

public theorem readGroupsFor_append {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroupsFor version limits checked expanded before = (groups, .ok left)) :
    readGroupsFor version limits checked expanded (before ++ after) =
      let tail := readGroupsFor version limits checked left after
      (groups ++ tail.1, tail.2) :=
  readGroupsUsing_append (read := readGroupFor version limits) h

public theorem convertFor_first_error {version : PageVersion} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsFor version limits checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroupFor version limits checked ordinal left = .error cause) :
    (convertFor version limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convertFor version limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  convertUsing_first_error (read := readGroupFor version limits) opened split earlier failed

public theorem convertFor_readback {version : PageVersion} {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convertFor version limits source).wire = .ok wire) : Readback limits source wire version :=
  ⟨(convertUsing_readback (read := readGroupFor version limits)
    (witness := fun checked ordinal rows spent => GroupWire limits checked ordinal rows spent version)
    (fun proof => readGroupFor_wire proof) h).data⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy

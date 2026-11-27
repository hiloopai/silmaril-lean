module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Payload.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy (Budget expandedSize)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1
open Silmaril.Relational
open ListPage (Event State Row)

private theorem checksum_extent {storedCap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status}
    (h : Page.Checksum.verify storedCap source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent => exact (Page.Checksum.verify_absent_iff.mp h).2.1
  | valid crc => exact (Page.Checksum.verify_valid_iff.mp h).2.1

public theorem expand_wire {storedCap expandedCap : Nat} {source : Bytes} {frame : Page.Frame}
    {expanded : Bytes} (h : expand storedCap expandedCap source frame = .ok expanded) :
    ExpandedWire storedCap expandedCap source frame expanded := by
  unfold expand at h
  cases checksum : Page.Checksum.verify storedCap source frame with
  | error e => simp [checksum, Except.mapError, Bind.bind, Except.bind] at h
  | ok status =>
    simp only [checksum, Except.mapError, Bind.bind, Except.bind] at h
    let bounds : Payload.Bounds :=
      ⟨frame.value.compressedSize, storedCap, frame.value.uncompressedSize, expandedCap, 0⟩
    let stored := Page.Checksum.payloadBytes source frame
    cases decoded : Payload.decode bounds 1 stored.toList with
    | error e =>
      simp only [bounds, stored] at decoded
      simp [decoded] at h
    | ok bytes =>
      simp only [bounds, stored] at decoded
      simp only [decoded] at h
      obtain rfl := Except.ok.inj h
      obtain ⟨slice, exactSize⟩ := Page.Checksum.payload_exact (checksum_extent checksum)
      obtain ⟨codec, tag, output, _, diskCap, length, memoryCap⟩ := Payload.decode_sound decoded
      change some Payload.Codec.snappy = some codec at tag
      obtain rfl := Option.some.inj tag
      exact ⟨status, stored, checksum, slice, exactSize,
        by simpa [bounds] using diskCap, by simpa [bounds] using length,
        by simpa [bounds] using memoryCap, by simpa [bounds] using output⟩

public theorem expand_checksum_error {storedCap expandedCap : Nat} {source : Bytes} {frame : Page.Frame}
    {cause : Page.Checksum.Error} (h : Page.Checksum.verify storedCap source frame = .error cause) :
    expand storedCap expandedCap source frame = .error (.checksum cause) := by
  simp [expand, h, Except.mapError, Bind.bind, Except.bind]

public theorem readEntries_wire {container : ListFile.Container} {limits : Limits} {checked : ListFile.Checked container} {expanded : Nat}
    {frame : Page.Frame} {entries : List Int32} (h : readEntries limits checked expanded frame = .ok entries) :
    DictionaryWire limits checked frame entries ∧ frame.value.uncompressedSize ≤ expanded := by
  unfold readEntries at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i encoding
    split at h
    · contradiction
    rename_i count
    split at h
    · contradiction
    rename_i sized
    split at h
    · contradiction
    rename_i cap
    cases output : expand (dictionaryStoredCap limits) (dictionaryExpandedCap limits checked)
        checked.snapshot.bytes frame with
    | error e => simp [output, Bind.bind, Except.bind] at h
    | ok bytes =>
      simp only [output, Bind.bind, Except.bind, Except.mapError] at h
      cases plain : Plain.decodeInt32 info.numValues bytes with
      | error e => simp [plain] at h
      | ok actual =>
        simp only [plain] at h
        obtain rfl := Except.ok.inj h
        have exact : actual.length = info.numValues := by
          change Plain.decodeFixedWidth 4 _ _ _ = .ok actual at plain
          obtain ⟨_, words, _, wordCount, _, eq⟩ := Plain.decodeFixedWidth_ok_iff.mp plain
          rw [eq, List.length_map, wordCount]
        exact ⟨⟨info, bytes, kind, not_not.mp encoding, Nat.le_of_not_gt count, not_not.mp sized, expand_wire output, plain, exact⟩,
          Nat.le_of_not_gt cap⟩
  · contradiction

public theorem readValues_wire {limits : Limits} {entries : Array Int32} {present : Nat}
    {source : Bytes} {values : List Int32} (h : readValues limits entries present source = .ok values) :
    LookupWire limits entries present source values := by
  unfold readValues at h
  cases read : DictionaryIndex.readIndices limits.indices present source with
  | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
  | ok indices =>
    simp only [read, Except.mapError, Bind.bind, Except.bind] at h
    cases selected : DictionaryIndex.select entries indices with
    | error e => simp [selected] at h
    | ok actual =>
      simp only [selected] at h
      obtain rfl := Except.ok.inj h
      obtain ⟨byteCap, width, runs, extent, bits, count, countCap, wire⟩ :=
        DictionaryIndex.readIndices_ok_iff.mp read
      have runCap : runs.length ≤ limits.indices.bytes := by
        have size := congrArg List.length extent
        rw [Bytes.length_toList, List.length_cons] at size
        omega
      have decoded : Hybrid.decode width.toNat present limits.indices (Bytes.ofList runs) = .ok indices :=
        Hybrid.decode_ok_iff.mpr ⟨bits, count, countCap, by simpa using runCap, by simpa using wire⟩
      have indicesLen := Hybrid.decode_length decoded
      have lookups := DictionaryIndex.select_ok_iff.mp selected
      have valuesLen : actual.length = present := by
        have eq := congrArg List.length lookups
        simpa [indicesLen] using eq.symm
      exact ⟨width, runs, indices, extent, bits, byteCap, countCap, wire, indicesLen, valuesLen, lookups,
        fun _ member => DictionaryIndex.select_indices_lt selected member⟩

public theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column entries budget frame = .ok events) :
    FrameWire limits checked column entries frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i enc
    split at h
    · contradiction
    rename_i levels
    push Not at levels
    split at h
    · contradiction
    rename_i slots
    split at h
    · contradiction
    rename_i cap
    cases output : expand limits.snappy.maxStoredPageBytes checked.limits.page.maxBodyBytes
        checked.snapshot.bytes frame with
    | error e => simp [output, Bind.bind, Except.bind] at h
    | ok body =>
      simp only [output, Bind.bind, Except.bind] at h
      cases read : ListPage.decodeEventsUsing FrameError.page (readValues limits entries)
          checked.limits.page info.numValues body with
      | error e => simp [read] at h
      | ok actual =>
        simp only [read] at h
        split at h
        · contradiction
        rename_i indexed
        obtain rfl := Except.ok.inj h
        have wire := ListPage.decodeEventsUsing_wire read
        refine ⟨⟨⟨info, body, kind, not_not.mp enc, levels.1, levels.2, expand_wire output, wire⟩, ?_⟩,
          ?_, Nat.le_of_not_gt cap⟩
        · intro advertised
          simpa [advertised] using indexed
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sections⟩ := wire
          rw [sections.slotCount]
          exact Nat.le_of_not_gt slots
  · contradiction

public theorem readFramesUsing_wire {read : FrameReader} {witness : Page.Frame → List Event → Prop} {ordinal : Nat} {budget left : Budget} {state next : State}
    {frames : List Page.Frame}
    (sound : ∀ {budget frame events}, read budget frame = .ok events →
      witness frame events ∧ events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded)
    (h : readFramesUsing read ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ witness frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  induction frames generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨[], .nil, by simp, by simp [expandedSize], ListPage.feed_nil state, by simp⟩
  | cons frame rest ih =>
    rw [readFramesUsing] at h
    cases decoded : read budget frame with
    | error e => simp [decoded, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h
        obtain ⟨pages, wire, slots, bytes, feed, _⟩ := ih h
        obtain ⟨localWire, slotBound, byteBound⟩ := sound decoded
        have combined : state.feed (events ++ pages.flatten) = .ok next := by
          rw [ListPage.feed_append, fed]
          exact feed
        refine ⟨events :: pages, .cons localWire wire, ?_, ?_, combined, ListPage.feed_wire combined⟩
        · simp only [List.flatten_cons, List.length_append, Budget.use] at slots ⊢
          omega
        · simp only [expandedSize, List.map_cons, List.sum_cons, Budget.use] at bytes ⊢
          omega

public theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {ordinal : Nat} {budget left : Budget} {state next : State}
    {frames : List Page.Frame}
    (h : readFrames limits checked column entries ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column entries) frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  readFramesUsing_wire (read := readFrame limits checked column entries) (fun proof => readFrame_wire proof) h

public theorem selectFramedChunk_wire {container : ListFile.Container} {checked : ListFile.Checked container} {ordinal : Nat}
    {framed : ListFile.FramedGroup} {chunk : Chunk}
    (origin : ListFile.ChunkFrameWire checked ordinal framed 1)
    (h : selectFramedChunk framed = .ok chunk) :
    ChunkWire checked ordinal chunk ∧ chunk.framed = framed := by
  unfold selectFramedChunk at h
  cases frames :  framed.frames with
  | nil => simp [frames] at h
  | cons dictionary data =>
    simp only [frames] at h
    cases data with
    | nil => contradiction
    | cons first tail =>
      dsimp only at h
      split at h
      · contradiction
      rename_i dictOffset
      split at h
      · contradiction
      rename_i dataOffset
      obtain rfl := Except.ok.inj h
      exact ⟨⟨origin, frames, not_not.mp dictOffset, not_not.mp dataOffset⟩, rfl⟩

public theorem selectChunk_wire {container : ListFile.Container} {checked : ListFile.Checked container} {ordinal : Nat} {chunk : Chunk}
    (h : selectChunk checked ordinal = .ok chunk) : ChunkWire checked ordinal chunk := by
  unfold selectChunk at h
  cases selected : checked.frameGroupWith 1 true ordinal with
  | error e => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    exact (selectFramedChunk_wire (ListFile.frameGroupWith_wire selected).1 h).1

public theorem readSelectedGroupWith_wire {container : ListFile.Container} {limits : Limits} {walk : DataWalk container} {witness : WalkWitness container}
    {checked : ListFile.Checked container} {ordinal expanded left : Nat} {chunk : Chunk} {rows : List Row}
    (origin : ChunkWire checked ordinal chunk)
    (sound : ∀ {checked column entries ordinal budget state frames left next},
      walk checked column entries ordinal budget state frames = .ok (left, next) →
      ∃ pages, witness checked column entries frames pages ∧
        pages.flatten.length + left.slots = budget.slots ∧
        expandedSize frames + left.expanded = budget.expanded ∧
        state.feed pages.flatten = .ok next)
    (h : readSelectedGroupWith limits walk checked chunk expanded = .ok (rows, left)) :
    GroupWireWith limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  unfold readSelectedGroupWith at h
  dsimp only at h
  split at h
  · contradiction
  rename_i slotCap
  split at h
  · contradiction
  rename_i rowCap
  cases entriesRead : readEntries limits checked expanded chunk.dictionary with
  | error e => simp [entriesRead, Except.mapError, Bind.bind, Except.bind] at h
  | ok entries =>
    simp only [entriesRead, Except.mapError, Bind.bind, Except.bind] at h
    cases decoded : walk checked chunk.framed.chunk entries.toArray 1
        ⟨chunk.framed.chunk.metadata.numValues.toNat, expanded - chunk.dictionary.value.uncompressedSize⟩
        State.empty (chunk.firstData :: chunk.rest) with
    | error e => simp [decoded] at h
    | ok output =>
      obtain ⟨budget, state⟩ := output
      simp only [decoded] at h
      split at h
      · contradiction
      rename_i noSurplus
      push Not at noSurplus
      split at h
      · contradiction
      rename_i rowCount
      push Not at rowCount
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨dictionary, dictBound⟩ := readEntries_wire entriesRead
      obtain ⟨pages, wires, slots, bytes, fed⟩ := sound decoded
      have order := ListPage.feed_wire fed
      change _ + budget.slots = _ at slots
      change expandedSize (chunk.firstData :: chunk.rest) + budget.expanded =
        expanded - chunk.dictionary.value.uncompressedSize at bytes
      have total : expandedSize chunk.framed.frames + budget.expanded = expanded := by
        rw [origin.order]
        change chunk.dictionary.value.uncompressedSize + expandedSize (chunk.firstData :: chunk.rest) +
          budget.expanded = expanded
        omega
      exact ⟨⟨chunk, entries, pages, origin, dictionary, wires, by simpa [noSurplus] using slots, rowCount,
        ListPage.reconstruct_of_feed fed, by simpa [ListPage.finish_empty] using order,
        Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap, by omega⟩, by omega⟩

public theorem readGroupWith_wire {container : ListFile.Container} {limits : Limits} {walk : DataWalk container} {witness : WalkWitness container}
    {checked : ListFile.Checked container} {ordinal expanded left : Nat} {rows : List Row}
    (sound : ∀ {checked column entries ordinal budget state frames left next},
      walk checked column entries ordinal budget state frames = .ok (left, next) →
      ∃ pages, witness checked column entries frames pages ∧
        pages.flatten.length + left.slots = budget.slots ∧
        expandedSize frames + left.expanded = budget.expanded ∧
        state.feed pages.flatten = .ok next)
    (h : readGroupWith limits walk checked ordinal expanded = .ok (rows, left)) :
    GroupWireWith limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  unfold readGroupWith at h
  cases chosen : selectChunk checked ordinal with
  | error e => simp [chosen, Bind.bind, Except.bind] at h
  | ok chunk =>
    simp only [chosen, Bind.bind, Except.bind] at h
    exact readSelectedGroupWith_wire (selectChunk_wire chosen) sound h

public theorem readGroupUsing_wire {container : ListFile.Container} {limits : Limits} {read : DataReader container} {witness : DataWitness container}
    {checked : ListFile.Checked container} {ordinal expanded left : Nat}
    {rows : List Row}
    (sound : ∀ {checked column entries budget frame events}, read checked column entries budget frame = .ok events →
      witness checked column entries frame events ∧ events.length ≤ budget.slots ∧
        frame.value.uncompressedSize ≤ budget.expanded)
    (h : readGroupUsing limits read checked ordinal expanded = .ok (rows, left)) :
    GroupWireUsing limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  obtain ⟨wire, bound⟩ := readGroupWith_wire
    (witness := fun checked column entries => List.Forall₂ (witness checked column entries))
    (walk := fun checked column entries => readFramesUsing (read checked column entries))
    (fun decoded => by
      obtain ⟨pages, localWire, slots, bytes, fed, _⟩ := readFramesUsing_wire (fun proof => sound proof) decoded
      exact ⟨pages, localWire, slots, bytes, fed⟩) h
  exact ⟨⟨wire⟩, bound⟩

public theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  obtain ⟨original, bound⟩ := readGroupUsing_wire (read := readFrame limits) (witness := FrameWire limits)
    (fun proof => readFrame_wire proof) h
  exact ⟨⟨original.data⟩, bound⟩

public theorem readGroup_dictionary_error {limits : Limits} {checked : ListFile.Checked} {ordinal expanded : Nat}
    {chunk : Chunk} {cause : FrameError}
    (selected : selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) := by
  simp [readGroup, readGroupUsing, readGroupWith, readSelectedGroupWith, selected, Nat.not_lt.mpr slots, Nat.not_lt.mpr rows, failed, Except.mapError, Bind.bind, Except.bind]

public theorem readFramesUsing_append {read : FrameReader}
    {earlier suffix : List Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State}
    (h : readFramesUsing read ordinal budget state earlier = .ok (left, next)) :
    readFramesUsing read ordinal budget state (earlier ++ suffix) =
      readFramesUsing read (ordinal + earlier.length) left next suffix := by
  induction earlier generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    simp
  | cons frame rest ih =>
    rw [readFramesUsing] at h
    rw [List.cons_append, readFramesUsing]
    cases decoded : read budget frame with
    | error e => simp [decoded, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h ⊢
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h ⊢
        simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using ih h

public theorem readFramesUsing_read_error {read : FrameReader}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {cause : FrameError}
    (h : read budget frame = .error cause) :
    readFramesUsing read ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) := by
  simp [readFramesUsing, h, Except.mapError, Bind.bind, Except.bind]

public theorem readFramesUsing_feed_error {read : FrameReader}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : read budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFramesUsing read ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) := by
  simp [readFramesUsing, decoded, failed, Except.mapError, Bind.bind, Except.bind]

public theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {earlier suffix : List Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State}
    (h : readFrames limits checked column entries ordinal budget state earlier = .ok (left, next)) :
    readFrames limits checked column entries ordinal budget state (earlier ++ suffix) =
      readFrames limits checked column entries (ordinal + earlier.length) left next suffix :=
  readFramesUsing_append (read := readFrame limits checked column entries) h

public theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {cause : FrameError}
    (h : readFrame limits checked column entries budget frame = .error cause) :
    readFrames limits checked column entries ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  readFramesUsing_read_error (read := readFrame limits checked column entries) h

public theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {events : List Event} {cause : ListPage.Error}
    (read : readFrame limits checked column entries budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column entries ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  readFramesUsing_feed_error (read := readFrame limits checked column entries) read failed

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
  ListFile.Multi.Snappy.convertWith_first_error (errors := errors) opened split earlier failed

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  ListFile.Multi.Snappy.convertWith_readback (errors := errors) (read := readGroup limits)
    (witness := GroupWire limits) (fun proof => readGroup_wire proof) h

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

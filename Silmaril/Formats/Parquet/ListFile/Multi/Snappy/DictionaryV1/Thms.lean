module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

open Silmaril.Relational
open ListPage (Event State Row)
open Snappy (Budget expandedSize)

/-- The exact original CRC-checked payload denotes the bounded Snappy body. -/
theorem expand_wire {storedCap expandedCap : Nat} {source : Bytes} {frame : Page.Frame}
    {expanded : Bytes} (h : expand storedCap expandedCap source frame = .ok expanded) :
    ExpandedWire storedCap expandedCap source frame expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.expand_wire h

/-- A stored checksum failure precedes decompression. -/
theorem expand_checksum_error {storedCap expandedCap : Nat} {source : Bytes} {frame : Page.Frame}
    {cause : Page.Checksum.Error} (h : Page.Checksum.verify storedCap source frame = .error cause) :
    expand storedCap expandedCap source frame = .error (.checksum cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.expand_checksum_error h

/-- The leading dictionary is the exact original ordered signed PLAIN words. -/
theorem readEntries_wire {limits : Limits} {checked : ListFile.Checked} {expanded : Nat}
    {frame : Page.Frame} {entries : List Int32} (h : readEntries limits checked expanded frame = .ok entries) :
    DictionaryWire limits checked frame entries ∧ frame.value.uncompressedSize ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readEntries_wire h

/-- The exact width-prefixed Hybrid stream selects original dictionary entries in index order. -/
theorem readValues_wire {limits : Limits} {entries : Array Int32} {present : Nat}
    {source : Bytes} {values : List Int32} (h : readValues limits entries present source = .ok values) :
    LookupWire limits entries present source values :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readValues_wire h

/-- A V1 frame supplies exact original level streams and its present-count dictionary suffix. -/
theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column entries budget frame = .ok events) :
    FrameWire limits checked column entries frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFrame_wire h

/-- The same dictionary and live LIST state follow every original data frame. -/
theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {ordinal : Nat} {budget left : Budget} {state next : State}
    {frames : List Page.Frame}
    (h : readFrames limits checked column entries ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column entries) frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFrames_wire h

/-- The original footer and source frame chain bind both dictionary and first data offsets. -/
theorem selectChunk_wire {checked : ListFile.Checked} {ordinal : Nat} {chunk : Chunk}
    (h : selectChunk checked ordinal = .ok chunk) : ChunkWire checked ordinal chunk :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.selectChunk_wire h

/-- Checked dictionary and data frame evidence gives exact nested rows and footer counts. -/
theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readGroup_wire h

/-- A leading dictionary error retains page zero and its original absolute header offset. -/
theorem readGroup_dictionary_error {limits : Limits} {checked : ListFile.Checked} {ordinal expanded : Nat}
    {chunk : Chunk} {cause : FrameError}
    (selected : selectChunk checked ordinal = .ok chunk)
    (slots : chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots)
    (rows : chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (failed : readEntries limits checked expanded chunk.dictionary = .error cause) :
    readGroup limits checked ordinal expanded = .error (.frame 0 chunk.dictionary.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readGroup_dictionary_error selected slots rows failed

/-- A successful data prefix carries the same dictionary, list state and remaining budgets. -/
theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {earlier suffix : List Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State}
    (h : readFrames limits checked column entries ordinal budget state earlier = .ok (left, next)) :
    readFrames limits checked column entries ordinal budget state (earlier ++ suffix) =
      readFrames limits checked column entries (ordinal + earlier.length) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFrames_append h

/-- The first failing data frame retains its original indexed cause. -/
theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {cause : FrameError}
    (h : readFrame limits checked column entries budget frame = .error cause) :
    readFrames limits checked column entries ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFrames_read_error h

/-- A failed nested transition retains its original page ordinal and header offset. -/
theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {entries : Array Int32} {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {events : List Event} {cause : ListPage.Error}
    (read : readFrame limits checked column entries budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column entries ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFrames_feed_error read failed

/-- The first source error preserves earlier groups and precedes sink admission. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsWith SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.convert_first_error opened split earlier failed

/-- The original checked groups and ordered nested nullable IPC batches agree through exact EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.convert_readback h

/-- Apply the existing ordered budgeted walk to one segment of the selected chunk. -/
theorem readFramesUsing_wire {read : FrameReader} {witness : Page.Frame → List Event → Prop}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (sound : ∀ {budget frame events}, read budget frame = .ok events →
      witness frame events ∧ events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded)
    (h : readFramesUsing read ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ witness frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      Snappy.expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_wire sound h

/-- Lift a checked data walk to the original chunk, signed dictionary and group rows. -/
theorem readGroupWith_wire {limits : Limits} {walk : DataWalk} {witness : WalkWitness}
    {checked : ListFile.Checked} {ordinal expanded left : Nat} {rows : List Row}
    (sound : ∀ {checked column entries ordinal budget state frames left next},
      walk checked column entries ordinal budget state frames = .ok (left, next) →
      ∃ pages, witness checked column entries frames pages ∧
        pages.flatten.length + left.slots = budget.slots ∧
        Snappy.expandedSize frames + left.expanded = budget.expanded ∧
        state.feed pages.flatten = .ok next)
    (h : readGroupWith limits walk checked ordinal expanded = .ok (rows, left)) :
    GroupWireWith limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readGroupWith_wire sound h

/-- The dictionary group walk retains the original dictionary and data-page witnesses. -/
theorem readGroupUsing_wire {limits : Limits} {read : DataReader} {witness : DataWitness}
    {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row}
    (sound : ∀ {checked column entries budget frame events}, read checked column entries budget frame = .ok events →
      witness checked column entries frame events ∧ events.length ≤ budget.slots ∧
        frame.value.uncompressedSize ≤ budget.expanded)
    (h : readGroupUsing limits read checked ordinal expanded = .ok (rows, left)) :
    GroupWireUsing limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readGroupUsing_wire sound h

/-- An accepted frame prefix passes the live LIST state and remaining budgets to the suffix. -/
theorem readFramesUsing_append {read : FrameReader}
    {earlier suffix : List Page.Frame} {ordinal : Nat}
    {budget left : Budget} {state next : State}
    (h : readFramesUsing read ordinal budget state earlier = .ok (left, next)) :
    readFramesUsing read ordinal budget state (earlier ++ suffix) =
      readFramesUsing read (ordinal + earlier.length) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_append h

/-- The selected data callback retains the first failing page coordinates. -/
theorem readFramesUsing_read_error {read : FrameReader}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {cause : FrameError}
    (h : read budget frame = .error cause) :
    readFramesUsing read ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_read_error h

/-- Nested transition errors retain the original page coordinates. -/
theorem readFramesUsing_feed_error {read : FrameReader}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat}
    {budget : Budget} {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : read budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFramesUsing read ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.readFramesUsing_feed_error decoded failed

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

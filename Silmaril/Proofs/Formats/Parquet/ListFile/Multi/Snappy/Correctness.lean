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

public theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked column ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column) frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  induction frames generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨[], .nil, by simp, by simp [expandedSize], ListPage.feed_nil state, by simp⟩
  | cons frame rest ih =>
    rw [readFrames] at h
    cases read : readFrame limits checked column budget frame with
    | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at h
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h
        obtain ⟨pages, wire, count, bytes, nextFed, _⟩ := ih h
        obtain ⟨page, slotBound, byteBound⟩ := readFrame_wire read
        have combined : state.feed (events ++ pages.flatten) = .ok next := by
          rw [ListPage.feed_append, fed]
          exact nextFed
        refine ⟨events :: pages, .cons page wire, ?_, ?_, combined, ListPage.feed_wire combined⟩
        · simp only [List.flatten_cons, List.length_append, Budget.use] at count ⊢
          omega
        · simp only [expandedSize, List.map_cons, List.sum_cons, Budget.use] at bytes ⊢
          omega

public theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  unfold readGroup at h
  cases selected : checked.frameGroupFor 1 ordinal with
  | error e => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i slotCap
      split at h
      · contradiction
      · rename_i rowCap
        cases read : readFrames limits checked framed.chunk 0 ⟨framed.chunk.metadata.numValues.toNat, expanded⟩
            State.empty framed.frames with
        | error e => simp [read] at h
        | ok result =>
          obtain ⟨budget, state⟩ := result
          simp only [read] at h
          split at h
          · contradiction
          · rename_i noSurplus
            push Not at noSurplus
            split at h
            · contradiction
            · rename_i rowCount
              push Not at rowCount
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨pages, wire, count, bytes, fed, order⟩ := readFrames_wire read
              change pages.flatten.length + budget.slots = _ at count
              change expandedSize framed.frames + budget.expanded = expanded at bytes
              exact ⟨⟨framed, pages, ListFile.frameGroupFor_wire selected, wire,
                by simpa [noSurplus] using count, rowCount, ListPage.reconstruct_of_feed fed, by simpa [ListPage.finish_empty] using order,
                Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap, by omega⟩, by omega⟩

public theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {budget left : Budget} {state next : State}
    (h : readFrames limits checked column ordinal budget state earlier = .ok (left, next)) :
    readFrames limits checked column ordinal budget state (earlier ++ suffix) =
      readFrames limits checked column (ordinal + earlier.length) left next suffix := by
  induction earlier generalizing ordinal budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    simp
  | cons frame rest ih =>
    rw [readFrames] at h
    rw [List.cons_append, readFrames]
    cases read : readFrame limits checked column budget frame with
    | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at h ⊢
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h ⊢
        simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using ih h

public theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrame limits checked column budget frame = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) := by
  simp [readFrames, h, Except.mapError, Bind.bind, Except.bind]

public theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : readFrame limits checked column budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) := by
  simp [readFrames, decoded, failed, Except.mapError, Bind.bind, Except.bind]

private theorem readGroups_wire {limits : Limits} {checked : ListFile.Checked} {indices : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroups limits checked expanded indices = (groups, .ok left)) :
    ∃ costs,
      List.Forall₂ (fun ordinal (batch : List Row × Nat) => GroupWire limits checked ordinal batch.1 batch.2)
        indices (groups.zip costs) ∧
      costs.length = groups.length ∧ costs.sum + left = expanded := by
  induction indices generalizing expanded groups with
  | nil =>
    obtain ⟨rfl, same⟩ := Prod.mk.inj h
    obtain rfl := Except.ok.inj same
    exact ⟨[], .nil, rfl, by simp⟩
  | cons ordinal rest ih =>
    rw [readGroups] at h
    cases group : readGroup limits checked ordinal expanded with
    | error e => simp [group] at h
    | ok result =>
      obtain ⟨rows, remaining⟩ := result
      simp only [group] at h
      cases tailRead : readGroups limits checked remaining rest with
      | mk tail outcome =>
        rw [tailRead] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨costs, wire, counts, budget⟩ := ih tailRead
        obtain ⟨groupWire, bound⟩ := readGroup_wire group
        refine ⟨(expanded - remaining) :: costs, .cons groupWire wire, by simp [counts], ?_⟩
        simp only [List.sum_cons]
        omega

public theorem readGroups_append {limits : Limits} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroups limits checked expanded before = (groups, .ok left)) :
    readGroups limits checked expanded (before ++ after) =
      let tail := readGroups limits checked left after
      (groups ++ tail.1, tail.2) := by
  induction before generalizing expanded groups with
  | nil =>
    obtain ⟨rfl, same⟩ := Prod.mk.inj h
    obtain rfl := Except.ok.inj same
    simp
  | cons ordinal rest ih =>
    rw [readGroups] at h
    rw [List.cons_append, readGroups]
    cases group : readGroup limits checked ordinal expanded with
    | error e => simp [group] at h
    | ok result =>
      obtain ⟨rows, remaining⟩ := result
      simp only [group] at h ⊢
      cases tailRead : readGroups limits checked remaining rest with
      | mk tail outcome =>
        rw [tailRead] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [ih tailRead]
        rfl

public theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroups limits checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) := by
  unfold convert
  rw [opened]
  simp only [split, readGroups_append earlier, readGroups, failed, List.append_nil, and_self]

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire := by
  cases opened : ListFile.openFile limits.parquet.file source with
  | error e => simp [convert, opened] at h
  | ok checked =>
    cases groupsRead : readGroups limits checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount) with
    | mk groups outcome =>
      cases outcome with
      | error e => simp [convert, opened, groupsRead] at h
      | ok left =>
        simp only [convert, opened, groupsRead] at h
        cases written : Arrow.ListInt32.Stream.Writer.emit limits.ipc (ListFile.Multi.ToIpc.fieldOf checked) groups with
        | error e => simp [written, Except.mapError] at h
        | ok bytes =>
          obtain rfl := Except.ok.inj (by simpa only [written, Except.mapError] using h)
          obtain ⟨costs, witness, count, cap⟩ := readGroups_wire groupsRead
          obtain ⟨decoded, size, read, agrees, wf, envelope, schema, batches⟩ :=
            Arrow.ListInt32.Stream.Writer.emit_readback written
          exact ⟨checked, groups, costs, left, decoded, size, opened, ListFile.openFile_wire opened,
            groupsRead, witness, count, cap, by simp [convert, opened, groupsRead],
            read, agrees, wf, envelope, schema, batches⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy

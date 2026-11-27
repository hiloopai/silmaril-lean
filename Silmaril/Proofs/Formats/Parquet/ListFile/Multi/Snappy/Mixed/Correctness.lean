module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi (startsWithinRow)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy (Limits Budget GroupError FrameError expandedSize)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed
open Silmaril.Relational
open ListPage (Event State Row)

public theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events) :
    FrameWire limits checked column frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  cases kind : frame.value.kind <;> simp only [readFrame, FrameWire, kind] at h ⊢
  case dataV1 => exact ListFile.Multi.Snappy.readFrame_wire h
  case dataV2 => exact ListFile.Multi.Snappy.readV2Frame_wire h
  all_goals contradiction

public theorem v2_startsAtBoundary {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {events : List Event} {info : Page.DataV2}
    (kind : frame.value.kind = .dataV2 info) (h : FrameWire limits checked column frame events) :
    startsWithinRow events = false := by
  have wire : ListFile.Multi.Snappy.V2FrameWire limits checked frame events := by simpa only [FrameWire, kind] using h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, boundary, _⟩ := wire.data
  exact boundary

public theorem following_v2_startsAtBoundary {pending : Bool} {frame next : Page.Frame}
    {frames : List Page.Frame} {events following : List Event} {pages : List (List Event)} {info : Page.DataV2}
    (kind : frame.value.kind = .dataV2 info)
    (h : Boundaries pending (frame :: next :: frames) (events :: following :: pages)) :
    startsWithinRow following = false := by
  cases h with
  | cons _ rest =>
    cases rest with
    | cons start _ => exact start (by simp [nextBoundary, kind])

private theorem frameWire_slots {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {events : List Event} (h : FrameWire limits checked column frame events) :
    events.length = frameSlots frame := by
  cases kind : frame.value.kind <;> simp only [kind, FrameWire, frameSlots] at h ⊢
  case dataV1 info =>
    obtain ⟨_, _, _, actual, _, _, _, _, _, _, parsed, _, wire⟩ := h.data
    rw [kind] at parsed
    cases parsed
    exact wire.slotCount
  case dataV2 info =>
    obtain ⟨_, _, actual, _, _, _, _, _, parsed, _, _, wire, _⟩ := h.data
    rw [kind] at parsed
    cases parsed
    exact wire.slotCount

private theorem frameWire_total {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frames : List Page.Frame} {pages : List (List Event)}
    (h : List.Forall₂ (FrameWire limits checked column) frames pages) :
    (frames.map frameSlots).sum = pages.flatten.length := by
  induction h with
  | nil => rfl
  | cons localWire _ ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, ih, frameWire_slots localWire]

public theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {ordinal : Nat} {pending : Bool} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked column ordinal pending budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column) frames pages ∧ Boundaries pending frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  induction frames generalizing ordinal pending budget state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨[], .nil, .nil pending, by simp, by simp [expandedSize], ListPage.feed_nil state, by simp⟩
  | cons frame rest ih =>
    rw [readFrames] at h
    cases read : readFrame limits checked column budget frame with
    | error e => simp [read, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      · rename_i accepted
        cases fed : state.feed events with
        | error e => simp [fed] at h
        | ok more =>
          simp only [fed] at h
          obtain ⟨pages, wire, boundaries, slots, bytes, feed, _⟩ := ih h
          obtain ⟨localWire, slotBound, byteBound⟩ := readFrame_wire read
          have combined : state.feed (events ++ pages.flatten) = .ok next := by
            rw [ListPage.feed_append, fed]
            exact feed
          have validStart (required : pending = true) : startsWithinRow events = false :=
            Bool.eq_false_iff.mpr (by simpa [required] using accepted)
          refine ⟨events :: pages, .cons localWire wire, .cons validStart boundaries, ?_, ?_,
            combined, ListPage.feed_wire combined⟩
          · simp only [List.flatten_cons, List.length_append, ListFile.Multi.Snappy.Budget.use] at slots ⊢
            omega
          · simp only [expandedSize, List.map_cons, List.sum_cons, ListFile.Multi.Snappy.Budget.use] at bytes ⊢
            omega

public theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  obtain ⟨framed, budget, state, origin, read, noSurplus, remaining, rfl, rowCount, slotCap, rowCap⟩ :=
    ListFile.Multi.Snappy.readGroupUsing_checked
      (walk := fun column budget => readFrames limits checked column 0 false budget State.empty) h
  obtain ⟨pages, wire, boundaries, count, bytes, fed, order⟩ := readFrames_wire read
  change pages.flatten.length + budget.slots = _ at count
  change expandedSize framed.frames + budget.expanded = expanded at bytes
  have allSlots : pages.flatten.length = framed.chunk.metadata.numValues.toNat := by simpa [noSurplus] using count
  exact ⟨⟨framed, pages, origin, wire, boundaries, allSlots, (frameWire_total wire).trans allSlots, rowCount,
    ListPage.reconstruct_of_feed fed, by simpa [ListPage.finish_empty] using order, slotCap, rowCap, by omega⟩, by omega⟩

public theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget left : Budget} {state next : State}
    (h : readFrames limits checked column ordinal pending budget state earlier = .ok (left, next)) :
    readFrames limits checked column ordinal pending budget state (earlier ++ suffix) =
      readFrames limits checked column (ordinal + earlier.length) (earlier.foldl nextBoundary pending) left next suffix := by
  induction earlier generalizing ordinal pending budget state with
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
      split at h
      · contradiction
      · rename_i accepted
        simp only [accepted]
        cases fed : state.feed events with
        | error e => simp [fed] at h
        | ok more =>
          simp only [fed] at h ⊢
          simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using ih h

public theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrame limits checked column budget frame = .error cause) :
    readFrames limits checked column ordinal pending budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) := by
  simp [readFrames, h, Except.mapError, Bind.bind, Except.bind]

public theorem readFrames_boundary_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events)
    (continued : startsWithinRow events = true) :
    readFrames limits checked column ordinal true budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start .v2Continuation) := by
  simp [readFrames, h, continued, Except.mapError, Bind.bind, Except.bind]
  rfl

public theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (h : readFrame limits checked column budget frame = .ok events)
    (eligible : (pending && startsWithinRow events) = false)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column ordinal pending budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) := by
  simp [readFrames, h, eligible, failed, Except.mapError, Bind.bind, Except.bind]

public theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsUsing (readGroup limits) checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  ListFile.Multi.Snappy.convertUsing_first_error opened split earlier failed

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  ListFile.Multi.Snappy.convertUsing_readback (read := readGroup limits)
    (witness := GroupWire limits) (fun proof => readGroup_wire proof) h

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed

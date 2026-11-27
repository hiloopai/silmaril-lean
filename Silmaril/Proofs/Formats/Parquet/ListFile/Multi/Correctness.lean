module

public import Silmaril.Formats.Parquet.ListFile.Multi.Defs
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi
open ListPage (Event State Row)
open Silmaril.Relational

public theorem readFrame_wire {checked : ListFile.Checked} {column : Footer.ColumnChunk} {remaining : Nat}
    {frame : Page.Frame} {events : List Event} (h : readFrame checked column remaining frame = .ok events) :
    FrameWire checked column frame events ∧ events.length ≤ remaining := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    · rename_i cap
      split at h
      · contradiction
      · cases sliced : checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) with
        | none => simp [sliced] at h
        | some body =>
          simp only [sliced, Except.mapError, Bind.bind, Except.bind] at h
          cases decoded : ListPage.decodeV1Events checked.limits.page column.metadata.codec frame.value body with
          | error e => simp [decoded] at h
          | ok result =>
            simp only [decoded] at h
            split at h
            · contradiction
            · rename_i boundary
              obtain rfl := Except.ok.inj h
              obtain ⟨actual, header, wire⟩ := ListPage.decodeV1Events_wire decoded
              have same := header.kind
              rw [kind] at same
              cases same
              refine ⟨⟨⟨body, info, sliced, header, wire⟩, ?_⟩, ?_⟩
              · intro indexed
                simpa [indexed] using boundary
              · rw [wire.slotCount]
                exact Nat.le_of_not_gt cap
  · contradiction

public theorem readFramesWith_wire {frameError groupError : Type} {indexed : Nat → Nat → frameError → groupError}
    {feedError : ListPage.Error → frameError} {read : SlotFrameReader frameError}
    {witness : Page.Frame → List Event → Prop}
    {frames : List Page.Frame} {ordinal remaining left : Nat} {state next : State}
    (sound : ∀ {remaining frame events}, read remaining frame = .ok events →
      witness frame events ∧ events.length ≤ remaining)
    (h : readFramesWith indexed feedError read frames ordinal remaining state = .ok (left, next)) :
    ∃ pages, List.Forall₂ witness frames pages ∧
      pages.flatten.length + left = remaining ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  induction frames generalizing ordinal remaining state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨[], .nil, by simp, ListPage.feed_nil state, by simp⟩
  | cons frame rest ih =>
    rw [readFramesWith] at h
    cases frameRead : read remaining frame with
    | error e => simp [frameRead, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [frameRead, Except.mapError, Bind.bind, Except.bind] at h
      cases fed : state.feed events with
      | error e => simp [fed] at h
      | ok more =>
        simp only [fed] at h
        obtain ⟨pages, wire, count, nextFed, order⟩ := ih h
        obtain ⟨page, bound⟩ := sound frameRead
        refine ⟨events :: pages, .cons page wire, ?_, ?_, ?_⟩
        · simp only [List.flatten_cons, List.length_append]
          omega
        · rw [List.flatten_cons, ListPage.feed_append, fed]
          exact nextFed
        · simpa [ListPage.feed_wire fed, List.append_assoc] using order

public theorem readFrames_wire {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frames : List Page.Frame} {ordinal remaining left : Nat} {state next : State}
    (h : readFrames checked column frames ordinal remaining state = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire checked column) frames pages ∧
      pages.flatten.length + left = remaining ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten := by
  obtain ⟨pages, frameWire, count, _, ordered⟩ :=
    readFramesWith_wire (witness := FrameWire checked column)
      (read := readFrame checked column) (fun decoded => readFrame_wire decoded) h
  exact ⟨pages, frameWire, count, ordered⟩

public theorem readFramesWith_append {frameError groupError : Type}
    {indexed : Nat → Nat → frameError → groupError} {feedError : ListPage.Error → frameError}
    {read : SlotFrameReader frameError} {before after : List Page.Frame} {ordinal remaining left : Nat}
    {state next : State}
    (h : readFramesWith indexed feedError read before ordinal remaining state = .ok (left, next)) :
    readFramesWith indexed feedError read (before ++ after) ordinal remaining state =
      readFramesWith indexed feedError read after (ordinal + before.length) left next := by
  induction before generalizing ordinal remaining state with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    simp
  | cons frame rest ih =>
    rw [readFramesWith] at h
    cases decoded : read remaining frame with
    | error cause => simp [decoded, Except.mapError, Bind.bind, Except.bind] at h
    | ok events =>
      simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
      cases fed : state.feed events with
      | error cause => simp [fed] at h
      | ok more =>
        simp only [fed] at h
        simp only [List.cons_append, readFramesWith, decoded, Except.mapError, Bind.bind, Except.bind, fed]
        rw [ih h]
        congr 1
        simp only [List.length_cons]
        omega

public theorem readGroup_wire {maxGroupSlots : Nat} {checked : ListFile.Checked} {ordinal : Nat} {slots : List Row}
    (h : readGroup maxGroupSlots checked ordinal = .ok slots) : GroupWire maxGroupSlots checked ordinal slots := by
  unfold readGroup at h
  cases frame : checked.frameGroup ordinal with
  | error e => simp [frame, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [frame, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i slotCap
      split at h
      · contradiction
      · rename_i rowCap
        cases read : readFrames checked framed.chunk framed.frames 0 framed.chunk.metadata.numValues.toNat
            State.empty with
        | error e => simp [read] at h
        | ok result =>
          obtain ⟨left, state⟩ := result
          simp only [read] at h
          split at h
          · contradiction
          · rename_i noSurplus
            push Not at noSurplus
            subst left
            split at h
            · contradiction
            · rename_i rowCount
              push Not at rowCount
              obtain rfl := Except.ok.inj h
              obtain ⟨pages, wire, count, order⟩ := readFrames_wire read
              exact ⟨framed, pages, ListFile.frameGroup_wire frame, wire, by simpa using count, rowCount,
                by simpa [ListPage.finish_empty] using order, Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩

public theorem readFrames_read_error {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal remaining : Nat}
    {state : State} {cause : FrameError} (failed : readFrame checked column remaining frame = .error cause) :
    readFrames checked column (frame :: rest) ordinal remaining state =
      .error (.frame ordinal frame.header.start cause) := by
  simp [readFrames, readFramesWith, failed, Except.mapError, Bind.bind, Except.bind]

public theorem readFrames_feed_error {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal remaining : Nat}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (read : readFrame checked column remaining frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames checked column (frame :: rest) ordinal remaining state =
      .error (.frame ordinal frame.header.start (.page cause)) := by
  simp [readFrames, readFramesWith, read, failed, Except.mapError, Bind.bind, Except.bind]

public theorem readFrames_leading_continuation {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {remaining : Nat} {item : Option Int32} {events : List Event}
    (read : readFrame checked column remaining frame = .ok (.next item :: events)) :
    readFrames checked column (frame :: rest) 0 remaining State.empty =
      .error (.frame 0 frame.header.start (.page .continuationWithoutList)) := by
  apply readFrames_feed_error read
  rw [ListPage.feed_next]
  rfl

public theorem readAll_reference {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    (opened : ListFile.openFile limits.file source = .ok checked) :
    let groups := groupSource limits checked
    let reference := Reader.denoteGroups groups.readGroup (List.range checked.snapshot.groupCount)
    readAll limits source = .ok ⟨ListFile.schema checked,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ := by
  have admitted : openSource limits source = .ok ⟨ListFile.schema checked, groupSource limits checked⟩ := by
    simp [openSource, opened, Except.map, Except.mapError]
  unfold readAll
  rw [admitted, Reader.readAll_opened]
  rfl

private theorem denote_first_error {limits : Limits} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (Reader.RowGroup (ListFile.schema checked) ListFile.Cell)}
    {error : Error}
    (earlier : before.mapM (groupSource limits checked).readGroup = .ok groups)
    (failed : (groupSource limits checked).readGroup ordinal = .error error) :
    Reader.denoteGroups (groupSource limits checked).readGroup (before ++ ordinal :: after) =
      (groups, .readError error) := by
  induction before generalizing groups with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst groups
    simp [Reader.denoteGroups, failed]
  | cons index rest ih =>
    cases first : (groupSource limits checked).readGroup index with
    | error e => simp [List.mapM_cons, first, Bind.bind, Except.bind] at earlier
    | ok rows =>
      cases tail : rest.mapM (groupSource limits checked).readGroup with
      | error e => simp [List.mapM_cons, first, tail, Bind.bind, Except.bind] at earlier
      | ok decoded =>
        simp [List.mapM_cons, first, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at earlier
        subst groups
        simp [Reader.denoteGroups, first, ih tail]

public theorem readAll_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (Reader.RowGroup (ListFile.schema checked) ListFile.Cell)}
    {cause : GroupError}
    (opened : ListFile.openFile limits.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (groupSource limits checked).readGroup = .ok groups)
    (failed : readGroup limits.maxGroupSlots checked ordinal = .error cause) :
    readAll limits source = .ok ⟨ListFile.schema checked,
      ⟨groups.map AlignedColumns.ofRows, .readError (.groupFailure ordinal cause)⟩⟩ := by
  have original : (groupSource limits checked).readGroup ordinal = .error (.groupFailure ordinal cause) := by
    simp [groupSource, failed, Except.map, Except.mapError]
  rw [readAll_reference opened, split, denote_first_error earlier original]

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi

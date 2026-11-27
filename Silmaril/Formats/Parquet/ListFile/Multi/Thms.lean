module

public import Silmaril.Formats.Parquet.ListFile.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi

open ListPage (Event State Row)
open Silmaril.Relational

/-- A frame consumes its original source slice and no more than the remaining slots. -/
theorem readFrame_wire {checked : ListFile.Checked} {column : Footer.ColumnChunk} {remaining : Nat}
    {frame : Page.Frame} {events : List Event} (h : readFrame checked column remaining frame = .ok events) :
    FrameWire checked column frame events ∧ events.length ≤ remaining :=
  Proofs.Formats.Parquet.ListFile.Multi.readFrame_wire h

/-- The selected decoder contributes exact slots and the shared LIST state
retains the original event order. -/
theorem readFramesWith_wire {frameError groupError : Type} {indexed : Nat → Nat → frameError → groupError}
    {feedError : ListPage.Error → frameError} {read : SlotFrameReader frameError}
    {witness : Page.Frame → List Event → Prop}
    {frames : List Page.Frame} {ordinal remaining left : Nat} {state next : State}
    (sound : ∀ {remaining frame events}, read remaining frame = .ok events →
      witness frame events ∧ events.length ≤ remaining)
    (h : readFramesWith indexed feedError read frames ordinal remaining state = .ok (left, next)) :
    ∃ pages, List.Forall₂ witness frames pages ∧
      pages.flatten.length + left = remaining ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.readFramesWith_wire sound h

/-- A successful original frame prefix passes the remaining slots and state to its suffix. -/
theorem readFramesWith_append {frameError groupError : Type}
    {indexed : Nat → Nat → frameError → groupError} {feedError : ListPage.Error → frameError}
    {read : SlotFrameReader frameError} {before after : List Page.Frame} {ordinal remaining left : Nat}
    {state next : State}
    (h : readFramesWith indexed feedError read before ordinal remaining state = .ok (left, next)) :
    readFramesWith indexed feedError read (before ++ after) ordinal remaining state =
      readFramesWith indexed feedError read after (ordinal + before.length) left next :=
  Proofs.Formats.Parquet.ListFile.Multi.readFramesWith_append h

/-- The original frame order determines the concatenated wire events and exact slot total. -/
theorem readFrames_wire {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frames : List Page.Frame} {ordinal remaining left : Nat} {state next : State}
    (h : readFrames checked column frames ordinal remaining state = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire checked column) frames pages ∧
      pages.flatten.length + left = remaining ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.readFrames_wire h

/-- The original checked group and frames determine every row and level slot. -/
theorem readGroup_wire {maxGroupSlots : Nat} {checked : ListFile.Checked} {ordinal : Nat} {slots : List Row}
    (h : readGroup maxGroupSlots checked ordinal = .ok slots) : GroupWire maxGroupSlots checked ordinal slots :=
  Proofs.Formats.Parquet.ListFile.Multi.readGroup_wire h

/-- A failed continuation retains the original frame ordinal, offset and cause. -/
theorem readFrames_feed_error {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal remaining : Nat}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (read : readFrame checked column remaining frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames checked column (frame :: rest) ordinal remaining state =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.readFrames_feed_error read failed

/-- The event trace follows the complete checked groups in footer order and stops at the first error. -/
theorem readAll_reference {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    (opened : ListFile.openFile limits.file source = .ok checked) :
    let groups := groupSource limits checked
    let reference := Reader.denoteGroups groups.readGroup (List.range checked.snapshot.groupCount)
    readAll limits source = .ok ⟨ListFile.schema checked,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :=
  Proofs.Formats.Parquet.ListFile.Multi.readAll_reference opened

/-- Frame decoding errors retain the original ordinal, offset and typed cause. -/
theorem readFrames_read_error {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal remaining : Nat}
    {state : State} {cause : FrameError} (failed : readFrame checked column remaining frame = .error cause) :
    readFrames checked column (frame :: rest) ordinal remaining state =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.readFrames_read_error failed

/-- A group may never start with a continuation, even when the page bytes decode. -/
theorem readFrames_leading_continuation {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {remaining : Nat} {item : Option Int32} {events : List Event}
    (read : readFrame checked column remaining frame = .ok (.next item :: events)) :
    readFrames checked column (frame :: rest) 0 remaining State.empty =
      .error (.frame 0 frame.header.start (.page .continuationWithoutList)) :=
  Proofs.Formats.Parquet.ListFile.Multi.readFrames_leading_continuation read

/-- A group failure retains the preceding batches with the original indexed cause. -/
theorem readAll_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (Reader.RowGroup (ListFile.schema checked) ListFile.Cell)}
    {cause : GroupError}
    (opened : ListFile.openFile limits.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (groupSource limits checked).readGroup = .ok groups)
    (failed : readGroup limits.maxGroupSlots checked ordinal = .error cause) :
    readAll limits source = .ok ⟨ListFile.schema checked,
      ⟨groups.map AlignedColumns.ofRows, .readError (.groupFailure ordinal cause)⟩⟩ :=
  Proofs.Formats.Parquet.ListFile.Multi.readAll_first_error opened split earlier failed

end Silmaril.Formats.Parquet.ListFile.Multi

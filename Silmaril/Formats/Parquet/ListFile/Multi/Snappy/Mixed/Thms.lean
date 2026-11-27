module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed

open Silmaril.Relational
open ListPage (Event State Row)
open Multi (startsWithinRow)

/-- The original frame tag selects the exact V1 or V2 witness. -/
theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events) :
    FrameWire limits checked column frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrame_wire h

/-- A V2 page starts at a row boundary. -/
theorem v2_startsAtBoundary {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {events : List Event} {info : Page.DataV2}
    (kind : frame.value.kind = .dataV2 info) (h : FrameWire limits checked column frame events) :
    startsWithinRow events = false :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.v2_startsAtBoundary kind h

/-- After a V2 page the next frame cannot continue its final row. -/
theorem following_v2_startsAtBoundary {pending : Bool} {frame next : Page.Frame}
    {frames : List Page.Frame} {events following : List Event} {pages : List (List Event)} {info : Page.DataV2}
    (kind : frame.value.kind = .dataV2 info)
    (h : Boundaries pending (frame :: next :: frames) (events :: following :: pages)) :
    startsWithinRow following = false :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.following_v2_startsAtBoundary kind h

/-- An ordered frame walk retains version-specific wire, boundary, budget and continuation evidence. -/
theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {ordinal : Nat} {pending : Bool} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked column ordinal pending budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column) frames pages ∧ Boundaries pending frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrames_wire h

/-- The complete original chunk gives exact nested rows and footer counts. -/
theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readGroup_wire h

/-- A successful frame prefix preserves its boundary requirement, live list and budgets. -/
theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget left : Budget} {state next : State}
    (h : readFrames limits checked column ordinal pending budget state earlier = .ok (left, next)) :
    readFrames limits checked column ordinal pending budget state (earlier ++ suffix) =
      readFrames limits checked column (ordinal + earlier.length) (earlier.foldl nextBoundary pending) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrames_append h

/-- Frame reads preserve the original typed failure and page coordinates. -/
theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrame limits checked column budget frame = .error cause) :
    readFrames limits checked column ordinal pending budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrames_read_error h

/-- A continuation across the trailing V2 boundary is refused at its original page. -/
theorem readFrames_boundary_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events)
    (continued : startsWithinRow events = true) :
    readFrames limits checked column ordinal true budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start .v2Continuation) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrames_boundary_error h continued

/-- A failed LIST transition retains its original page ordinal and offset. -/
theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {pending : Bool} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (h : readFrame limits checked column budget frame = .ok events)
    (eligible : (pending && startsWithinRow events) = false)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column ordinal pending budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.readFrames_feed_error h eligible failed

/-- The first failing group precedes IPC admission and retains earlier groups. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : ListFile.Multi.Snappy.readGroupsUsing (readGroup limits) checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.convert_first_error opened split earlier failed

/-- Successful native IPC readback agrees with the checked mixed chunks through EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.Mixed.convert_readback h

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed

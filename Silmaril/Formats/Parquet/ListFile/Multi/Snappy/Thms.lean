module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy

open ListPage (Event State Row)
open Silmaril.Relational

/-- The original stored CRC, exact Snappy member and expanded V1 sections agree. -/
theorem readFrame_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readFrame limits checked column budget frame = .ok events) :
    FrameWire limits checked column frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrame_wire h

/-- Once the header and allowance checks pass, a stored-payload refusal precedes expansion. -/
theorem readFrame_checksum_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV1} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV1 info)
    (encoding : info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked column budget frame = .error (.checksum cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrame_checksum_error kind encoding slots expanded failed

/-- Frames contribute their events in wire order with exact slot and byte accounting. -/
theorem readFrames_wire {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked column ordinal budget state frames = .ok (left, next)) :
    ∃ pages, List.Forall₂ (FrameWire limits checked column) frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧
      state.feed pages.flatten = .ok next ∧
      next.finish.flatMap ListPage.rowEvents = state.finish.flatMap ListPage.rowEvents ++ pages.flatten :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrames_wire h

/-- The original selected group reconstructs the exact rows and charges its expanded bytes. -/
theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroup_wire h

/-- A successful frame prefix carries the same live list and budgets to the suffix. -/
theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {budget left : Budget} {state next : State}
    (h : readFrames limits checked column ordinal budget state earlier = .ok (left, next)) :
    readFrames limits checked column ordinal budget state (earlier ++ suffix) =
      readFrames limits checked column (ordinal + earlier.length) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrames_append h

/-- A failed frame retains its original page ordinal and header offset. -/
theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrame limits checked column budget frame = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrames_read_error h

/-- A failed transition retains its original page ordinal and header offset. -/
theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : readFrame limits checked column budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFrames_feed_error decoded failed

/-- A successful group prefix passes the remaining expansion budget to the suffix. -/
theorem readGroups_append {limits : Limits} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroups limits checked expanded before = (groups, .ok left)) :
    readGroups limits checked expanded (before ++ after) =
      let tail := readGroups limits checked left after
      (groups ++ tail.1, tail.2) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroups_append h

/-- The first indexed group failure retains the batch prefix and takes precedence over IPC admission. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroups limits checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convert_first_error opened split earlier failed

/-- A successful native stream agrees with the checked Parquet groups through exact EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convert_readback h

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy

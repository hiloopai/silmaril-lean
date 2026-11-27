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
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_wire (version := .v1) h

/-- The original selected group reconstructs the exact rows and charges its expanded bytes. -/
theorem readGroup_wire {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroupFor_wire (version := .v1) h

/-- A successful frame prefix carries the same live list and budgets to the suffix. -/
theorem readFrames_append {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {budget left : Budget} {state next : State}
    (h : readFrames limits checked column ordinal budget state earlier = .ok (left, next)) :
    readFrames limits checked column ordinal budget state (earlier ++ suffix) =
      readFrames limits checked column (ordinal + earlier.length) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_append (version := .v1) h

/-- A failed frame retains its original page ordinal and header offset. -/
theorem readFrames_read_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrame limits checked column budget frame = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_read_error (version := .v1) h

/-- A failed transition retains its original page ordinal and header offset. -/
theorem readFrames_feed_error {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : readFrame limits checked column budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFrames limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_feed_error (version := .v1) decoded failed

/-- A successful group prefix passes the remaining expansion budget to the suffix. -/
theorem readGroups_append {limits : Limits} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroups limits checked expanded before = (groups, .ok left)) :
    readGroups limits checked expanded (before ++ after) =
      let tail := readGroups limits checked left after
      (groups ++ tail.1, tail.2) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroupsFor_append (version := .v1) h

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
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertFor_first_error (version := .v1) opened split earlier failed

/-- A successful native stream agrees with the checked Parquet groups through exact EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertFor_readback (version := .v1) h

/-- The original stored payload splits into two exact raw level slices and the flag-selected value suffix. -/
theorem prepareV2_wire {limits : Limits} {checked : ListFile.Checked}
    {frame : Page.Frame} {info : Page.DataV2} {stored : Bytes} {sections : V2Sections}
    (h : prepareV2 limits checked frame info stored = .ok sections) :
    V2BodyWire checked frame info stored sections :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.prepareV2_wire h

/-- A V2 frame has exact slot, row and null counts, a row boundary, and ordered signed words. -/
theorem readV2Frame_wire {limits : Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readV2Frame limits checked budget frame = .ok events) :
    V2FrameWire limits checked frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readV2Frame_wire h

/-- A failed stored CRC precedes V2 level or suffix decoding. -/
theorem readV2Frame_checksum_error {limits : Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 0)
    (slots : info.numValues ≤ budget.slots) (expanded : frame.value.uncompressedSize ≤ budget.expanded)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readV2Frame limits checked budget frame = .error (.checksum cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readV2Frame_checksum_error kind encoding slots expanded failed

/-- Original V2 headers sum to the checked footer counts and the exact reconstructed null-slot count. -/
theorem readV2Group_counts {limits : Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroupFor .v2 limits checked ordinal expanded = .ok (rows, left)) :
    ∃ framed infos,
      ListFile.FramedGroupWire checked ordinal framed 1 ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) framed.frames infos ∧
      (infos.map (·.numValues)).sum = framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = pageNulls (rows.flatMap ListPage.rowEvents) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readV2Group_counts h

/-- A successful frame prefix preserves its live list and budgets for the original suffix. -/
theorem readFramesFor_append {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {earlier suffix : List Page.Frame} {ordinal : Nat} {budget left : Budget} {state next : State}
    (h : readFramesFor version limits checked column ordinal budget state earlier = .ok (left, next)) :
    readFramesFor version limits checked column ordinal budget state (earlier ++ suffix) =
      readFramesFor version limits checked column (ordinal + earlier.length) left next suffix :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_append h

/-- A failed page body retains its original ordinal and header offset. -/
theorem readFramesFor_read_error {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {cause : FrameError}
    (h : readFrameFor version limits checked column budget frame = .error cause) :
    readFramesFor version limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_read_error h

/-- A failed LIST transition retains its original page ordinal and offset. -/
theorem readFramesFor_feed_error {version : PageVersion} {limits : Limits} {checked : ListFile.Checked} {column : Footer.ColumnChunk}
    {frame : Page.Frame} {rest : List Page.Frame} {ordinal : Nat} {budget : Budget}
    {state : State} {events : List Event} {cause : ListPage.Error}
    (decoded : readFrameFor version limits checked column budget frame = .ok events)
    (failed : state.feed events = .error cause) :
    readFramesFor version limits checked column ordinal budget state (frame :: rest) =
      .error (.frame ordinal frame.header.start (.page cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readFramesFor_feed_error decoded failed

/-- The original group failure keeps the complete earlier groups and precedes IPC admission. -/
theorem convertFor_first_error {version : PageVersion} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsFor version limits checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroupFor version limits checked ordinal left = .error cause) :
    (convertFor version limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convertFor version limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertFor_first_error opened split earlier failed

/-- Exact checked frame-to-IPC readback for the explicitly selected page version. -/
theorem convertFor_readback {version : PageVersion} {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convertFor version limits source).wire = .ok wire) : Readback limits source wire version :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertFor_readback h

/-- The shared group checks bind the original frame walk and checked footer totals. -/
theorem readGroupUsing_checked {limits : Limits} {checked : ListFile.Checked} {walk : GroupWalk}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroupUsing limits checked walk ordinal expanded = .ok (rows, left)) :
    ∃ framed budget state,
      ListFile.FramedGroupWire checked ordinal framed 1 ∧
      walk framed.chunk ⟨framed.chunk.metadata.numValues.toNat, expanded⟩ framed.frames = .ok (budget, state) ∧
      budget.slots = 0 ∧ budget.expanded = left ∧ state.finish = rows ∧
      rows.length = framed.group.numRows.toNat ∧
      framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
      framed.group.numRows.toNat ≤ checked.limits.page.maxRows :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroupUsing_checked h

/-- A successful group prefix passes the remaining file budget to the suffix. -/
theorem readGroupsUsing_append {read : GroupReader} {checked : ListFile.Checked} {before after : List Nat}
    {expanded left : Nat} {groups : List (List Row)}
    (h : readGroupsUsing read checked expanded before = (groups, .ok left)) :
    readGroupsUsing read checked expanded (before ++ after) =
      let tail := readGroupsUsing read checked left after
      (groups ++ tail.1, tail.2) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.readGroupsUsing_append h

/-- A group reader's first failure precedes native IPC admission. -/
theorem convertUsing_first_error {read : GroupReader} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsUsing read checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : read checked ordinal left = .error cause) :
    (convertUsing limits read source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convertUsing limits read source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertUsing_first_error opened split earlier failed

/-- Checked group witnesses compose with exact native IPC readback. -/
theorem convertUsing_readback {read : GroupReader} {limits : Limits}
    {witness : ListFile.Checked → Nat → List Row → Nat → Prop} {source : Bytes} {wire : KBytes}
    (sound : ∀ {checked ordinal expanded left rows}, read checked ordinal expanded = .ok (rows, left) →
      witness checked ordinal rows (expanded - left) ∧ left ≤ expanded)
    (h : (convertUsing limits read source).wire = .ok wire) : ReadbackUsing limits read witness source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertUsing_readback sound h

/-- A selected typed source error preserves its group prefix and precedes native IPC admission. -/
theorem convertWith_first_error {ε σ ρ : Type} {errors : ConversionErrors ε σ ρ}
    {read : GroupReaderFor ε} {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : ε}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : readGroupsWith errors.groupFailure read checked limits.maxExpandedBytes before = (groups, .ok left))
    (failed : read checked ordinal left = .error cause) :
    (convertWith errors limits read source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (errors.groupFailure ordinal cause)⟩⟩ ∧
    (convertWith errors limits read source).wire = .error (errors.sourceFailure (errors.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertWith_first_error opened split earlier failed

/-- A typed group reader with per-group witnesses composes with checked native IPC readback. -/
theorem convertWith_readback {ε σ ρ : Type} {errors : ConversionErrors ε σ ρ}
    {read : GroupReaderFor ε} {limits : Limits}
    {witness : ListFile.Checked → Nat → List Row → Nat → Prop} {source : Bytes} {wire : KBytes}
    (sound : ∀ {checked ordinal expanded left rows}, read checked ordinal expanded = .ok (rows, left) →
      witness checked ordinal rows (expanded - left) ∧ left ≤ expanded)
    (h : (convertWith errors limits read source).wire = .ok wire) : ReadbackWith errors limits read witness source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.Snappy.convertWith_readback sound h

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy

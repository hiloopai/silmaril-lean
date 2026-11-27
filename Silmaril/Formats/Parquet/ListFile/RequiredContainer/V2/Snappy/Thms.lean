module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Correctness
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

open RequiredContainer (Checked)
open ListPage (Event Row)
open Silmaril.Relational

/-- The stored checksum and raw level spans belong to the original frame and snapshot. -/
theorem readSections_wire {limits : Limits} {checked : Checked} {frame : Page.Frame}
    {info : Page.DataV2} {sections : ListFile.Multi.Snappy.V2Sections}
    (kind : frame.value.kind = .dataV2 info)
    (h : readSections limits checked frame info = .ok sections) : StoredWire limits checked frame info sections :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.readSections_wire kind h

/-- The exact original suffix is one Snappy member or the unchanged raw bytes. -/
theorem suffix_wire {checked : Checked} {frame : Page.Frame} {info : Page.DataV2}
    {stored : Bytes} {sections : ListFile.Multi.Snappy.V2Sections}
    (wire : ListFile.Multi.Snappy.V2BodyWire checked frame info stored sections) :
    ∃ suffix,
      stored.toList = sections.repetition.toList ++ sections.definition.toList ++ suffix ∧
      suffix.length = frame.value.compressedSize - ListFile.Multi.Snappy.v2LevelBytes info ∧
      sections.scalars.length = frame.value.uncompressedSize - ListFile.Multi.Snappy.v2LevelBytes info ∧
      (if info.isCompressed then
        Payload.Decodes (frame.value.uncompressedSize - ListFile.Multi.Snappy.v2LevelBytes info)
          .snappy suffix sections.scalars.toList
      else suffix = sections.scalars.toList) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.suffix_wire wire

/-- The admitted page events carry stored-body, exact level and header-count evidence. -/
theorem readEvents_wire {limits : Limits} {checked : Checked} {frame : Page.Frame}
    {info : Page.DataV2} {events : List Event} (kind : frame.value.kind = .dataV2 info)
    (h : readEvents limits checked frame info = .ok events) : EventsWire limits checked frame info events :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.readEvents_wire kind h

/-- CRC refusal is returned before decoding the original level sections or
preparing the suffix, irrespective of their contents. -/
theorem readEvents_checksum_error {limits : Limits} {checked : Checked} {frame : Page.Frame}
    {info : Page.DataV2} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readEvents limits checked frame info = .error (.checksum cause) := by
  simp [readEvents, readSections, failed, Except.mapError, Bind.bind, Except.bind]

/-- The signed result preserves checked counts, original wire sections and present parents. -/
theorem readFrame_wire {limits : Limits} {checked : Checked} {framed : ListFile.FramedGroup}
    {frame : Page.Frame} {rows : List Row}
    (h : readFrame limits checked framed frame = .ok rows) : FrameWire limits checked framed frame rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.readFrame_wire h

/-- Original raw levels distinguish header slots, row starts and zero-value slots. -/
theorem frame_counts {limits : Limits} {checked : Checked} {framed : ListFile.FramedGroup}
    {frame : Page.Frame} {rows : List Row} (wire : FrameWire limits checked framed frame rows) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire limits checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.frame_counts wire

/-- The selected local Snappy chunk and singleton V2 frame witness the original group. -/
theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal = .ok rows) : GroupWire limits checked ordinal rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.readGroup_wire h

/-- Once header checks pass, a refused stored CRC precedes all body processing. -/
theorem readFrame_checksum_error {limits : Limits} {checked : Checked} {framed : FramedGroup}
    {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (codec : framed.chunk.metadata.codec = 1)
    (encoding : info.encoding = 0) (slots : framed.chunk.metadata.numValues = (info.numValues : Int))
    (groupRows : framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (pageRows : info.numRows ≤ checked.limits.page.maxRows)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked framed frame = .error (.snappy (.checksum cause)) := by
  simp [readFrame, readEvents, readSections, kind, codec, encoding, slots, Nat.not_lt.mpr groupRows, Nat.not_lt.mpr pageRows,
    failed, Except.mapError, Bind.bind, Except.bind]

/-- A body refusal keeps frame zero and its absolute offset in the selected group. -/
theorem readGroup_frame_error {limits : Limits} {checked : Checked} {ordinal : Nat}
    {framed : FramedGroup} {frame : Page.Frame} {cause : FrameError}
    (selected : checked.frameGroupFor 1 ordinal = .ok framed) (single : framed.frames = [frame])
    (failed : readFrame limits checked framed frame = .error cause) :
    readGroup limits checked ordinal = .error (.frame 0 frame.header.start cause) := by
  simp [readGroup, RequiredContainer.readGroupWith, selected, single, failed, Except.mapError, Bind.bind, Except.bind]

/-- Retain the original failed group and its successful predecessors before writer admission. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : RequiredContainer.openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (readGroup limits checked) = .ok groups)
    (failed : readGroup limits checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ RequiredContainer.rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  RequiredContainer.convertUsing_first_error opened split earlier failed

/-- Exact native V5 readback preserves field nullability, signed child slots, and EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  RequiredContainer.convertUsing_readback readGroup_wire h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

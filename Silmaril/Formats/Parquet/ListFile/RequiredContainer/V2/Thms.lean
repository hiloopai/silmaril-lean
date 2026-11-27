module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Correctness
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2

open ListPage (Event Row)
open RequiredContainer (Checked Limits SectionsWire)
open Silmaril.Relational

/-- The three advertised raw sections partition the original stored body. -/
theorem readSections_wire {limits : ListPage.Limits} {source : Bytes} {frame : Page.Frame}
    {info : Page.DataV2} {sections : Sections} (kind : frame.value.kind = .dataV2 info)
    (h : readSections limits source frame info = .ok sections) : RawWire limits source frame info sections :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.readSections_wire kind h

/-- The exact signed PLAIN suffix carries one word per physical value slot in order. -/
theorem sections_physical {slots : Nat} {repetition definition scalars : Bytes} {events : List Event}
    (wire : SectionsWire slots repetition definition scalars events) :
    Plain.decodeInt32 (slots - missingSlots events) scalars = .ok (events.filterMap (fun event => event.wire.2.2)) ∧
    scalars.length = 4 * (slots - missingSlots events) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.sections_physical wire

/-- The original V2 frame yields exact ordered rows, raw levels and signed values. -/
theorem readFrame_wire {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (h : readFrame checked framed frame = .ok rows) : FrameWire checked framed frame rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.readFrame_wire h

/-- Raw levels distinguish header slots, repetition-zero rows and zero-value slots. -/
theorem frame_counts {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (wire : FrameWire checked framed frame rows) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.frame_counts wire

/-- The original selected chunk and singleton V2 frame witness the group result. -/
theorem readGroup_wire {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup checked ordinal = .ok rows) : GroupWire checked ordinal rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.readGroup_wire h

/-- A body refusal keeps the original singleton frame coordinates. -/
theorem readGroup_frame_error {checked : Checked} {ordinal : Nat}
    {framed : FramedGroup} {frame : Page.Frame} {cause : FrameError}
    (selected : checked.frameGroup ordinal = .ok framed) (single : framed.frames = [frame])
    (failed : readFrame checked framed frame = .error cause) :
    readGroup checked ordinal = .error (.frame 0 frame.header.start cause) := by
  simp [readGroup, RequiredContainer.readGroupUsing, selected, single, failed, Except.mapError, Bind.bind, Except.bind]

/-- The first original group error preserves its earlier batches ahead of the writer. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : RequiredContainer.openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (readGroup checked) = .ok groups)
    (failed : readGroup checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ RequiredContainer.rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  RequiredContainer.convertUsing_first_error opened split earlier failed

/-- Required native Arrow field, signed nullable child order, and exact EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  RequiredContainer.convertUsing_readback readGroup_wire h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2

module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Correctness
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

open ListPage (Event Row State)
open Silmaril.Relational
open RequiredContainer (Checked)

theorem readFrame_wire {checked : Checked} {remaining : Nat} {frame : Page.Frame}
    {events : List Event} (h : readFrame checked remaining frame = .ok events) :
    FrameWire checked frame events ∧ events.length ≤ remaining :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.readFrame_wire h

/-- Exact raw level extents, the rep-zero boundary and signed scalar suffix. -/
theorem frame_levels {checked : Checked} {frame : Page.Frame} {events : List Event}
    (h : FrameWire checked frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧ sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
      Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
        .ok (events.filterMap (fun event => event.wire.2.2)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.frame_levels h

/-- The original frame chain yields ordered rows and three separate totals. -/
theorem readGroup_wire {maxGroupSlots : Nat} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup maxGroupSlots checked ordinal = .ok rows) : GroupWire maxGroupSlots checked ordinal rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.readGroup_wire h

/-- The first decode or stitch error retains the original page ordinal and offset. -/
theorem readGroup_frame_error {maxGroupSlots : Nat} {checked : Checked} {ordinal : Nat}
    {framed : ListFile.FramedGroup} {before after : List Page.Frame} {frame : Page.Frame}
    {remaining : Nat} {state : State} {cause : FrameError}
    (selected : checked.frameGroup ordinal = .ok framed)
    (slots : framed.chunk.metadata.numValues.toNat ≤ maxGroupSlots)
    (rows : framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (order : framed.frames = before ++ frame :: after)
    (earlier : readFrames checked before 0 framed.chunk.metadata.numValues.toNat State.empty = .ok (remaining, state))
    (failed : readFrame checked remaining frame = .error cause ∨
      ∃ events error, readFrame checked remaining frame = .ok events ∧
        state.feed events = .error error ∧ cause = .data (.page error)) :
    readGroup maxGroupSlots checked ordinal = .error (.frame before.length frame.header.start cause) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.readGroup_frame_error selected slots rows order earlier failed

/-- A late source failure retains the completed earlier groups and precedes writer admission. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : RequiredContainer.openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (readGroup limits.maxGroupSlots checked) = .ok groups)
    (failed : readGroup limits.maxGroupSlots checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ RequiredContainer.rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  RequiredContainer.convertUsing_first_error opened split earlier failed

/-- Required parent validity, ordered nullable children, and exact native EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  RequiredContainer.convertUsing_readback readGroup_wire h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

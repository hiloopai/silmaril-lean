module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Correctness
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms

public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi

open ListPage (Event Row State)
open Silmaril.Relational
open RequiredContainer (Checked)
open Snappy (StoredWire)

/-- The page witness binds the original admitted V2 header and checksum-checked events. -/
theorem readFrame_wire {limits : Limits} {checked : Checked} {remaining : Nat} {frame : Page.Frame}
    {events : List Event} (h : readFrame limits checked remaining frame = .ok events) :
    FrameWire limits checked frame events ∧ events.length ≤ remaining :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.readFrame_wire h

/-- Original raw level streams begin at a row boundary and determine the signed scalar extent. -/
theorem frame_levels {limits : Limits} {checked : Checked} {frame : Page.Frame} {events : List Event}
    (h : FrameWire limits checked frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire limits.toSnappyLimits checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧ sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
      Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
        .ok (events.filterMap (fun event => event.wire.2.2)) :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.frame_levels h

/-- Original codec-one chunk and ordered frame chain witness all three independent totals. -/
theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal = .ok rows) : GroupWire limits checked ordinal rows :=
  Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.readGroup_wire h

/-- After header and count-cap checks, a checksum refusal precedes level
decoding and raw or Snappy suffix preparation. -/
theorem readFrame_checksum_error {limits : Limits} {checked : Checked} {remaining : Nat}
    {frame : Page.Frame} {info : Page.DataV2} {cause : Page.Checksum.Error}
    (kind : frame.value.kind = .dataV2 info) (encoding : info.encoding = 0)
    (slots : info.numValues ≤ remaining) (rows : info.numRows ≤ checked.limits.page.maxRows)
    (failed : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .error cause) :
    readFrame limits checked remaining frame = .error (.checksum cause) := by
  simp [readFrame, kind, encoding, Nat.not_lt.mpr slots, Nat.not_lt.mpr rows, Snappy.readEvents_checksum_error failed]

/-- The first body or stitch refusal preserves its original coordinates. -/
theorem readGroup_frame_error {limits : Limits} {checked : Checked} {ordinal : Nat}
    {framed : ListFile.FramedGroup} {before after : List Page.Frame} {frame : Page.Frame}
    {remaining : Nat} {state : State} {cause : FrameError}
    (selected : checked.frameGroupFor 1 ordinal = .ok framed)
    (slots : framed.chunk.metadata.numValues.toNat ≤ limits.maxGroupSlots)
    (rows : framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (order : framed.frames = before ++ frame :: after)
    (earlier : readFrames limits checked before 0 framed.chunk.metadata.numValues.toNat State.empty =
      .ok (remaining, state))
    (failed : readFrame limits checked remaining frame = .error cause ∨
      ∃ events error, readFrame limits checked remaining frame = .ok events ∧
        state.feed events = .error error ∧ cause = .page error) :
    readGroup limits checked ordinal = .error (.frame before.length frame.header.start cause) :=
  V2.Multi.readGroupWith_frame_error selected slots rows order earlier failed

/-- A late source failure retains the completed earlier groups and precedes writer admission. -/
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

/-- Required parent validity, ordered nullable children, and exact native EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  RequiredContainer.convertUsing_readback readGroup_wire h

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi

module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Admission

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The bind uses the original schema and ordinal on the opt-in checked snapshot. -/
theorem openLeaf_exact {profile : AnnotationProfile} {limits : Snapshot.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : openLeaf profile limits input ordinal = .ok bound) :
    ∃ snapshot, Snapshot.checkPageLessTimestamp limits input = .ok snapshot ∧
      bindWith profile limits.footer snapshot ordinal = .ok bound :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.openLeaf_exact opened

/-- A successful open checks all source caps before group decoding. -/
theorem openBound_sound {profile : AnnotationProfile} {limits : Events.ToIpc.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : openBound profile limits input ordinal = .ok bound) :
    openLeaf profile limits.snapshot input ordinal = .ok bound ∧ input.length ≤ limits.maxFileBytes ∧
      bound.snapshot.groupCount ≤ limits.maxGroups ∧
      bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows :=
  Events.ToIpc.openBoundUsing_sound opened

/-- Each original admitted page-less ordinal contributes one empty slot list. -/
theorem readGroup_empty {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {group : Footer.RowGroup}
    (found : bound.snapshot.groupAt index = some group)
    (admitted : bound.snapshot.admitsPageLessTimestamp group = true) :
    readGroup limits leafLimits bound index = .ok [] := by
  simp [readGroup, found, admitted]

/-- Framed groups run the existing plan on the same checked source and ordinal. -/
theorem readGroup_framed {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {group : Footer.RowGroup}
    (found : bound.snapshot.groupAt index = some group)
    (framed : bound.snapshot.admitsPageLessTimestamp group = false) :
    readGroup limits leafLimits bound index = MixedGroups.readGroup limits leafLimits bound index := by
  simp [readGroup, found, framed]

/-- Missing ordinals still report a typed group error. -/
theorem readGroup_missing {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} (missing : bound.snapshot.groupAt index = none) :
    readGroup limits leafLimits bound index = .error (.groupIndex index) := by
  simp [readGroup, missing]

/-- The trace uses the original footer groups including admitted no-frame groups in footer order. -/
theorem readBound_reference (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Events.referenceGroupsWith (readGroup limits leafLimits bound)
      (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Events.rows bound), reference.2⟩⟩ :=
  Events.readBoundWith_reference bound (readGroup limits leafLimits bound)

/-- A group error retains precisely the earlier complete footer groups. -/
theorem readBound_first_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The native Arrow stream reads back to the retained descriptor and the
ordered nullable counts of every complete footer group. -/
theorem convert_readback {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert profile limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, openBound profile inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroupsUsing_readback written

/-- The first failing footer group forwards the same cause before the IPC
writer attempts admission. -/
theorem convert_first_error {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : openBound profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert profile limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroupsUsing_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess

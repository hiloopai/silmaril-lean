module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Readback

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

theorem openBoundUsing_sound {limits : Limits} {input : Bytes} {bound : Leaf.Bound}
    {bind : Bytes → Except Leaf.Error Leaf.Bound}
    (opened : openBoundUsing limits input bind = .ok bound) :
    bind input = .ok bound ∧ input.length ≤ limits.maxFileBytes ∧
      bound.snapshot.groupCount ≤ limits.maxGroups ∧
      bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.openBoundUsing_sound opened

/-- A successful open checks the original file, selected leaf and resource bounds. -/
theorem openBoundWith_sound {profile : AnnotationProfile} {limits : Limits} {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : openBoundWith profile limits input ordinal = .ok bound) :
    Leaf.openLeafWith profile limits.snapshot input ordinal = .ok bound ∧ input.length ≤ limits.maxFileBytes ∧
      bound.snapshot.groupCount ≤ limits.maxGroups ∧
      bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.openBoundWith_sound opened

/-- A successful open checks the original file, selected leaf and resource bounds. -/
theorem openBound_sound {limits : Limits} {input : Bytes} {ordinal : Nat} {bound : Leaf.Bound}
    (opened : openBound limits input ordinal = .ok bound) :
    Leaf.openLeaf limits.snapshot input ordinal = .ok bound ∧ input.length ≤ limits.maxFileBytes ∧
      bound.snapshot.groupCount ≤ limits.maxGroups ∧
      bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows :=
  openBoundWith_sound (profile := .modernOnly) opened

/-- The selected output keeps the original unit and epoch interpretation. -/
theorem selectedBinding_exact (bound : Leaf.Bound) :
    (selectedBinding bound).name = bound.binding.leaf.name ∧
      (selectedBinding bound).nullable = (bound.binding.leaf.repetition == some .optional) ∧
      (selectedBinding bound).metadata.unit = bound.binding.descriptor.unit.tickUnit ∧
      (selectedBinding bound).metadata.timezone = (if bound.binding.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (selectedBinding bound).metadata.kind = bound.binding.descriptor.kind :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.selectedBinding_exact bound

/-- An original group failure is forwarded without attempting writer admission. -/
theorem emit_trace_error (limits : Arrow.ObservationLimits) {schema : Scan.Schema String Leaf.Events.Kind}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Events.Error} {cause : Leaf.Events.Error}
    (failed : trace.termination = .readError cause) :
    emit limits (.ok ⟨schema, trace⟩) = .error (.source cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.emit_trace_error limits failed

/-- The reader recovers the exact event descriptor and original batch slot lists. -/
theorem emit_readback {limits : Arrow.ObservationLimits} {schema : Scan.Schema String Leaf.Events.Kind}
    {trace : Arrow.Events.Trace schema Leaf.Events.Cell Leaf.Events.Error} {wire : KBytes}
    (one : schema.width = 1) (ended : trace.termination = .eos)
    (written : emit limits (.ok ⟨schema, trace⟩) = .ok wire) :
    let column : Fin schema.width := ⟨0, by omega⟩
    ∃ result, Arrow.TimestampStream.read limits.ipc wire = .ok result ∧
      result.binding = bindingAt schema column ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        (batchesAt trace column).map Arrow.TimestampBatch.Writer.tickCounts :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.emit_readback one ended written

theorem convertGroupsUsing_first_error {source : Except Error Leaf.Bound}
    {outputLimits : Arrow.ObservationLimits}
    {read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)}
    {index : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : source = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (read bound) = .ok groups)
    (failed : read bound index = .error cause) :
    convertGroupsUsing source outputLimits read = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertGroupsUsing_first_error opened split earlier failed

/-- The first failed footer group determines the exact original source error. -/
theorem convertGroups_first_error {profile : AnnotationProfile} {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)}
    {input : Bytes} {ordinal index : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : openBoundWith profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (read bound) = .ok groups)
    (failed : read bound index = .error cause) :
    convertGroups profile inputLimits outputLimits input ordinal read = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertGroups_first_error opened split earlier failed

/-- The first failed footer group determines the exact original source error. -/
theorem convertWith_first_error {profile : AnnotationProfile} {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : openBoundWith profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup inputLimits.leaf bound) = .ok groups)
    (failed : Leaf.readGroup inputLimits.leaf bound index = .error cause) :
    convertWith profile inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertWith_first_error opened split earlier failed

/-- The first failed footer group determines the exact original source error. -/
theorem convert_first_error {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Leaf.Bound}
    {before after : List Nat} {groups : List (Leaf.Slots bound)} {cause : Leaf.Error}
    (opened : openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup inputLimits.leaf bound) = .ok groups)
    (failed : Leaf.readGroup inputLimits.leaf bound index = .error cause) :
    convert inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) :=
  convertWith_first_error (profile := .modernOnly) opened split earlier failed

theorem convertGroupsUsing_readback {source : Except Error Leaf.Bound}
    {outputLimits : Arrow.ObservationLimits}
    {read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)}
    {wire : KBytes}
    (written : convertGroupsUsing source outputLimits read = .ok wire) :
    ∃ bound : Leaf.Bound, source = .ok bound ∧
      let reference := Leaf.Events.referenceGroupsWith (read bound) (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertGroupsUsing_readback written

/-- Successful IPC reads back to the same leaf descriptor and complete original
group observations in footer order. -/
theorem convertGroups_readback {profile : AnnotationProfile} {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convertGroups profile inputLimits outputLimits input ordinal read = .ok wire) :
    ∃ bound : Leaf.Bound, openBoundWith profile inputLimits input ordinal = .ok bound ∧
      let reference := Leaf.Events.referenceGroupsWith (read bound) (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertGroups_readback written

/-- Successful IPC reads back to the same leaf descriptor and complete original
group observations in footer order. -/
theorem convertWith_readback {profile : AnnotationProfile} {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convertWith profile inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, openBoundWith profile inputLimits input ordinal = .ok bound ∧
      let reference := Leaf.Events.referenceGroups inputLimits.leaf bound (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.convertWith_readback written

/-- Successful IPC reads back to the same leaf descriptor and complete original
group observations in footer order. -/
theorem convert_readback {inputLimits : Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, openBound inputLimits input ordinal = .ok bound ∧
      let reference := Leaf.Events.referenceGroups inputLimits.leaf bound (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  convertWith_readback (profile := .modernOnly) written

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

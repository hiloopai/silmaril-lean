module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs
public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
import Silmaril.Formats.Arrow.TimestampStream.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Exact

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds

open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Internal (rescaleSlot rescaleGroup)

/-- The output keeps the selected leaf and exact original epoch interpretation in seconds. -/
theorem binding_exact (bound : Bound) :
    (binding bound).name = bound.binding.leaf.name ∧
      (binding bound).nullable = (bound.binding.leaf.repetition == some .optional) ∧
      (binding bound).metadata.unit = .second ∧
      (binding bound).metadata.timezone = (if bound.binding.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (binding bound).metadata.kind = bound.binding.descriptor.kind :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.binding_exact bound

/-- A present millis count is refused precisely when it is off the whole-second grid. -/
theorem millis_nonintegral_iff {kind : Silmaril.Numeric.Timestamp.Kind} (value : Ticks kind .millisecond) :
    value.rescale .second = none ↔ value.ticks % 1000 ≠ 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.millis_nonintegral_iff value

/-- Successful rescaling preserves the exact same-kind nanosecond coordinates. -/
theorem millis_exact {kind : Silmaril.Numeric.Timestamp.Kind} {value : Ticks kind .millisecond} {seconds : Ticks kind .second}
    (read : value.rescale .second = some seconds) :
    value.denote = seconds.denote ∧ value.ticks = seconds.ticks * 1000 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.millis_exact read

/-- An off-grid count returns its original group and logical slot, including preceding nulls. -/
theorem rescaleSlot_nonintegral {bound : Bound} {group slot : Nat}
    (unit : bound.binding.descriptor.unit = .millis) (value : Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding)
    (offGrid : Ticks.ticks value % 1000 ≠ 0) :
    rescaleSlot bound group slot (some value) = .error (.nonintegral group slot (Ticks.ticks value)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.rescaleSlot_nonintegral unit value offGrid

/-- Successful rescaling recovers the exact nullable counts and original group shape. -/
theorem rescaleGroups_exact {bound : Bound} {groups : List (Slots bound)}
    {batches : List (Arrow.TimestampBatch.Column (binding bound))}
    (rescaled : rescaleGroups bound groups = .ok batches) :
    bound.snapshot.metadata.schema.length = 2 ∧ bound.binding.descriptor.unit = .millis ∧
      FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
        some (batches.map Arrow.TimestampBatch.Writer.tickCounts) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.rescaleGroups_exact rescaled

/-- Successful source reads are the same original reads used to certify the canonical writer. -/
theorem readGroups_agree {limits : Leaf.Limits} {bound : Bound} {groups : List (Slots bound)} :
    readGroups limits bound = .ok groups ↔ FromIpc.Internal.readGroups limits bound = .ok groups :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.readGroups_agree

/-- The first original group failure preempts interpreting any counts or writing IPC. -/
theorem convert_first_source_error {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {prefixGroups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup inputLimits.leaf bound) = .ok prefixGroups)
    (failed : Leaf.readGroup inputLimits.leaf bound index = .error cause) :
    convert inputLimits outputLimits input = .error (.source (.source (.groupFailure index cause))) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.convert_first_source_error opened split earlier failed

/-- Within an admitted group, the first failing slot retains its original indexed cause. -/
theorem rescaleGroup_first_error {bound : Bound} {group slot : Nat}
    {value : Option (Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding)} {slots : Slots bound}
    {before after : List (Option (Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding) × Nat)}
    {output : Arrow.TimestampBatch.Column (binding bound)} {cause : Leaf.Events.ToIpc.Seconds.Error}
    (split : slots.zipIdx = before ++ (value, slot) :: after)
    (earlier : before.mapM (fun (item, index) => rescaleSlot bound group index item) = .ok output)
    (failed : rescaleSlot bound group slot value = .error cause) :
    rescaleGroup bound group slots = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.rescaleGroup_first_error split earlier failed

/-- After the original source is read, the first nonintegral group preempts IPC emission. -/
theorem convert_first_rescale_error {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {bound : Bound}
    {groups : List (Slots bound)} {group : Nat} {slots : Slots bound}
    {before after : List (Slots bound × Nat)}
    {output : List (Arrow.TimestampBatch.Column (binding bound))} {cause : Leaf.Events.ToIpc.Seconds.Error}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound)
    (read : readGroups inputLimits.leaf bound = .ok groups)
    (fields : bound.snapshot.metadata.schema.length = 2)
    (unit : bound.binding.descriptor.unit = .millis)
    (split : groups.zipIdx = before ++ (slots, group) :: after)
    (earlier : before.mapM (fun (items, i) => rescaleGroup bound i items) = .ok output)
    (failed : rescaleGroup bound group slots = .error cause) :
    convert inputLimits outputLimits input = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.convert_first_rescale_error opened read fields unit split earlier failed

/-- Checked native IPC readback preserves the original binding and exact rescaled nullable batches. -/
theorem convert_readback {inputLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {wire : KBytes} (written : convert inputLimits outputLimits input = .ok wire) :
    ∃ bound groups result,
      Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound ∧
      readGroups inputLimits.leaf bound = .ok groups ∧
      bound.snapshot.metadata.schema.length = 2 ∧ bound.binding.descriptor.unit = .millis ∧
      Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧ result.binding = binding bound ∧
      FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
        some (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.convert_readback written

/-- With matched intermediate snapshot and leaf limits, two successful legs recover the complete seconds observation. -/
theorem ipc_roundtrip {ipc : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {writeLimits : FromIpc.Limits} {readLimits : Leaf.Events.ToIpc.Limits}
    {input output : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (toParquet : FromIpc.Seconds.convert ipc writeLimits input = .ok middle)
    (toIpc : convert readLimits outputLimits middle = .ok output) :
    ∃ original prepared bound groups result,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      FromIpc.Seconds.prepare original = .ok prepared ∧
      Leaf.openLeaf writeLimits.snapshot middle 1 = .ok bound ∧
      FromIpc.Internal.readGroups writeLimits.leaf bound = .ok groups ∧
      FromIpc.Internal.ReadbackMatches prepared bound groups ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok result ∧
      Arrow.TimestampStream.Writer.descriptor result.binding =
        Arrow.TimestampStream.Writer.descriptor original.binding ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        original.batches.map Arrow.TimestampBatch.Writer.tickCounts :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.ipc_roundtrip sameSnapshot sameLeaf toParquet toIpc

/-- The emitted stream has a checked Schema and exact EOS after its final batch. -/
theorem convert_output_eos {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {wire : KBytes}
    (written : convert inputLimits outputLimits input = .ok wire) :
    wire.wf = true ∧ ∃ field start batches,
      Arrow.TimestampStream.readSchema outputLimits.ipc wire = .ok (field, start) ∧
      Arrow.TimestampStream.BatchesWire outputLimits.ipc wire field outputLimits.ipc.batches start batches := by
  obtain ⟨_, _, result, _, _, _, _, read, _⟩ := convert_readback written
  obtain ⟨wf, start, schema, batches⟩ := (Arrow.TimestampStream.read_iff outputLimits.ipc wire result).mp read
  exact ⟨wf, result.binding, start, result.batches, schema, batches⟩

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds

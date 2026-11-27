module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
import Silmaril.Formats.Arrow.TimestampStream.Thms
import Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.Exact

public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds

open Silmaril.Numeric.Timestamp (Kind Ticks)
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Internal (rescaleSlot rescaleBatch)

/-- Successful admission preserves exactly the original absent or UTC timezone. -/
theorem admit_exact {binding : Arrow.TimestampBatch.Binding} {descriptor : Descriptor}
    (accepted : admit binding = .ok descriptor) :
    binding.metadata.unit = .second ∧ descriptor.unit = .millis ∧
      binding.metadata.timezone = (if descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      descriptor.kind = binding.metadata.kind :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.admit_exact accepted

/-- Mathematical seconds and their scaled millis denote the same exact time. -/
theorem rescale_seconds {kind : Kind} (value : Ticks kind .second) :
    value.rescale .millisecond = some ⟨value.ticks * 1000⟩ :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.rescale_seconds value

/-- Exact rescaling on the admitted image recovers the original seconds. -/
theorem seconds_inverse {kind : Kind} (value : Ticks kind .second) :
    (⟨value.ticks * 1000⟩ : Ticks kind .millisecond).rescale .second = some value :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.seconds_inverse value

/-- The signed payload overflows exactly outside these inclusive seconds endpoints. -/
theorem overflow_iff {kind : Kind} (value : Ticks kind .second) :
    value.toInt64 .millisecond = .error .outOfRange ↔
      value.ticks < -9223372036854775 ∨ 9223372036854775 < value.ticks :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.overflow_iff value

/-- Overflow keeps the original batch and logical slot, including preceding nulls. -/
theorem rescaleSlot_overflow {binding : Arrow.TimestampBatch.Binding}
    {batch slot : Nat} (unit : binding.metadata.unit = .second)
    (value : Arrow.TimestampBatch.Value binding)
    (outside : Ticks.ticks value < -9223372036854775 ∨ 9223372036854775 < Ticks.ticks value) :
    rescaleSlot batch slot (some value) = .error (.rescale batch slot .outOfRange) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.rescaleSlot_overflow unit value outside

/-- Preparation preserves the original field and every ordered nullable batch. -/
theorem prepare_exact {original : Arrow.TimestampStream.Stream} {prepared : FromIpc.Source}
    (accepted : prepare original = .ok prepared) :
    original.binding.metadata.unit = .second ∧ prepared.descriptor.unit = .millis ∧
      original.binding.metadata.timezone =
        (if prepared.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      prepared.stream.binding = millisecondBinding original.binding ∧
      prepared.stream.batches.map FromIpc.Internal.counts =
        (original.batches.map FromIpc.Internal.counts).map (List.map (Option.map (· * 1000))) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.prepare_exact accepted

/-- An original source failure preempts metadata admission, rescaling and sink work. -/
theorem convert_source_error {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes}
    {cause : Arrow.TimestampStream.Error} (bytes : input.len ≤ limits.maxInputBytes)
    (failed : Arrow.TimestampStream.read ipc input = .error cause) :
    convert ipc limits input = .error (.source cause) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.convert_source_error bytes failed

/-- The first failing slot keeps its original indexed cause. -/
theorem rescaleBatch_first_error {binding : Arrow.TimestampBatch.Binding}
    {batch slot : Nat} {value : Option (Arrow.TimestampBatch.Value binding)}
    {slots : Arrow.TimestampBatch.Column binding}
    {before after : List (Option (Arrow.TimestampBatch.Value binding) × Nat)}
    {output : Arrow.TimestampBatch.Column (millisecondBinding binding)} {cause : FromIpc.Seconds.Error}
    (split : slots.zipIdx = before ++ (value, slot) :: after)
    (earlier : before.mapM (fun (value, index) => rescaleSlot batch index value) = .ok output)
    (failed : rescaleSlot batch slot value = .error cause) :
    rescaleBatch batch slots = .error cause :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.rescaleBatch_first_error split earlier failed

/-- After exact source read and admission, the first failing batch retains its original cause. -/
theorem convert_first_rescale_error {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes}
    {original : Arrow.TimestampStream.Stream} {annotation : Descriptor}
    {batch : Nat} {slots : Arrow.TimestampBatch.Column original.binding}
    {before after : List (Arrow.TimestampBatch.Column original.binding × Nat)}
    {output : List (Arrow.TimestampBatch.Column (millisecondBinding original.binding))}
    {cause : FromIpc.Seconds.Error} (bytes : input.len ≤ limits.maxInputBytes)
    (read : Arrow.TimestampStream.read ipc input = .ok original)
    (admitted : admit original.binding = .ok annotation)
    (split : original.batches.zipIdx = before ++ (slots, batch) :: after)
    (earlier : before.mapM (fun (items, index) => rescaleBatch index items) = .ok output)
    (failed : rescaleBatch batch slots = .error cause) :
    convert ipc limits input = .error cause :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.convert_first_rescale_error bytes read admitted split earlier failed

/-- Checked Parquet readback returns millis under the retained field and exact slot shape. -/
theorem convert_readback {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ original prepared bound groups,
      Arrow.TimestampStream.read ipc input = .ok original ∧ prepare original = .ok prepared ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      FromIpc.Internal.readGroups limits.leaf bound = .ok groups ∧
      FromIpc.Internal.ReadbackMatches prepared bound groups ∧
      groups.map FromIpc.Internal.counts =
        (original.batches.map FromIpc.Internal.counts).map (List.map (Option.map (· * 1000))) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.convert_readback written

/-- Inverting the exact output counts recovers the original nullable second batches. -/
theorem convert_inverse {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ original bound groups,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      FromIpc.Internal.readGroups limits.leaf bound = .ok groups ∧
      recover original.binding.metadata.kind (groups.map FromIpc.Internal.counts) =
        some (original.batches.map FromIpc.Internal.counts) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds.convert_inverse written

/-- Successful output certifies that the original seconds stream reached exact EOS. -/
theorem convert_source_eos {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    input.wf = true ∧ ∃ binding start batches,
      Arrow.TimestampStream.readSchema ipc input = .ok (binding, start) ∧
      Arrow.TimestampStream.BatchesWire ipc input binding ipc.batches start batches := by
  obtain ⟨original, _, _, _, read, _⟩ := convert_readback written
  obtain ⟨wf, start, schema, batches⟩ := (Arrow.TimestampStream.read_iff ipc input original).mp read
  exact ⟨wf, original.binding, start, original.batches, schema, batches⟩

end Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds

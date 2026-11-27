module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Events

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The selected codec comes from the original footer column admitted by the leaf reader. -/
theorem selectedCodec_exact {encoding : Leaf.ChunkEncoding} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {chunk : Leaf.Chunk}
    (selected : selectChunkWith encoding leafLimits bound index = .ok chunk) :
    selectedCodec bound index = .ok chunk.column.metadata.codec :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.selectedCodec_exact selected

/-- A failed footer lookup retains its original typed cause. -/
theorem readGroup_selection_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : selectedCodec bound index = .error cause) :
    readGroup limits leafLimits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.readGroup_selection_error failed

/-- An unsupported selected codec retains its original numeric ID. -/
theorem readGroup_unsupported_codec {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {codec : Int} (selected : selectedCodec bound index = .ok codec)
    (gzip : codec ≠ Payload.Codec.gzip.id) (zstd : codec ≠ Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index = .error (.unsupportedCodec codec) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.readGroup_unsupported_codec selected gzip zstd

/-- Codec 2 preserves the complete GZIP dispatcher result. -/
theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.gzip leafLimits bound index).mapError .gzip :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.readGroup_gzip_agrees selected

/-- Codec 6 preserves the complete Zstandard dispatcher result. -/
theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.zstd leafLimits bound index).mapError .zstd :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.readGroup_zstd_agrees selected

/-- The chosen route keeps the strict original wire and slot witnesses on the same snapshot. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.readGroup_wire read

/-- The shared collector retains exactly the groups preceding a typed failure. -/
theorem traceUsing_first_error {ε δ : Type} {bound : Bound} {read : Nat → Except ε (Slots bound)}
    {tag : Nat → ε → δ} {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : ε}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM read = .ok groups) (failed : read index = .error cause) :
    traceUsing bound read tag =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (tag index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.traceUsing_first_error split earlier failed

/-- Source EOS witnesses every completed group in footer order. -/
theorem traceUsing_eos {ε δ : Type} {bound : Bound} {read : Nat → Except ε (Slots bound)} {tag : Nat → ε → δ}
    (ended : (traceUsing bound read tag).termination = .eos) :
    ∃ groups, (List.range bound.snapshot.groupCount).mapM read = .ok groups ∧
      traceUsing bound read tag = ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.traceUsing_eos ended

/-- Native IPC recovers the selected binding and ordered signed nullable ticks. -/
theorem emitUsing_readback {ε δ : Type} {bound : Bound} {output : Arrow.ObservationLimits}
    {events : Arrow.Events.Trace (Leaf.Events.schema bound) Leaf.Events.Cell ε}
    {sourceError : ε → δ} {closed : δ} {writerError : Arrow.TimestampStream.Writer.Error → δ}
    {groups : List (Slots bound)} {wire : KBytes}
    (complete : events = ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩)
    (written : emitUsing output bound events sourceError closed writerError = .ok wire) :
    ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
      result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        groups.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.emitUsing_readback complete written

/-- The first failed group retains exactly the earlier complete event batches. -/
theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.trace_first_error split earlier failed

/-- The original indexed source failure precedes IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.convert_first_error opened split earlier failed

/-- Native IPC reads through EOS with the original footer groups and selected descriptor and ticks. -/
theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      List.Forall₂ (GroupWire limits inputLimits.leaf bound) (List.range bound.snapshot.groupCount) groups ∧
      trace limits inputLimits.leaf bound =
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

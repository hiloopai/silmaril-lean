module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Events
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The dispatch selector reads the original selected footer column's codec. -/
theorem selectedCodec_exact {encoding : Leaf.ChunkEncoding} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {chunk : Leaf.Chunk}
    (selected : selectChunkWith encoding leafLimits bound index = .ok chunk) :
    V2.selectedCodec bound index = .ok chunk.column.metadata.codec :=
  V2.selectedCodec_exact selected

/-- Codec 1 preserves the complete strict Snappy dispatcher result. -/
theorem readGroup_snappy_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.snappy.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Snappy.Dispatch.V2.readGroup limits.snappy leafLimits bound index).mapError .snappy :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.readGroup_snappy_agrees selected

/-- Every non-Snappy selection preserves the complete two-codec result. -/
theorem readGroup_twoCodec_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (other : Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    readGroup limits leafLimits bound index =
      (Leaf.MixedCodec.V2.readGroup limits.twoCodec leafLimits bound index).mapError .twoCodec :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.readGroup_twoCodec_agrees other

/-- Codec 2 preserves the complete strict GZIP dispatcher result. -/
theorem readGroup_gzip_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Gzip.Dispatch.V2.readGroup limits.twoCodec.gzip leafLimits bound index).mapError
        (GroupError.twoCodec ∘ Leaf.MixedCodec.V2.GroupError.gzip) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.readGroup_gzip_agrees selected

/-- Codec 6 preserves the complete strict Zstandard dispatcher result. -/
theorem readGroup_zstd_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits leafLimits bound index =
      (Leaf.Zstd.Dispatch.V2.readGroup limits.twoCodec.zstd leafLimits bound index).mapError
        (GroupError.twoCodec ∘ Leaf.MixedCodec.V2.GroupError.zstd) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.readGroup_zstd_agrees selected

/-- Each completed group retains its strict original frame and nullable slot witnesses. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.readGroup_wire read

/-- The first failed source group retains exactly the earlier complete batches. -/
theorem trace_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    trace limits leafLimits bound =
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.trace_first_error split earlier failed

/-- The original indexed source failure precedes IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.convert_first_error opened split earlier failed

/-- Native IPC reads through EOS with the selected descriptor and original signed nullable ticks. -/
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
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.convert_readback written

/-- A source with non-Snappy selections preserves the previous batches and typed outcome. -/
theorem trace_twoCodec_agrees {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    (other : ∀ index ∈ List.range bound.snapshot.groupCount,
      Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    trace limits leafLimits bound =
      let prev := Leaf.MixedCodec.V2.trace limits.twoCodec leafLimits bound
      ⟨prev.batches, terminationOfTwoCodec prev.termination⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.trace_twoCodec_agrees other

/-- A source with non-Snappy selections preserves the previous complete converter result. -/
theorem convert_twoCodec_agrees {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat}
    (other : ∀ bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound →
      ∀ index ∈ List.range bound.snapshot.groupCount,
        Leaf.MixedCodec.V2.selectedCodec bound index ≠ .ok Payload.Codec.snappy.id) :
    convert limits inputLimits output input ordinal =
      (Leaf.MixedCodec.V2.convert limits.twoCodec inputLimits output input ordinal).mapError Error.ofTwoCodec :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.convert_twoCodec_agrees other

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy

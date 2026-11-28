module

public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Thms
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy

open Silmaril.Relational

/-- Outside codec 1 the complete result agrees with the existing two-codec reader. -/
theorem readGroup_twoCodec_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (outsideSnappy : ∀ actual, selectedCodec bound index = .ok actual → actual ≠ Payload.Codec.snappy.id) :
    readGroup limits bound index =
      (Date.Leaf.MixedCodec.V2.readGroup limits.toTwoCodecLimits bound index).mapError .twoCodec :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_twoCodec_agrees outsideSnappy

/-- The original selected footer lookup error is preserved. -/
theorem readGroup_selectionError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : selectedCodec bound index = .error cause) :
    readGroup limits bound index = .error (.twoCodec (.selection cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_selectionError failed

/-- Unsupported codecs retain the original numeric ID. -/
theorem readGroup_unsupportedCodec {limits : Limits} {bound : Bound} {index : Nat} {actual : Int}
    (selected : selectedCodec bound index = .ok actual)
    (snappy : actual ≠ Payload.Codec.snappy.id) (gzip : actual ≠ Payload.Codec.gzip.id)
    (zstd : actual ≠ Payload.Codec.zstd.id) :
    readGroup limits bound index = .error (.twoCodec (.unsupportedCodec actual)) :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_unsupportedCodec selected snappy gzip zstd

/-- Codec 2 returns the strict GZIP result and its original typed cause. -/
theorem readGroup_gzip_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits bound index =
      ((Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError
        Date.Leaf.MixedCodec.V2.GroupError.gzip).mapError .twoCodec :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_gzip_agrees selected

/-- Codec 6 returns the strict Zstandard result and its original typed cause. -/
theorem readGroup_zstd_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits bound index =
      ((Date.Leaf.Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError
        Date.Leaf.MixedCodec.V2.GroupError.zstd).mapError .twoCodec :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_zstd_agrees selected

/-- Codec 1 returns the strict Snappy result and its original typed cause. -/
theorem readGroup_snappy_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.snappy.id) :
    readGroup limits bound index =
      (Date.Leaf.Snappy.Dispatch.V2.readGroup limits.snappy bound index).mapError .snappy :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_snappy_agrees selected

/-- Every successful group retains its chosen codec's original selected frames and CRC evidence. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readGroup_wire read

/-- The first indexed source failure retains all complete earlier groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.readAll_firstError opened split earlier failed

/-- The first indexed source failure takes precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.toIpc_firstError opened split earlier failed

/-- Date32 IPC preserves the descriptor and exact footer-order signed nullable groups through EOS. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      List.Forall₂ (GroupWire limits bound) (List.range bound.snapshot.groupCount) groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy

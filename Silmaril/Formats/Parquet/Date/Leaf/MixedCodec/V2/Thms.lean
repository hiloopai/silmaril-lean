module

public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2

open Silmaril.Relational

/-- The codec ID is that of the original selected footer column. -/
theorem selectedCodec_exact {bound : Bound} {index : Nat} {selected : Date.Leaf.Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    selectedCodec bound index = .ok selected.column.metadata.codec :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.selectedCodec_exact admitted

/-- A failed original footer lookup preserves its typed cause. -/
theorem readGroup_selectionError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : selectedCodec bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readGroup_selectionError failed

/-- Any other codec returns its original numeric identifier. -/
theorem readGroup_unsupportedCodec {limits : Limits} {bound : Bound} {index : Nat} {actual : Int}
    (selected : selectedCodec bound index = .ok actual)
    (gzip : actual ≠ Payload.Codec.gzip.id) (zstd : actual ≠ Payload.Codec.zstd.id) :
    readGroup limits bound index = .error (.unsupportedCodec actual) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readGroup_unsupportedCodec selected gzip zstd

/-- Codec 2 preserves the complete strict GZIP dispatcher result. -/
theorem readGroup_gzip_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError .gzip :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readGroup_gzip_agrees selected

/-- Codec 6 preserves the complete strict Zstandard dispatcher result. -/
theorem readGroup_zstd_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id) :
    readGroup limits bound index =
      (Date.Leaf.Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError .zstd :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readGroup_zstd_agrees selected

/-- Every successful group retains the exact physical witness of the chosen codec. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readGroup_wire read

/-- The first indexed source error retains exactly the completed earlier groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.readAll_firstError opened split earlier failed

/-- The first indexed source error takes precedence over writer limits. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.toIpc_firstError opened split earlier failed

/-- Every exact codec witness supplies its original footer-order Date32 batch through EOS. -/
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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.MixedCodec.V2.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2

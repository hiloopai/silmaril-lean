module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain

open Silmaril.Relational

/-- Routing uses the dictionary offset of the exact selected footer column. -/
theorem route_selected {bound : Bound} {index : Nat} {selected : Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    route bound index = .ok (if selected.column.metadata.dictionaryPageOffset.isSome then
      .dictionaryBacked else .plain) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.route_selected admitted

/-- A missing group or column keeps the original selection error. -/
theorem readGroup_routeError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : route bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_routeError failed

/-- The PLAIN-only route preserves the dedicated reader’s slots and typed error. -/
theorem readGroup_plain_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .plain) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.V2.readGroup (plainLimits limits) bound index).mapError .plain :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_plain_agrees routed

/-- A dictionary offset selects the existing dictionary-backed dispatcher. -/
theorem readGroup_dictionaryBacked_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .dictionaryBacked) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.Dispatch.V2.readGroup limits bound index).mapError .dictionaryBacked :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_dictionaryBacked_agrees routed

/-- After framing, dictionary-only reads agree with the dedicated reader. -/
theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked)
    (original : Date.Leaf.Gzip.Dispatch.V2.FramedGroup limits bound index frames)
    (chosen : Date.Leaf.Gzip.Dispatch.V2.profile frames = .dictionary) :
    readGroup limits bound index =
      ((Date.Leaf.Dictionary.Gzip.V2.readGroup limits bound index).mapError
        Date.Leaf.Gzip.Dispatch.V2.dictionaryError).mapError .dictionaryBacked :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_dictionary_agrees routed original chosen

/-- After framing, dictionary-to-PLAIN reads agree with the dedicated fallback reader. -/
theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked)
    (original : Date.Leaf.Gzip.Dispatch.V2.FramedGroup limits bound index frames)
    (chosen : Date.Leaf.Gzip.Dispatch.V2.profile frames = .fallback) :
    readGroup limits bound index =
      (Date.Leaf.Fallback.Gzip.V2.readGroup limits bound index).mapError .dictionaryBacked :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_fallback_agrees routed original chosen

/-- Every completed group has the selected reader’s original chunk and physical page witnesses. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    GroupWire limits bound index slots :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readGroup_wire read

/-- The trace retains the exact earlier complete groups before the first indexed source error. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.readAll_firstError opened split earlier failed

/-- The first source error takes precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.toIpc_firstError opened split earlier failed

/-- Native Date32 readback preserves the descriptor and every footer-order batch through EOS. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain

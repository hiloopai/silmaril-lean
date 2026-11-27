module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

open Silmaril.Relational

/-- The original selected footer column fixes the top-level route. -/
theorem route_selected {bound : Bound} {index : Nat} {selected : Date.Leaf.Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    route bound index = .ok (if selected.column.metadata.dictionaryPageOffset.isSome then
      .dictionaryBacked else .plain) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.route_selected admitted

/-- A missing group or column keeps its original cause. -/
theorem readGroup_routeError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : route bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_routeError failed

/-- The PLAIN route preserves the strict reader result and error. -/
theorem readGroup_plain_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .plain) :
    readGroup limits bound index =
      (Date.Leaf.Zstd.V2.readGroup (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) bound index).mapError
        .plain :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_plain_agrees routed

/-- The chosen planner retains original page order and admits exactly its phase. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DictionaryChunk.DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Zstd.V2.planData bound page.frame = .ok page) ∧
      Phase (profile frames) pages :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.planPages_wire planned

/-- Dictionary-backed admission retains the original frame chain, dictionary and selected phase. -/
theorem checkDictionaryGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkDictionaryGroup limits bound index = .ok checked) :
    Date.Leaf.Fallback.Zstd.V2.GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      Phase (profile (checked.data.map (·.frame))) checked.data :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_wire accepted

/-- The dictionary-only planner preserves all results on the original framed group. -/
theorem checkDictionaryGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    checkDictionaryGroup limits bound index =
      (Date.Leaf.Dictionary.Zstd.V2.checkGroup limits bound index).mapError
        Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_dictionary_agrees original chosen

/-- The fallback planner preserves all results on the original framed group. -/
theorem checkDictionaryGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    checkDictionaryGroup limits bound index = Date.Leaf.Fallback.Zstd.V2.checkGroup limits bound index :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.checkDictionaryGroup_fallback_agrees original chosen

/-- The dictionary-only route preserves the dedicated reader result and error. -/
theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (routed : route bound index = .ok .dictionaryBacked)
    (original : FramedGroup limits bound index frames) (chosen : profile frames = .dictionary) :
    readGroup limits bound index =
      ((Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index).mapError
        Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary).mapError .dictionaryBacked :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_dictionary_agrees routed original chosen

/-- The fallback route preserves the dedicated reader result and error. -/
theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (routed : route bound index = .ok .dictionaryBacked)
    (original : FramedGroup limits bound index frames) (chosen : profile frames = .fallback) :
    readGroup limits bound index =
      (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index).mapError .dictionaryBacked :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_fallback_agrees routed original chosen

/-- Successful selected reads agree exactly with the three standalone profiles. -/
theorem readGroup_success_iff {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots} :
    readGroup limits bound index = .ok slots ↔
      Date.Leaf.Zstd.V2.readGroup (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) bound index = .ok slots ∨
      Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index = .ok slots ∨
      Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_success_iff

/-- Every successful group retains its selected frame chain and original physical page evidence. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readGroup_wire read

/-- The first indexed source error retains exactly the earlier complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.readAll_firstError opened split earlier failed

/-- The original indexed source error precedes writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.toIpc_firstError opened split earlier failed

/-- Successful IPC preserves the selected descriptor and every footer-order batch through EOS. -/
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
  Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.toIpc_readback written

/-- Once the dictionary-backed route is selected, its setup error is returned directly. -/
theorem readGroup_dictionarySetupError {limits : Limits} {bound : Bound} {index : Nat}
    {cause : Fallback.Zstd.V2.GroupError} (routed : route bound index = .ok .dictionaryBacked)
    (failed : checkDictionaryGroup limits bound index = .error cause) :
    readGroup limits bound index = .error (.dictionaryBacked cause) := by
  simp [readGroup, routed, readDictionaryGroup, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

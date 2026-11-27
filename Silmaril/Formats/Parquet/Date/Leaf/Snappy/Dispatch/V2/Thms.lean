module

public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

open Silmaril.Relational

/-- The original selected footer column fixes the top-level route. -/
theorem route_selected {bound : Bound} {index : Nat} {selected : Date.Leaf.Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    route bound index = .ok (if selected.column.metadata.dictionaryPageOffset.isSome then
      .dictionaryBacked else .plain) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.route_selected admitted

/-- A missing group or column retains the original lookup error. -/
theorem readGroup_routeError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : route bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_routeError failed

/-- The PLAIN route preserves the complete strict result. -/
theorem readGroup_plain_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .plain) :
    readGroup limits bound index =
      (Date.Leaf.Snappy.V2.readGroup (plainLimits limits) bound index).mapError .plain :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_plain_agrees routed

/-- The chosen planner retains the original data frames and exact phase. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DictionaryChunk.DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Dictionary.Snappy.V2.planData (profile frames) bound page.frame = .ok page) ∧
      Date.Leaf.Dictionary.Snappy.V2.Phase (profile frames) pages :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.planPages_wire planned

/-- The dispatcher preserves the strict checker result. Without a frame chain, both checks agree. -/
theorem checkDictionaryGroup_agrees {limits : Limits} {bound : Bound} {index : Nat} {choice : DictionaryProfile}
    (chosen : ∀ frames, FramedGroup limits bound index frames → profile frames = choice) :
    checkDictionaryGroup limits bound index = Date.Leaf.Dictionary.Snappy.V2.checkGroup choice limits bound index :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.checkDictionaryGroup_agrees chosen

/-- A selected dictionary-backed profile preserves every strict result, including setup failures. -/
theorem readGroup_dictionaryBacked_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {choice : DictionaryProfile} (routed : route bound index = .ok .dictionaryBacked)
    (chosen : ∀ frames, FramedGroup limits bound index frames → profile frames = choice) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Snappy.V2.readGroup choice limits bound index).mapError .dictionaryBacked :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_dictionaryBacked_agrees routed chosen

/-- On the original dictionary-backed chain, the chosen strict result is returned directly. -/
theorem readGroup_framed_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked) (original : FramedGroup limits bound index frames) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Snappy.V2.readGroup (profile frames) limits bound index).mapError .dictionaryBacked :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_framed_agrees routed original

/-- The original frame chain determines which strict wire witness applies. -/
theorem checkDictionaryGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkDictionaryGroup limits bound index = .ok checked) :
    FramedGroup limits bound index (checked.data.map (·.frame)) ∧
      Date.Leaf.Dictionary.Snappy.V2.GroupWire (profile (checked.data.map (·.frame))) limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.checkDictionaryGroup_wire accepted

/-- The successful route retains its original checked frames, CRC and signed slots. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_wire read

/-- Successful dispatch agrees exactly with success in one of the three strict readers. -/
theorem readGroup_success_iff {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots} :
    readGroup limits bound index = .ok slots ↔
      Date.Leaf.Snappy.V2.readGroup (plainLimits limits) bound index = .ok slots ∨
      Date.Leaf.Dictionary.Snappy.V2.readGroup .dictionaryOnly limits bound index = .ok slots ∨
      Date.Leaf.Dictionary.Snappy.V2.readGroup .fallback limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readGroup_success_iff

/-- The first indexed failure retains exactly the earlier complete groups. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.readAll_firstError opened split earlier failed

/-- The first indexed source failure precedes writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the descriptor and every original footer-order batch through EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

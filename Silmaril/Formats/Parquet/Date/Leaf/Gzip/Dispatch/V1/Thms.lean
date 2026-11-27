module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- Successful planning preserves original frames and checks the chosen encoding phase. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Gzip.planData bound page.frame = .ok page) ∧
      Phase (profile frames) pages :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.planPages_wire planned

/-- The original selected chunk supplies the frame chain, offsets, dictionary and row total. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      Phase (profile (checked.data.map (·.frame))) checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.checkGroup_wire accepted

/-- After framing, the dictionary branch agrees on both checked results and diagnostics. -/
theorem checkGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    checkGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.checkGroup limits bound index).mapError dictionaryError :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.checkGroup_dictionary_agrees original chosen

/-- After framing, the fallback branch agrees on both checked results and diagnostics. -/
theorem checkGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    checkGroup limits bound index = Date.Leaf.Fallback.Gzip.checkGroup limits bound index :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.checkGroup_fallback_agrees original chosen

/-- The dictionary branch preserves the dedicated reader’s rows and original errors. -/
theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.readGroup limits bound index).mapError dictionaryError :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.readGroup_dictionary_agrees original chosen

/-- The fallback branch preserves the dedicated reader’s rows and original errors. -/
theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    readGroup limits bound index = Date.Leaf.Fallback.Gzip.readGroup limits bound index :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.readGroup_fallback_agrees original chosen

/-- The chosen profile supplies exact page and CRC witnesses for every ordered group slot. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ Phase (profile (checked.data.map (·.frame))) checked.data ∧
      PagesWire limits bound.snapshot.bytes (profile (checked.data.map (·.frame))) checked pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.readGroup_wire read

/-- The first body failure after admission keeps its original indexed diagnostic. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      Date.Leaf.Fallback.Gzip.decodePage limits bound.snapshot.bytes checked.entries.toArray item i) =
        .ok prefixSlots)
    (failed : Date.Leaf.Fallback.Gzip.decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal =
      .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.readGroup_firstPageError admitted split earlier failed

/-- The trace retains the exact earlier complete groups before the first original source error. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.readAll_firstError opened split earlier failed

/-- An original source error takes precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.toIpc_firstError opened split earlier failed

/-- Native Date32 readback retains the descriptor and one batch per original footer group through EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1

module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- Admission witnesses a nonempty modern dictionary prefix and nonempty PLAIN suffix. -/
theorem checkSequence_wire {data : List DataPage} (checked : checkSequence data = .ok ()) :
    Ordered data :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.checkSequence_wire checked

/-- Both encoding phases use the original bounded frames and declared chunk offsets. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Dictionary.CheckedGroup} (read : checkGroup limits bound index = .ok checked) :
    Dictionary.GroupWire limits bound index checked ∧ Ordered checked.chunk.data :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.checkGroup_wire read

/-- The admitted page encoding selects the physical decoder for its exact payload. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {dictionary : DictionaryChunk.Dictionary}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits bound dictionary page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes dictionary page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.decodePage_wire read

/-- The selected group concatenates the two phases in wire order at its declared row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Dictionary.GroupWire limits bound index checked ∧ Ordered checked.chunk.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.dictionary) checked.chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.readGroup_wire read

/-- The original PLAIN suffix payload supplies its validity mask and exact signed words. -/
theorem plainWire_exact {limits : Limits} {source : Bytes} {page : DataPage} {slots : Slots}
    (decoded : ScalarPage.decode .int32 page.params limits.scalar
      (DictionaryChunk.body source page.frame) = .ok slots) :
    let body := DictionaryChunk.body source page.frame
    ∃ layout prepared words, ScalarPage.validate page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.plainWire_exact decoded

/-- After group planning, the first failing body read returns its original error. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Dictionary.CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.chunk.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.dictionary item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.dictionary page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.readGroup_firstPageError admitted split earlier failed

/-- The event trace retains exactly the earlier complete groups and the first
failed original footer index and cause. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.readAll_firstError opened split earlier failed

/-- The first source error precedes output limits and produces no IPC bytes. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.toIpc_firstError opened split earlier failed

/-- Output preserves the descriptor and exactly one ordered batch per footer group,
with exact signed nullable days and terminal EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Fallback.toIpc_readback written

theorem planPrefixWith_firstError {ε δ : Type} {plan : Page.Frame → Except ε DataPage}
    {atFrame : Nat → Page.Frame → ε → δ} {before after : List (Page.Frame × Nat)}
    {frame : Page.Frame} {ordinal : Nat} {pages : List DataPage}
    {cause : ε}
    (earlier : before.mapM
      (fun entry => plan entry.1) = .ok pages)
    (failed : plan frame = .error cause) :
    planPrefixWith plan atFrame (before ++ (frame, ordinal) :: after) =
      (pages, some (atFrame ordinal frame cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.planPrefixWith_firstError earlier failed

theorem planPagesWith_earlierPhaseError {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option δ} {ordinal offset : Nat} {tag : Int}
    (scanned : planPrefixWith plan atFrame (frames.zipIdx 1) = (pages, failure)) :
    (checkSequence pages = .error (.prefixEncoding ordinal offset tag) →
      planPagesWith plan atFrame headerError phaseError frames = .error (phaseError (.prefixEncoding ordinal offset tag))) ∧
    (checkSequence pages = .error (.suffixEncoding ordinal offset tag) →
      planPagesWith plan atFrame headerError phaseError frames = .error (phaseError (.suffixEncoding ordinal offset tag))) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.planPagesWith_earlierPhaseError scanned

theorem planPagesWith_headerError {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε} {frames : List Page.Frame} {pages : List DataPage}
    {cause : δ}
    (scanned : planPrefixWith plan atFrame (frames.zipIdx 1) = (pages, some cause))
    (phase : checkSequence pages = .ok () ∨
      checkSequence pages = .error .missingReferences ∨
      checkSequence pages = .error .missingPlain) :
    planPagesWith plan atFrame headerError phaseError frames = .error (headerError cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.planPagesWith_headerError scanned phase

theorem planPagesWith_wire {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε}
    (keeps : ∀ {frame page}, plan frame = .ok page → page.frame = frame) {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPagesWith plan atFrame headerError phaseError frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, plan page.frame = .ok page) ∧
      Ordered pages :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.planPagesWith_wire keeps planned

end Silmaril.Formats.Parquet.Date.Leaf.Fallback

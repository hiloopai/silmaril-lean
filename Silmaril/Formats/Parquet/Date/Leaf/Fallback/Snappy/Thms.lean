module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- An unsupported header terminates planning at its original indexed coordinate. -/
theorem planPrefix_firstError {bound : Bound} {before after : List (Page.Frame × Nat)}
    {frame : Page.Frame} {ordinal : Nat} {pages : List DataPage}
    {cause : Date.Leaf.Dictionary.Snappy.PageError}
    (earlier : before.mapM
      (fun entry => Date.Leaf.Dictionary.Snappy.planDataWith admits bound entry.1) = .ok pages)
    (failed : Date.Leaf.Dictionary.Snappy.planDataWith admits bound frame = .error cause) :
    planPrefix bound (before ++ (frame, ordinal) :: after) =
      (pages, some (Date.Leaf.Dictionary.Snappy.atFrame ordinal frame cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.planPrefix_firstError earlier failed

/-- An earlier phase failure retains priority over a subsequent header error. -/
theorem planPages_earlierPhaseError {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option Date.Leaf.Dictionary.Snappy.GroupError} {ordinal offset : Nat} {tag : Int}
    (scanned : planPrefix bound (frames.zipIdx 1) = (pages, failure)) :
    (Date.Leaf.Fallback.checkSequence pages = .error (.prefixEncoding ordinal offset tag) →
      planPages bound frames = .error (.sequence (.prefixEncoding ordinal offset tag))) ∧
    (Date.Leaf.Fallback.checkSequence pages = .error (.suffixEncoding ordinal offset tag) →
      planPages bound frames = .error (.sequence (.suffixEncoding ordinal offset tag))) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.planPages_earlierPhaseError scanned

/-- Missing end-of-sequence evidence cannot replace the next original header error. -/
theorem planPages_headerError {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {cause : Date.Leaf.Dictionary.Snappy.GroupError}
    (scanned : planPrefix bound (frames.zipIdx 1) = (pages, some cause))
    (phase : Date.Leaf.Fallback.checkSequence pages = .ok () ∨
      Date.Leaf.Fallback.checkSequence pages = .error .missingReferences ∨
      Date.Leaf.Fallback.checkSequence pages = .error .missingPlain) :
    planPages bound frames = .error (.snappy cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.planPages_headerError scanned phase

/-- A successful plan keeps the original ordered headers and encoding phases. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Dictionary.Snappy.planDataWith admits bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.planPages_wire planned

/-- The two phases share the original CRC-checked dictionary and bounded frame chain. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Date.Leaf.Dictionary.Snappy.GroupWire limits bound index checked admits ∧
      Date.Leaf.Fallback.Ordered checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.checkGroup_wire accepted

/-- The original dictionary and both data phases share one expansion budget.
Their data slot counts add up to the declared group count. -/
theorem transition_totals {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    ∃ references plain, checked.data = references ++ plain ∧
      references ≠ [] ∧ plain ≠ [] ∧
      (∀ page ∈ references, page.params.encoding = 8) ∧
      (∀ page ∈ plain, page.params.encoding = 0) ∧
      (references.map (·.params.numValues)).sum + (plain.map (·.params.numValues)).sum =
        checked.selection.group.numRows.toNat ∧
      checked.dictionary.value.uncompressedSize +
        ((references.map (·.frame.value.uncompressedSize)).sum +
          (plain.map (·.frame.value.uncompressedSize)).sum) ≤ limits.maxExpandedChunkBytes :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.transition_totals accepted

/-- Both branches verify the original stored frame before the physical decoder. -/
theorem decodePage_wire {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots} (admitted : admits page.params.encoding = true)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.decodePage_wire admitted decoded

/-- The exact V1 or V2 PLAIN payload yields its checked mask and signed PLAIN words. -/
theorem plainWire_exact {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {slots : Slots} (wire : PageWire limits source entries page slots)
    (plain : page.params.encoding = 0) :
    let body := Page.Checksum.payloadBytes source page.frame
    ∃ status layout prepared words,
      Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
      ScalarPage.validate page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.plainWire_exact wire plain

/-- Group slots concatenate both original phases at the exact declared row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Date.Leaf.Dictionary.Snappy.GroupWire limits bound index checked admits ∧
      Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.readGroup_wire read

/-- After planning, an original body failure keeps its indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup} {page : DataPage}
    {before after : List (DataPage × Nat)} {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.readGroup_firstPageError admitted split earlier failed

/-- The event trace retains the exact complete group prefix and original error. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.readAll_firstError opened split earlier failed

/-- The first source error precedes writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.toIpc_firstError opened split earlier failed

/-- Successful IPC preserves the descriptor and all signed nullable slots in
one batch per original footer group through exact EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy

module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary

open Silmaril.Relational

/-- The leading PLAIN dictionary and its original bounded frames are attached
to the same selected row group. -/
theorem checkGroup_exact {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (read : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.checkGroup_exact read

/-- A successful modern dictionary page selects its original typed payload. -/
theorem decodePage_wire {limits : Limits} {bound : Bound}
    {dictionary : DictionaryChunk.Dictionary} {page : DictionaryChunk.DataPage}
    {ordinal : Nat} {slots : Slots} (decoded : decodePage limits bound dictionary page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes dictionary page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.decodePage_wire decoded

/-- The same original selected chunk supplies the bounded frame chain, signed PLAIN
dictionary entries, and ordered dictionary-coded nullable slots. -/
theorem readGroup_exact {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ selected chunk dictionary header pages,
      selectChunk bound index = .ok selected ∧ frame limits bound selected = .ok chunk ∧
      chunk.span = selected.span ∧
      DictionaryChunk.Admitted limits bound.snapshot.bytes bound.snapshot.footer.start
        selected.group.numRows.toNat bound.field.layout selected.column.metadata chunk ∧
      Page.Chain selected.span selected.span.start selected.span.stop chunk.frames ∧
      (∀ page ∈ chunk.frames, Page.FrameWithin selected.span page.header.start page ∧
        (DictionaryChunk.body bound.snapshot.bytes page).length = page.value.compressedSize) ∧
      chunk.dictionary = some dictionary ∧ dictionary.frame.value.kind = .dictionary header ∧
      header.encoding = 0 ∧ dictionary.Exact limits bound.snapshot.bytes ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes dictionary) chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.readGroup_exact read

/-- The original body supplies the exact validity mask and fully consumed Hybrid
indices, and every index resolves in the chunk-local signed dictionary. -/
theorem pageWire_exact {limits : Limits} {source : Bytes} {dictionary : DictionaryChunk.Dictionary}
    {page : DictionaryChunk.DataPage} {slots : Slots}
    (decoded : PageWire limits source dictionary page slots) :
    let body := DictionaryChunk.body source page.frame
    ∃ layout prepared width runs indices,
      ScalarPage.validateFor 8 page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => dictionary.entries[index]?) = (slots.filterMap id).map some :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.pageWire_exact decoded

/-- The event trace retains exactly the earlier complete batches and the first
failed original footer index with its typed cause. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.readAll_firstError opened split earlier failed

/-- The original group error takes precedence over output limits. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.toIpc_firstError opened split earlier failed

/-- Success preserves the exact selected name, nullability, original group cuts,
and ordered signed nullable days in native Date32 IPC. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      Arrow.DateStream.read output.ipc wire =
        .ok (Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.toIpc_readback written

/-- Schema binding failures are reported before group or writer checks. -/
theorem toIpc_openError {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {cause : Leaf.Error}
    (failed : openLeaf input bytes ordinal = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.openFailure cause)) := by
  simp [toIpc, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary

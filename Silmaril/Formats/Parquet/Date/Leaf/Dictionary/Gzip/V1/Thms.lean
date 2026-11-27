module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- The exact original V1 header and selected schema fix the dictionary data parameters. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ page.params.encoding = 8 ∧
      ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 8 ∧
        page.params =
          ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
            ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
            header.encoding, .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.planData_wire planned

/-- The first PLAIN header is rejected even if subsequent pages resume dictionary encoding. -/
theorem planData_refusesPlain {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : Fallback.Gzip.planData bound frame = .ok page) (plain : page.params.encoding = 0) :
    planData bound frame = .error (.encoding 0) := by
  simp [planData, planned, plain, Bind.bind, Except.bind]
  rfl

/-- The plan preserves the original frame order. -/
theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.planPages_wire planned

/-- Planning returns the first inadmissible original page and its header offset. -/
theorem planPages_firstError {bound : Bound} {frames : List Page.Frame}
    {before after : List (Page.Frame × Nat)} {frame : Page.Frame} {ordinal : Nat}
    {pages : List DataPage} {cause : HeaderError}
    (split : frames.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (GroupError.header i item.header.start)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    planPages bound frames = .error (.header ordinal frame.header.start cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.planPages_firstError split earlier failed

/-- Each admitted group retains its original frame chain with a nonempty dictionary-only phase. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      ∀ page ∈ checked.data, page.params.encoding = 8 :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.checkGroup_wire accepted

/-- The original dictionary is one checksummed whole-body GZIP member
with exact signed PLAIN entries. -/
theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    let frame := checked.dictionary
    let source := bound.snapshot.bytes
    let bounds := Date.Leaf.Dictionary.Snappy.dictionaryBounds limits.toDictionaryLimits frame
    ∃ header expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Date.Leaf.Fallback.Gzip.StoredMember source frame bounds.compressedLimit bounds.outputLimit expanded ∧
      Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok checked.entries ∧
      checked.entries.length = header.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.checkGroup_dictionary accepted

/-- Exact whole-body V1 expansion yields the original level and reference slices,
with ordered signed nullable slots. -/
theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.decodePage_wire planned decoded

/-- The admitted original pages account for every ordered slot at the declared group count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ (∀ page ∈ checked.data, page.params.encoding = 8) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.readGroup_wire read

/-- After planning, the first original body failure retains its indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.readGroup_firstPageError admitted split earlier failed

/-- The trace keeps earlier complete groups and the original group index and cause. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.readAll_firstError opened split earlier failed

/-- The first source error takes precedence over IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.toIpc_firstError opened split earlier failed

/-- Native Date32 readback preserves the descriptor and one ordered batch per
original footer group through exact EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.toIpc_readback written

/-- An original stored CRC failure takes precedence over the dictionary decoder. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source entries page ordinal =
      .error (.chunk (.page ordinal page.frame.header.start (.checksum cause))) := by
  simp [decodePage, Date.Leaf.Dictionary.Snappy.decodePage, Date.Leaf.Dictionary.Snappy.verifyData,
    Date.Leaf.Dictionary.Snappy.atFrame, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1

module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- The original header supplies the V2 version, admitted encoding and exact scalar parameters. -/
theorem planData_wire {profile : Profile} {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData profile bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ profile.admits header.encoding = true ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues,
          Payload.Codec.snappy.id, header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.planData_wire planned

/-- A V1 data header fails the version gate for either declared profile. -/
theorem planData_rejectV1 {profile : Profile} {bound : Bound} {frame : Page.Frame} {header : Page.DataV1}
    (kind : frame.value.kind = .dataV1 header) :
    planData profile bound frame = .error .expectedV2 :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.planData_rejectV1 kind

/-- The declared profile preserves the original data frames and its exact sequence. -/
theorem planPages_wire {profile : Profile} {bound : Bound} {frames : List Page.Frame}
    {pages : List DataPage} (planned : planPages profile bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData profile bound page.frame = .ok page) ∧
      Phase profile pages :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.planPages_wire planned

/-- The dictionary-only plan returns its first indexed data header failure. -/
theorem planPages_dictionaryFirstError {bound : Bound} {frames : List Page.Frame}
    {before after : List (Page.Frame × Nat)} {frame : Page.Frame} {ordinal : Nat}
    {pages : List DataPage} {cause : HeaderError}
    (split : frames.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => (planData .dictionaryOnly bound item).mapError (atHeader i item)) =
      .ok pages)
    (failed : planData .dictionaryOnly bound frame = .error cause) :
    planPages .dictionaryOnly bound frames = .error (atHeader ordinal frame cause) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.planPages_dictionaryFirstError split earlier failed

/-- An earlier fallback reentry retains its original coordinate before a later header failure. -/
theorem planPages_fallbackReentry {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option GroupError} {ordinal offset : Nat} {tag : Int}
    (scanned : Date.Leaf.Fallback.planPrefixWith (planData .fallback bound) atHeader (frames.zipIdx 1) =
      (pages, failure))
    (reentry : Date.Leaf.Fallback.checkSequence pages = .error (.suffixEncoding ordinal offset tag)) :
    planPages .fallback bound frames = .error (.sequence (.suffixEncoding ordinal offset tag)) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.planPages_fallbackReentry scanned reentry

/-- Admission retains the original selected frame chain, offsets, bounds and phase. -/
theorem checkGroup_wire {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (admitted : checkGroup profile limits bound index = .ok checked) :
    GroupWire profile limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.checkGroup_wire admitted

/-- The leading dictionary consumes its original checksummed Snappy block and signed PLAIN entries. -/
theorem checkGroup_dictionary {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (admitted : checkGroup profile limits bound index = .ok checked) :
    DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.checkGroup_dictionary admitted

/-- The V2 route preserves the existing body decoder's complete result. -/
theorem decodePage_agrees {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} :
    decodePage limits source entries page ordinal =
      (Date.Leaf.Fallback.Snappy.decodePage limits source entries page ordinal).mapError .decode :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.decodePage_agrees

/-- The original V2 levels and suffix supply the mask and signed slots in either phase. -/
theorem decodePage_wire {profile : Profile} {limits : Limits} {bound : Bound} {source : Bytes}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData profile bound page.frame = .ok page)
    (read : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.decodePage_wire planned read

/-- Slots concatenate the original pages in order at the declared group row count. -/
theorem readGroup_wire {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup profile limits bound index = .ok slots) : SlotsWire profile limits bound index slots :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.readGroup_wire read

/-- The first failed body keeps its original typed cause. -/
theorem readGroup_firstPageError {profile : Profile} {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup profile limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup profile limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.readGroup_firstPageError admitted split earlier failed

/-- The first source failure retains every complete earlier group and the original footer index. -/
theorem readAll_firstError {input : Snapshot.Limits} {profile : Profile} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup profile limits bound) = .ok groups)
    (failed : readGroup profile limits bound index = .error cause) :
    readAll profile input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.readAll_firstError opened split earlier failed

/-- An indexed source failure precedes writer admission. -/
theorem toIpc_firstError {input : Snapshot.Limits} {profile : Profile} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup profile limits bound) = .ok groups)
    (failed : readGroup profile limits bound index = .error cause) :
    toIpc profile input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the exact descriptor and every ordered group through EOS. -/
theorem toIpc_readback {input : Snapshot.Limits} {profile : Profile} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc profile input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup profile limits bound) = .ok groups ∧
      List.Forall₂ (SlotsWire profile limits bound) (List.range bound.snapshot.groupCount) groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll profile input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.toIpc_readback written

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2

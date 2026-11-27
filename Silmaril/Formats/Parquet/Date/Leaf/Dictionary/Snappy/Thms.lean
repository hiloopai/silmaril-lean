module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy

open Silmaril.Relational
open DictionaryChunk (DataPage)

/-- The checked CRC status concerns exactly the bounded stored payload. -/
theorem stored_verified {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status} (verified : Page.Checksum.verify cap source frame = .ok status) :
    let stored := Page.Checksum.payloadBytes source frame
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.stored_verified verified

/-- The leading dictionary CRC is checked over stored bytes, with bounded Snappy
expansion into exact signed PLAIN entries. -/
theorem readEntries_wire {limits : Limits} {source : Bytes} {frame : Page.Frame}
    {entries : List Int32} (read : readEntries limits source frame = .ok entries) :
    ∃ header status expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Page.Checksum.verify (dictionaryBounds limits frame).compressedLimit source frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Page.Checksum.payloadBytes source frame).toList
        expanded ∧
      expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ (dictionaryBounds limits frame).outputLimit ∧
      Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.readEntries_wire read

/-- The selected data policy preserves the original header and exact codec parameters. -/
theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ admits page.params.encoding = true ∧
      ∃ base, FlatScan.int32PageParameters bound.field frame.value = some base ∧
        page.params = { base with codec := Payload.Codec.snappy.id } :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.planDataWith_wire planned

/-- The admitted tag and compression parameters come from the original data header. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ page.params.encoding = 8 ∧
      ∃ base, FlatScan.int32PageParameters bound.field frame.value = some base ∧
        page.params = { base with codec := Payload.Codec.snappy.id } :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.planData_wire planned

/-- A dictionary decoder may retain its own error while sharing the original checked chunk. -/
theorem checkGroupWithDictionary_wire {ε δ : Type} {codec : Payload.Codec} {wrap : GroupError → ε}
    {dictionaryError : Page.Frame → δ → ε}
    {readDictionary : Bytes → Page.Frame → Except δ (List Int32)}
    {plan : List Page.Frame → Except ε (List DataPage)} {admitted : DataPage → Prop}
    {valid : List DataPage → Prop} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup}
    (keeps : ∀ {frames data}, plan frames = .ok data →
      data.map (·.frame) = frames ∧ (∀ page ∈ data, admitted page) ∧ valid data)
    (accepted : checkGroupWithDictionary codec wrap dictionaryError readDictionary plan limits bound index = .ok checked) :
    GroupWireWith limits bound index checked codec readDictionary admitted ∧ valid checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_wire keeps accepted

/-- A codec-specific plan shares the selected chunk and original frames. -/
theorem checkGroupWithCodec_wire {ε : Type} {codec : Payload.Codec} {wrap : GroupError → ε}
    {readDictionary : Bytes → Page.Frame → Except PageError (List Int32)}
    {plan : List Page.Frame → Except ε (List DataPage)} {admitted : DataPage → Prop}
    {valid : List DataPage → Prop} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup}
    (keeps : ∀ {frames data}, plan frames = .ok data →
      data.map (·.frame) = frames ∧ (∀ page ∈ data, admitted page) ∧ valid data)
    (accepted : checkGroupWithCodec codec wrap readDictionary plan limits bound index = .ok checked) :
    GroupWireWith limits bound index checked codec readDictionary admitted ∧ valid checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire keeps accepted

/-- On the same original frames, equivalent plans and typed error wrappers agree. -/
theorem checkGroupWithDictionary_agrees {ε δ γ : Type} {limits : Limits} {bound : Bound} {index : Nat}
    {codec : Payload.Codec} {selection : Date.Leaf.Chunk} {dictionary : Page.Frame} {frames : List Page.Frame}
    {readDictionary : Bytes → Page.Frame → Except γ (List Int32)}
    {dictError : Page.Frame → γ → ε} {otherDictError : Page.Frame → γ → δ}
    {wrap : GroupError → ε} {otherWrap : GroupError → δ} {lift : ε → δ}
    {plan : List Page.Frame → Except ε (List DataPage)}
    {otherPlan : List Page.Frame → Except δ (List DataPage)}
    (selected : selectChunk bound index = .ok selection)
    (framed : Page.readChunk limits.page bound.snapshot.bytes selection.span = .ok (dictionary :: frames))
    (wrap_eq : ∀ cause, lift (wrap cause) = otherWrap cause)
    (dict_eq : ∀ frame cause, lift (dictError frame cause) = otherDictError frame cause)
    (plan_eq : otherPlan frames = (plan frames).mapError lift) :
    checkGroupWithDictionary codec otherWrap otherDictError readDictionary otherPlan limits bound index =
      (checkGroupWithDictionary codec wrap dictError readDictionary plan limits bound index).mapError lift :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_agrees
    selected framed wrap_eq dict_eq plan_eq

/-- The same original framed chunk preserves the result of the chosen plan
and its typed errors under the supplied wrapper. -/
theorem checkGroupWithCodec_agrees {ε δ : Type} {limits : Limits} {bound : Bound} {index : Nat}
    {codec : Payload.Codec} {selection : Date.Leaf.Chunk} {dictionary : Page.Frame} {frames : List Page.Frame}
    {readDictionary : Bytes → Page.Frame → Except PageError (List Int32)}
    {wrap : GroupError → ε} {otherWrap : GroupError → δ} {lift : ε → δ}
    {plan : List Page.Frame → Except ε (List DataPage)}
    {otherPlan : List Page.Frame → Except δ (List DataPage)}
    (selected : Date.Leaf.selectChunk bound index = .ok selection)
    (framed : Page.readChunk limits.page bound.snapshot.bytes selection.span = .ok (dictionary :: frames))
    (wrap_eq : ∀ cause, lift (wrap cause) = otherWrap cause)
    (plan_eq : otherPlan frames = (plan frames).mapError lift) :
    checkGroupWithCodec codec otherWrap readDictionary otherPlan limits bound index =
      (checkGroupWithCodec codec wrap readDictionary plan limits bound index).mapError lift :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_agrees selected framed wrap_eq plan_eq

/-- A profile plan that retains frames uses the same original chunk, bounds and dictionary. -/
theorem checkGroupWith_wire {ε : Type} {wrap : GroupError → ε}
    {plan : List Page.Frame → Except ε (List DataPage)} {admits : Int → Bool}
    {valid : List DataPage → Prop} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup}
    (keeps : ∀ {frames data}, plan frames = .ok data →
      data.map (·.frame) = frames ∧ (∀ page ∈ data, planDataWith admits bound page.frame = .ok page) ∧ valid data)
    (accepted : checkGroupWith wrap plan limits bound index = .ok checked) :
    GroupWire limits bound index checked admits ∧ valid checked.data :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroupWith_wire keeps accepted

/-- A checked group uses exactly the original selected frame chain and offsets. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.checkGroup_wire accepted

/-- Each data CRC check verifies the original stored body. -/
theorem verifyData_wire {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {status : Page.Checksum.Status}
    (verified : verifyData limits source page ordinal = .ok status) :
    Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.verifyData_wire verified

/-- A successful page has a checked stored body and exact dictionary decode. -/
theorem decodePage_wire {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.decodePage_wire read

/-- Bounded V1 or V2 preparation yields the exact validity mask, Hybrid indices
and in-range dictionary lookups over the original payload. -/
theorem pageWire_exact {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {slots : Slots} (read : PageWire limits source entries page slots) :
    let body := Page.Checksum.payloadBytes source page.frame
    ∃ status layout prepared width runs indices,
      Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
      slots.length = page.params.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.pageWire_exact read

/-- The selected group concatenates exact signed nullable slots at the footer count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.readGroup_wire read

/-- After planning, the first failed data page returns its original cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.readGroup_firstPageError admitted split earlier failed

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
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.readAll_firstError opened split earlier failed

/-- The first source error precedes output limits and produces no completed IPC. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the descriptor, signed nullable slots and one
ordered batch per original footer group through exact EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.toIpc_readback written

/-- A failed stored data CRC prevents reference decoding. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source entries page ordinal = .error (atFrame ordinal page.frame (.checksum cause)) := by
  simp [decodePage, verifyData, failed, Except.mapError, Bind.bind, Except.bind]

/-- An open failure precedes group decoding and writer admission. -/
theorem toIpc_openError {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {source : Bytes} {cause : Leaf.Error}
    (failed : openLeaf input source ordinal = .error cause) :
    toIpc input limits output ordinal source = .error (.source (.openFailure cause)) := by
  simp [toIpc, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy

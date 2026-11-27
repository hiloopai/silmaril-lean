module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- The original dictionary frame contains the exact bounded PLAIN signed entries. -/
theorem readEntries_wire {limits : Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {entries : List Int64} (read : readEntries limits bound frame = .ok entries) :
    ∃ header, frame.value.kind = .dictionary header ∧
      frame.value.crc = none ∧ header.encoding = 0 ∧
      frame.value.compressedSize = frame.value.uncompressedSize ∧
      header.numValues ≤ limits.maxEntries ∧ frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
      Plain.decodeInt64 header.numValues (Leaf.Internal.body bound frame) = .ok entries ∧
      entries.length = header.numValues :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.readEntries_wire read

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ page.frame.value.crc = none ∧
      page.frame.value.compressedSize = page.frame.value.uncompressedSize ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value = .ok page.params ∧
      admits page.params.encoding = true :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.planDataWith_wire read

/-- Each original data header supplies its RLE_DICTIONARY parameters. -/
theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ page.frame.value.crc = none ∧
      page.frame.value.compressedSize = page.frame.value.uncompressedSize ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value = .ok page.params ∧
      page.params.encoding = 8 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.planData_wire read

/-- One scan preserves the selected chunk's original frames and footer offsets. -/
theorem frameGroupUsing_wire {encoding : Leaf.ChunkEncoding} {limits : Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : FramedChunk}
    (accepted : frameGroupUsing encoding limits leafLimits bound index = .ok framed) :
    selectChunkWith encoding leafLimits bound index = .ok framed.chunk ∧
      framed.chunk.span.stop - framed.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes framed.chunk.span = .ok framed.frames ∧
      Parquet.Page.Chain framed.chunk.span framed.chunk.span.start framed.chunk.span.stop framed.frames ∧
      framed.chunk.column.metadata.dictionaryPageOffset = some (framed.dictionary.header.start : Int) ∧
      framed.chunk.column.metadata.dataPageOffset = (framed.firstData.header.start : Int) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.frameGroupUsing_wire accepted

/-- The codec-specific planners keep the same checked chunk, original
frame offsets and declared row count. -/
theorem checkGroupUsing_wire {encoding : Leaf.ChunkEncoding} {limits : Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {plan : Parquet.Page.Frame → Except Leaf.DictionaryPageError DataPage}
    {validate : List DataPage → Except Leaf.Error Unit}
    {read : Parquet.Page.Frame → Except Leaf.DictionaryPageError (List Int64)} {checked : CheckedChunk}
    (keepsFrame : ∀ {frame page}, plan frame = .ok page → page.frame = frame)
    (accepted : checkGroupUsing encoding limits leafLimits bound index plan validate read = .ok checked) :
    selectChunkWith encoding leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      read checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, plan page.frame = .ok page) ∧
      validate checked.data = .ok () ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.checkGroupUsing_wire keepsFrame accepted

theorem checkGroupWith_wire {admits : Int → Bool}
    {validate : List DataPage → Except Leaf.Error Unit} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroupWith admits validate limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planDataWith admits bound page.frame = .ok page) ∧
      validate checked.data = .ok () ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.checkGroupWith_wire accepted

/-- The selected chunk has one leading dictionary at the original offset,
with all continuation frames in wire order and their exact declared slot total. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.checkGroup_wire accepted

/-- The group concatenates original page slots and interprets each present
dictionary word on the selected descriptor scale. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (fun page raw => DictionaryIndex.decode checked.entries.toArray page.params
        leafLimits.page limits.indices (Leaf.Internal.body bound page.frame) = .ok raw) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.readGroup_wire read

/-- The original page supplies the exact level mask and width-prefixed Hybrid
indices, which resolve the signed dictionary entries in order. -/
theorem data_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {raw : List (Option Int64)}
    (decoded : DictionaryIndex.decode entries.toArray page.params leafLimits.page limits.indices
      (Leaf.Internal.body bound page.frame) = .ok raw) :
    ∃ layout prepared width runs indices,
      ScalarPage.validateFor page.params.encoding page.params leafLimits.page
        (Leaf.Internal.body bound page.frame) = .ok layout ∧
      ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      raw.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (raw.filterMap id).map some :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.data_decodes decoded

/-- The event trace agrees with the same checked reader in footer order. -/
theorem readBound_reference (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Events.referenceGroupsWith (readGroup limits leafLimits bound)
      (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Events.rows bound), reference.2⟩⟩ :=
  Events.readBoundWith_reference bound (readGroup limits leafLimits bound)

/-- Successful IPC retains the selected descriptor and every signed nullable
slot in its original footer group. -/
theorem convert_readback {profile : AnnotationProfile} {limits : Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert profile limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroups_readback written

/-- The earliest failed footer group forwards its original cause before any
IPC writer admission. -/
theorem convert_first_error {profile : AnnotationProfile} {limits : Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert profile limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary

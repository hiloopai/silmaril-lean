module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2
open Silmaril.Numeric.Timestamp (Ticks)

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.uncompressed.id frame.value =
        .ok page.params ∧
      ∃ header, frame.value.kind = .dataV2 header ∧ admits header.encoding = true ∧
        page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
          header.numValues, Payload.Codec.uncompressed.id, header.encoding, .v2 header.numNulls header.numRows
            header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    by_cases tag : admits header.encoding = true
    · by_cases levels : Timestamp.Page.leafLevels? bound.binding.leaf = some bound.levels
      · simp [planDataWith, kind, tag, Timestamp.Page.parameters, levels,
          Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at planned
        have params := congrArg DataPage.params planned.symm
        exact ⟨congrArg DataPage.frame planned.symm,
          by simp [Timestamp.Page.parameters, kind, levels, params], header, rfl, tag, params⟩
      · simp [planDataWith, kind, tag, Timestamp.Page.parameters, levels,
          Bind.bind, Except.bind, Except.mapError] at planned
    · simp [planDataWith, kind, tag, Bind.bind, Except.bind] at planned
  | dataV1 _ | dictionary _ | skipped _ => simp [planDataWith, kind, Bind.bind, Except.bind] at planned

theorem planDataWith_restrict {admits accepts : Int → Bool} {bound : Bound}
    {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page)
    (admitted : accepts page.params.encoding = true) :
    planDataWith accepts bound frame = .ok page := by
  obtain ⟨_, _, info, kind, tag, params⟩ := planDataWith_wire planned
  rw [params] at admitted
  simpa [planDataWith, kind, admitted, tag, Bind.bind, Except.bind] using planned

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.uncompressed.id, 8, .v2 header.numNulls header.numRows
          header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  obtain ⟨same, _, header, kind, tag, params⟩ := planDataWith_wire planned
  have encoding : header.encoding = 8 := by simpa using tag
  exact ⟨same, header, kind, encoding, by simpa [encoding] using params⟩

theorem readEntries_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntries limits leafLimits bound frame = .ok entries) :
    let stored := Leaf.Internal.body bound frame
    let bounds := Leaf.Dictionary.Snappy.dictionaryBounds limits leafLimits frame
    ∃ header, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
      (frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
        Compression.crc32Spec stored.toList = crc) ∧
      stored.length = frame.value.uncompressedSize ∧ stored.length ≤ bounds.outputLimit ∧
      Plain.decodeInt64 header.numValues stored = .ok entries ∧
      entries.length = header.numValues := by
  obtain ⟨header, status, _, kind, tag, entryCap, verified, literal, size, cap, decoded, count⟩ :=
    Leaf.Dictionary.Snappy.readEntriesWithCodec_wire read
  cases literal
  obtain ⟨slice, storedSize, storedCap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  refine ⟨header, kind, tag, entryCap, slice, storedSize, storedCap, ?_, by simpa using size,
    by simpa using cap, by simpa using decoded, count⟩
  cases status with
  | absent => exact .inl crc
  | valid value => exact .inr ⟨value, crc⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.uncompressed.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, entries, plans, _, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (plan := planData bound)
      (fun plan => (planData_wire plan).1) admitted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, frames, chain, dictionary, first, entries, plans, rows⟩

theorem data_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits leafLimits bound entries.toArray page slots) :
    let frame := page.frame
    let stored := Leaf.Internal.body bound frame
    ∃ header layout definitions suffix, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ leafLimits.page.compressedBytes ∧
      (frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
        Compression.crc32Spec stored.toList = crc) ∧
      frame.value.uncompressedSize ≤ leafLimits.page.uncompressedBytes ∧
      header.numNulls ≤ header.numValues ∧ header.numRows = header.numValues ∧
      header.repetitionBytes = 0 ∧
      header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
      definitions.length = header.definitionBytes ∧ definitions.length ≤ leafLimits.page.levels.bytes ∧
      stored.toList = definitions.toList ++ suffix ∧
      suffix.length = frame.value.compressedSize - header.definitionBytes ∧
      suffix.length = frame.value.uncompressedSize - header.definitionBytes ∧
      suffix = prepared.scalars.toList ∧ suffix = width :: runs ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some := by
  obtain ⟨status, layout, prepared, width, runs, indices, verified, expandedBound, wire,
    encoded, hybrid, mask, signed⟩ := Leaf.Dictionary.Snappy.data_decodes read
  obtain ⟨_, header, kind, tag, params⟩ := planData_wire planned
  rw [params] at wire expandedBound
  obtain ⟨nulls, rows, noRep, storedFits, expandedFits, levelCap, definitions, suffix,
    definitionSize, split, readMask, present, payload⟩ := wire
  obtain ⟨slice, storedSize, storedCap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  obtain ⟨storedSuffix, expandedSuffix, literal⟩ := Leaf.Uncompressed.V2.exactPayload_literal payload
  refine ⟨header, layout, definitions, suffix, prepared, width, runs, indices,
    kind, tag, slice, storedSize, storedCap, ?_, expandedBound, nulls, rows, noRep, storedFits, expandedFits,
    definitionSize, definitionSize ▸ levelCap, split, storedSuffix,
    ?_, literal, literal.trans encoded, readMask, present, hybrid, mask, signed⟩
  · cases status with
    | absent => exact .inl crc
    | valid value => exact .inr ⟨value, crc⟩
  · simpa only [← literal] using expandedSuffix

theorem readGroup_first_header_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .ok framed)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    readGroup limits leafLimits bound index = .error (.dictionaryPage ordinal frame.header.start cause) := by
  have rejected : (framed.data.zipIdx 1).mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) =
      .error (.dictionaryPage ordinal frame.header.start cause) := by
    rw [split, List.mapM_append, earlier]
    simp [failed, Leaf.Dictionary.atFrame, Except.mapError, Bind.bind, Except.bind]
  simp [readGroup, checkGroup, Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.checkFramedUsing, framedOk, rejected, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Dictionary.Snappy.DataWire limits leafLimits
        bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ := Leaf.Dictionary.Snappy.readGroupUsing_wire read
  obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  refine ⟨checked, pages, admitted, decoded, mapped, ?_, count.trans rows⟩
  rw [mapped, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot <;> rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2

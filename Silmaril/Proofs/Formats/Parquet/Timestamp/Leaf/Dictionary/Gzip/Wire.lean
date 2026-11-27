module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Compression.Gzip.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip
open Silmaril.Numeric.Timestamp (Ticks)

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ admits info.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, info.encoding, .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩ := by
  cases kind : frame.value.kind with
  | dataV1 info =>
    by_cases tag : admits info.encoding = true
    · cases chosen : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.gzip.id frame.value with
      | error cause =>
        simp [planDataWith, kind, tag, chosen, Bind.bind, Except.bind, Except.mapError] at planned
      | ok params =>
        simp [planDataWith, kind, tag, chosen, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at planned
        subst page
        unfold Timestamp.Page.parameters at chosen
        split at chosen
        · simp only [kind, Except.ok.injEq] at chosen
          exact ⟨rfl, info, rfl, tag, chosen.symm⟩
        · contradiction
    · simp [planDataWith, kind, tag, Bind.bind, Except.bind] at planned
  | dataV2 _ | dictionary _ | skipped _ => simp [planDataWith, kind, Bind.bind, Except.bind] at planned

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ info.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, 8, .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩ := by
  obtain ⟨same, info, kind, tag, params⟩ := planDataWith_wire (admits := (· == 8)) planned
  have encoding : info.encoding = 8 := by simpa using tag
  exact ⟨same, info, kind, encoding, by simpa [encoding] using params⟩

private theorem storedMember_of {bound : Bound} {frame : Parquet.Page.Frame}
    {storedCap expandedCap : Nat} {expanded : List UInt8} {status : Parquet.Page.Checksum.Status}
    (verified : Parquet.Page.Checksum.verify storedCap bound.snapshot.bytes frame = .ok status)
    (decoded : Payload.Decodes frame.value.uncompressedSize .gzip (Leaf.Internal.body bound frame).toList expanded)
    (size : expanded.length = frame.value.uncompressedSize) (cap : expanded.length ≤ expandedCap) :
    StoredMember bound frame storedCap expandedCap expanded := by
  have member : Compression.Gzip.decoder (Leaf.Internal.body bound frame).toList = some (expanded, []) := by
    cases decoded with | gzip exactMember => exact exactMember
  obtain ⟨prefixBytes, trailer⟩ := Compression.Gzip.decoder_trailer member
  obtain ⟨slice, storedSize, storedCap, checksum⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  refine ⟨slice, storedSize, storedSize ▸ storedCap, ?_, member, ⟨prefixBytes, by simpa using trailer⟩, size, cap⟩
  cases status with
  | absent => exact .inl checksum
  | valid crc => exact .inr ⟨crc, checksum⟩

theorem readEntries_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {entries : List Int64} (read : readEntries limits leafLimits bound frame = .ok entries) :
    let bounds := Leaf.Dictionary.Snappy.dictionaryBounds limits.dictionary (limits.withFuel leafLimits) frame
    ∃ header expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.dictionary.maxEntries ∧
      StoredMember bound frame bounds.compressedLimit bounds.outputLimit expanded ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = header.numValues := by
  obtain ⟨header, status, expanded, kind, tag, count, checksum, member, size, cap, words, length⟩ :=
    Leaf.Dictionary.Snappy.readEntriesWithCodec_wire (codec := .gzip) (tag := .plain) read
  exact ⟨header, expanded, kind, tag, count, storedMember_of checksum member size cap, words, length⟩

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
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

theorem prepared_member {admits : Int → Bool} {leafLimits : Leaf.Limits} {bound : Bound}
    {page : DataPage} {encoding : Int} {status : Parquet.Page.Checksum.Status}
    {prepared : ScalarPage.Prepared}
    (planned : planDataWith admits bound page.frame = .ok page)
    (verified : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .ok status)
    (preparedOk : ScalarPage.prepareFor encoding page.params leafLimits.page
      (Leaf.Internal.body bound page.frame) = .ok prepared) :
    ∃ expanded layout sections,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars := by
  obtain ⟨_, info, _, _, params⟩ := planDataWith_wire planned
  obtain ⟨layout, admitted, wire⟩ := ScalarPage.prepareFor_sound preparedOk
  have cap := Leaf.Dictionary.Snappy.expanded_bound admitted
  rw [params] at wire cap
  obtain ⟨_, _, expanded, sections, payload, split, definition, scalar⟩ := wire
  obtain ⟨_, size, codec, id, member⟩ := payload
  change Payload.Codec.ofId Payload.Codec.gzip.id = some codec at id
  rw [Payload.Codec.ofId_id] at id
  cases Option.some.inj id
  refine ⟨expanded, layout, sections, storedMember_of verified member size ?_, split, ?_, scalar⟩
  · rw [size]
    exact cap
  · rw [params]
    exact definition

theorem data_decodesWith {admits : Int → Bool} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planDataWith admits bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars ∧ prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some := by
  obtain ⟨_, verified, decoded⟩ := read
  obtain ⟨_, prepared, indices, preparedOk, indexOk, mask, signed⟩ :=
    DictionaryIndex.decode_ok_iff.mp decoded
  obtain ⟨expanded, layout, sections, member, split, definition, scalar⟩ :=
    prepared_member planned verified preparedOk
  obtain ⟨_, width, runs, suffix, _, _, _, hybrid⟩ :=
    DictionaryIndex.readIndices_ok_iff.mp indexOk
  exact ⟨expanded, layout, sections, prepared, width, runs, indices, member,
    split, definition, scalar, suffix, hybrid, mask, signed⟩

theorem data_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      StoredMember bound page.frame leafLimits.page.compressedBytes leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars ∧ prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  data_decodesWith (admits := (· == 8)) planned read

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
        bound checked.entries.toArray) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ :=
    Leaf.Dictionary.Snappy.readGroupUsing_wire read
  obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  refine ⟨checked, pages, admitted, decoded, ?_, count.trans rows⟩
  rw [mapped, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot <;> rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip

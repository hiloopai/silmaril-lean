module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Compression.Gzip.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2
open Silmaril.Numeric.Timestamp (Ticks)

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.gzip.id, 8, .v2 header.numNulls header.numRows
          header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    by_cases tag : header.encoding = 8
    · cases chosen : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.gzip.id frame.value with
      | error cause =>
        simp [planData, kind, tag, chosen, Bind.bind, Except.bind, Except.mapError] at planned
      | ok params =>
        simp [planData, kind, tag, chosen, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at planned
        subst page
        unfold Timestamp.Page.parameters at chosen
        split at chosen
        · simp only [kind, Except.ok.injEq] at chosen
          exact ⟨rfl, header, rfl, tag, by simpa [tag] using chosen.symm⟩
        · contradiction
    · simp [planData, kind, tag, Bind.bind, Except.bind] at planned
  | dataV1 _ | dictionary _ | skipped _ => simp [planData, kind, Bind.bind, Except.bind] at planned

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .gzipDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, entries, plans, _, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (plan := planData bound)
      (fun plan => (planData_wire plan).1) admitted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, frames, chain, dictionary, first, entries, plans, rows⟩

private theorem suffix_storage {storedSize expandedSize : Nat} {compressed : Bool}
    {stored expanded : List UInt8}
    (payload : ScalarPage.ExactPayload storedSize expandedSize
      (ScalarPage.v2Codec Payload.Codec.gzip.id (some compressed)) stored expanded) :
    if compressed then Compression.Gzip.decoder stored = some (expanded, []) ∧
      ∃ prefixBytes, stored = prefixBytes ++ Compression.Gzip.trailer expanded
    else stored = expanded := by
  obtain ⟨_, _, codec, selected, decoded⟩ := payload
  cases compressed with
  | false =>
    change some Payload.Codec.uncompressed = some codec at selected
    cases Option.some.inj selected
    cases decoded
    rfl
  | true =>
    change some Payload.Codec.gzip = some codec at selected
    cases Option.some.inj selected
    cases decoded with
    | gzip member =>
      obtain ⟨prefixBytes, trailer⟩ := Compression.Gzip.decoder_trailer member
      exact ⟨member, prefixBytes, by simpa using trailer⟩

theorem data_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
      bound entries.toArray page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some := by
  obtain ⟨_, header, kind, _, params⟩ := planData_wire planned
  obtain ⟨status, verified, decoded⟩ := read
  obtain ⟨_, prepared, indices, preparedOk, indexOk, mask, signed⟩ :=
    DictionaryIndex.decode_ok_iff.mp decoded
  obtain ⟨layout, admitted, wire⟩ := ScalarPage.prepareFor_sound preparedOk
  have expandedBound := Leaf.Dictionary.Snappy.expanded_bound admitted
  rw [params] at wire expandedBound
  obtain ⟨_, rows, noRep, storedFits, expandedFits, definitionBound, definitions, encoded,
    definitionSize, split, readMask, present, payload⟩ := wire
  obtain ⟨slice, storedSize, storedBound, checksum⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  have checksumWire : page.frame.value.crc = none ∨ ∃ crc, page.frame.value.crc = some crc ∧
      Compression.crc32Spec (Leaf.Internal.body bound page.frame).toList = crc := by
    cases status with
    | absent => exact .inl checksum
    | valid crc => exact .inr ⟨crc, checksum⟩
  have body : BodyWire bound page.frame leafLimits.page header definitions encoded prepared.scalars.toList :=
    ⟨slice, storedSize, storedSize ▸ storedBound, checksumWire, expandedBound, noRep, definitionSize,
      definitionBound, ⟨storedFits, expandedFits⟩, split, payload.1, payload.2.1, suffix_storage payload⟩
  obtain ⟨_, width, runs, suffix, _, _, _, hybrid⟩ :=
    DictionaryIndex.readIndices_ok_iff.mp indexOk
  exact ⟨header, layout, definitions, encoded, prepared, width, runs, indices,
    kind, rows, body, readMask, present, suffix, hybrid, mask, signed⟩

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

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2

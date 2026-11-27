module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2
open Silmaril.Numeric.Timestamp (Ticks)

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ admits header.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.snappy.id, header.encoding, .v2 header.numNulls header.numRows
          header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    have shared : Leaf.Dictionary.Snappy.planDataWith admits bound frame = .ok page := by
      simpa [planDataWith, kind, Bind.bind, Except.bind] using planned
    obtain ⟨same, source, admitted⟩ := Leaf.Dictionary.Snappy.planDataWith_wire shared
    unfold Timestamp.Page.parameters at source
    split at source
    · simp only [kind, Except.ok.injEq] at source
      exact ⟨same, header, rfl, by simpa [← source] using admitted, source.symm⟩
    · contradiction
  | dataV1 _ | dictionary _ | skipped _ => simp [planDataWith, kind, Bind.bind, Except.bind] at planned

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.snappy.id, 8, .v2 header.numNulls header.numRows
          header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  obtain ⟨same, header, kind, tag, params⟩ := planDataWith_wire planned
  have encoding : header.encoding = 8 := by simpa using tag
  exact ⟨same, header, kind, encoding, by simpa [encoding] using params⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Snappy.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
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
      (ScalarPage.v2Codec Payload.Codec.snappy.id (some compressed)) stored expanded) :
    if compressed then Payload.Decodes expandedSize .snappy stored expanded else stored = expanded := by
  obtain ⟨_, _, codec, selected, decoded⟩ := payload
  cases compressed with
  | false =>
    change some Payload.Codec.uncompressed = some codec at selected
    cases Option.some.inj selected
    cases decoded
    rfl
  | true =>
    change some Payload.Codec.snappy = some codec at selected
    cases Option.some.inj selected
    exact decoded

theorem body_wire {admits : Int → Bool} {leafLimits : Leaf.Limits} {bound : Bound}
    {page : DataPage} {status : Parquet.Page.Checksum.Status} {layout : FlatPage.Layout}
    {prepared : ScalarPage.Prepared}
    (planned : planDataWith admits bound page.frame = .ok page)
    (verified : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status)
    (expandedBound : page.params.sizes.uncompressed ≤ leafLimits.page.uncompressedBytes)
    (wire : ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared) :
    ∃ header definitions storedValues,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls := by
  obtain ⟨_, header, kind, _, params⟩ := planDataWith_wire planned
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
  exact ⟨header, definitions, encoded, kind, rows, body, readMask, present⟩

theorem data_decodesWith {admits : Int → Bool} {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planDataWith admits bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits leafLimits bound entries.toArray page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some := by
  obtain ⟨status, layout, prepared, width, runs, indices, verified, expandedBound, wire,
    suffix, hybrid, mask, signed⟩ := Leaf.Dictionary.Snappy.data_decodes read
  obtain ⟨header, definitions, storedValues, kind, rows, body, readMask, present⟩ :=
    body_wire planned verified expandedBound wire
  exact ⟨header, layout, definitions, storedValues, prepared, width, runs, indices, kind, rows, body,
    readMask, present, suffix, hybrid, mask, signed⟩

theorem data_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : Leaf.Dictionary.Snappy.DataWire limits leafLimits bound entries.toArray page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some :=
  data_decodesWith (admits := (· == 8)) planned read

theorem readGroup_first_header_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index = .ok framed)
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

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2

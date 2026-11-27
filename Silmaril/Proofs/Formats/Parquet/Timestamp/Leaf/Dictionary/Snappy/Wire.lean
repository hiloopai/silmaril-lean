module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem stored_verified {cap : Nat} {bound : Bound} {frame : Parquet.Page.Frame}
    {status : Parquet.Page.Checksum.Status}
    (verified : Parquet.Page.Checksum.verify cap bound.snapshot.bytes frame = .ok status) :
    let stored := Leaf.Internal.body bound frame
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc := by
  cases status with
  | absent =>
    obtain ⟨withinCap, extent, absent⟩ := Parquet.Page.Checksum.verify_absent_iff.mp verified
    obtain ⟨slice, size⟩ := Parquet.Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ withinCap, absent⟩
  | valid crc =>
    obtain ⟨withinCap, extent, header, computed⟩ := Parquet.Page.Checksum.verify_valid_iff.mp verified
    obtain ⟨slice, size⟩ := Parquet.Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ withinCap, header, computed⟩

theorem readEntriesWithCodec_wire {codec : Payload.Codec} {tag : DictionaryTag} {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntriesWithCodec codec tag limits leafLimits bound frame = .ok entries) :
    ∃ header status expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = tag.id ∧
      header.numValues ≤ limits.maxEntries ∧
      Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
        bound.snapshot.bytes frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize codec (Leaf.Internal.body bound frame).toList expanded ∧
      expanded.length = frame.value.uncompressedSize ∧
      expanded.length ≤ (dictionaryBounds limits leafLimits frame).outputLimit ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues := by
  cases kind : frame.value.kind with
  | dictionary header =>
    simp only [readEntriesWithCodec, kind, Bind.bind, Except.bind] at read
    split_ifs at read with encoding count size
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨body, decoded, read⟩ := bind_ok read
    obtain ⟨selected, id, expansion, _, _, exactSize, cap⟩ := Payload.decode_sound (mapError_ok decoded)
    rw [Payload.Codec.ofId_id] at id
    cases Option.some.inj id
    have words := mapError_ok read
    obtain ⟨_, original, _, rows, _, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp
      (by simpa only [Plain.decodeInt64] using words)
    exact ⟨header, status, body, rfl, Decidable.not_not.mp encoding, Nat.le_of_not_gt count,
      mapError_ok verified, expansion, exactSize, cap, words, by simpa using rows⟩
  | dataV1 _ | dataV2 _ | skipped _ =>
    simp [readEntriesWithCodec, kind] at read

theorem readEntriesWith_wire {tag : DictionaryTag} {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntriesWith tag limits leafLimits bound frame = .ok entries) :
    ∃ header status expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = tag.id ∧
      header.numValues ≤ limits.maxEntries ∧
      Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
        bound.snapshot.bytes frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Leaf.Internal.body bound frame).toList expanded ∧
      expanded.length = frame.value.uncompressedSize ∧
      expanded.length ≤ (dictionaryBounds limits leafLimits frame).outputLimit ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues :=
  readEntriesWithCodec_wire (codec := .snappy) read

theorem readEntries_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : readEntries limits leafLimits bound frame = .ok entries) :
    ∃ header status expanded,
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Parquet.Page.Checksum.verify (dictionaryBounds limits leafLimits frame).compressedLimit
        bound.snapshot.bytes frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Leaf.Internal.body bound frame).toList expanded ∧
      expanded.length = frame.value.uncompressedSize ∧
      expanded.length ≤ (dictionaryBounds limits leafLimits frame).outputLimit ∧
      Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues :=
  readEntriesWith_wire (tag := .plain) read

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
        .ok page.params ∧ admits page.params.encoding = true := by
  cases kind : frame.value.kind with
  | dictionary _ => simp [planDataWith, kind, Bind.bind, Except.bind] at planned
  | dataV1 _ | dataV2 _ | skipped _ =>
    simp only [planDataWith, kind, Bind.bind, Except.bind] at planned
    cases params : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value with
    | error e => simp [params, Except.mapError] at planned
    | ok value =>
      simp only [params, Except.mapError] at planned
      split_ifs at planned with tag
      cases Except.ok.inj planned
      exact ⟨rfl, rfl, by simpa using tag⟩

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
        .ok page.params ∧ page.params.encoding = 8 := by
  obtain ⟨same, params, tag⟩ := planDataWith_wire (admits := (· == 8)) planned
  exact ⟨same, params, by simpa using tag⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = 1 ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, read, plans, _, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (encoding := .snappyDictionary)
      (plan := planData bound) (validate := fun _ => .ok ()) (read := readEntries limits leafLimits bound)
      (fun success => (planData_wire success).1) accepted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec] using codec,
    cap, frames, chain, dictionary, first, read, plans, rows⟩

theorem decodePage_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    DataWire limits leafLimits bound entries page slots := by
  unfold decodePage at read
  obtain ⟨status, verified, decoded⟩ := bind_ok read
  exact ⟨status, mapError_ok verified, mapError_ok decoded⟩

theorem expanded_bound {encoding : Int} {params : ScalarPage.Parameters}
    {limits : ScalarPage.Limits} {source : Bytes} {layout : FlatPage.Layout}
    (checked : ScalarPage.validateFor encoding params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  unfold ScalarPage.validateFor at checked
  dsimp only at checked
  split_ifs at checked with tag extent compressed expanded
  exact Nat.le_of_not_gt expanded

theorem data_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : List Int64} {page : DataPage} {slots : List (Option Int64)}
    (read : DataWire limits leafLimits bound entries.toArray page slots) :
    ∃ status layout prepared width runs indices,
      Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ leafLimits.page.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared ∧
      prepared.scalars.toList = width :: runs ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries.toArray[index]?) = (slots.filterMap id).map some := by
  obtain ⟨status, verified, decoded⟩ := read
  obtain ⟨layout, prepared, width, runs, indices, checked, wire, suffix, hybrid, mask, selected⟩ :=
    Leaf.Dictionary.data_decodes (limits := limits) (leafLimits := leafLimits) (bound := bound)
      (entries := entries) (page := page) decoded
  exact ⟨status, layout, prepared, width, runs, indices, verified, expanded_bound checked,
    wire, suffix, hybrid, mask, selected⟩

theorem readGroupUsing_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {admission : Except Leaf.Error CheckedChunk} {slots : Slots bound}
    (read : readGroupUsing limits leafLimits bound admission = .ok slots) :
    ∃ checked pages, admission = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = (checked.data.map (·.params.numValues)).sum := by
  unfold readGroupUsing at read
  obtain ⟨checked, admitted, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages := by
    rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ h => decodePage_wire h
  have sizes : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear decoded read
    generalize checked.data = data at raw ⊢
    induction raw with
    | nil => rfl
    | cons current _ rest =>
      obtain ⟨_, _, decoded⟩ := current
      exact congrArg₂ List.cons (DictionaryIndex.decode_counts decoded).1 rest
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, admitted, raw, mapped, ?_⟩
  rw [mapped, List.length_map, List.length_flatten, sizes]

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ := readGroupUsing_wire read
  obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  exact ⟨checked, pages, admitted, decoded, mapped, count.trans rows⟩

theorem readGroupUsing_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {ordinal : Nat} {admission : Except Leaf.Error CheckedChunk} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : admission = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroupUsing limits leafLimits bound admission = .error cause := by
  simp [readGroupUsing, admitted, split, earlier, failed, Bind.bind, Except.bind]

theorem readGroup_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  readGroupUsing_first_page_error admitted split earlier failed

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy

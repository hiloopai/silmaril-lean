module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (CheckedChunk DataPage)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2
open Silmaril.Numeric.Timestamp (Ticks)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ admits header.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    by_cases encoding : admits header.encoding = true
    · simp only [planDataWith, kind, encoding, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at read
      obtain ⟨params, parsed, read⟩ := bind_ok read
      cases Except.ok.inj read
      have parameters := mapError_ok parsed
      unfold Timestamp.Page.parameters at parameters
      split at parameters
      · simp only [kind, Except.ok.injEq] at parameters
        exact ⟨rfl, header, rfl, encoding, parameters.symm⟩
      · contradiction
    · simp [planDataWith, kind, encoding, Bind.bind, Except.bind] at read
  | dataV1 _ | dictionary _ | skipped _ => simp [planDataWith, kind, Bind.bind, Except.bind] at read

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, 8,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  obtain ⟨same, header, kind, tag, params⟩ := planDataWith_wire (admits := (· == 8)) read
  have encoding : header.encoding = 8 := by simpa using tag
  exact ⟨same, header, kind, encoding, by simpa [encoding] using params⟩

private theorem planPages_wire {admits : Int → Bool} {bound : Bound} {frames : List Parquet.Page.Frame} {data : List DataPage}
    (read : planPagesWith admits bound frames = .ok data) :
    data.map (·.frame) = frames ∧ ∀ page ∈ data, planDataWith admits bound page.frame = .ok page := by
  unfold planPagesWith at read
  have plans : List.Forall₂ (fun frame page => planDataWith admits bound frame = .ok page) frames data := by
    rw [← List.zipIdx_map_fst 1 frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp read).imp fun _ _ h => mapError_ok h
  clear read
  induction plans with
  | nil => simp
  | cons head _ ih =>
    obtain ⟨original, _⟩ := planDataWith_wire head
    refine ⟨by simp [original, ih.1], ?_⟩
    intro page member
    simp only [List.mem_cons] at member
    rcases member with rfl | rest
    · rwa [original]
    · exact ih.2 page rest

theorem checkGroupWith_wire {admits : Int → Bool} {validate : List DataPage → Except Leaf.Error Unit}
    {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroupWith admits validate limits leafLimits bound index = .ok checked) :
    selectChunkWith .zstdDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planDataWith admits bound page.frame = .ok page) ∧
      validate checked.data = .ok () ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  unfold checkGroupWith at accepted
  obtain ⟨framed, selected, accepted⟩ := bind_ok accepted
  obtain ⟨chunk, storedCap, original, chain, dictionaryOffset, dataOffset⟩ :=
    Leaf.Dictionary.frameGroupUsing_wire (mapError_ok selected)
  split at accepted
  · contradiction
  rename_i expandedCap
  obtain ⟨data, planned, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, valid, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i rows
  obtain ⟨entries, read, accepted⟩ := bind_ok accepted
  cases Except.ok.inj accepted
  obtain ⟨order, plans⟩ := planPages_wire planned
  have same : (Leaf.Dictionary.CheckedChunk.mk framed.chunk framed.dictionary entries data).frames = framed.frames := by
    simp [Leaf.Dictionary.CheckedChunk.frames, Leaf.Dictionary.FramedChunk.frames, order]
  have first : data.head?.map (fun page => (page.frame.header.start : Int)) =
      some framed.chunk.column.metadata.dataPageOffset := by
    have head := congrArg List.head? order
    rw [List.head?_map] at head
    have offset := congrArg (Option.map (fun frame : Parquet.Page.Frame => (frame.header.start : Int))) head
    simpa [Option.map_map, Function.comp_def, Leaf.Dictionary.FramedChunk.data, ← dataOffset] using offset
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound chunk
  exact ⟨chunk, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec, storedCap,
    by simpa only [same] using original, by simpa only [same] using chain,
    by simpa only [same] using Nat.le_of_not_gt expandedCap,
    dictionaryOffset, first, read, plans, mapError_ok valid, not_not.mp rows⟩

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .zstdDictionaryV2 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, codec, stored, frames, chain, expanded, dictionary, data, entries, plans, _, rows⟩ :=
    checkGroupWith_wire (admits := (· == 8)) (validate := fun _ => .ok ()) accepted
  exact ⟨selected, codec, stored, frames, chain, expanded, dictionary, data, entries, plans, rows⟩

theorem readEntries_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {entries : List Int64} (read : readEntries limits leafLimits bound frame = .ok entries) :
    DictionaryWire limits leafLimits bound frame entries := by
  cases kind : frame.value.kind with
  | dictionary header =>
    simp only [readEntries, kind] at read
    split at read
    · contradiction
    rename_i encoding
    split at read
    · contradiction
    rename_i entryCap
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨expanded, expandedOk, words⟩ := bind_ok read
    have checked := mapError_ok verified
    have decoded := mapError_ok words
    obtain ⟨slice, stored, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified checked
    obtain ⟨_, _, expandedSize, outputCap, raw | compressed⟩ :=
      FlatColumn.Zstd.decodePayload_sound (mapError_ok expandedOk)
    · simp [Payload.Codec.id] at raw
    · obtain ⟨_, parsed, member, window⟩ := compressed
      obtain ⟨_, _, _, count, _, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp (by
        simpa only [Plain.decodeInt64] using decoded)
      exact ⟨status, header, expanded, parsed, kind, not_not.mp encoding, Nat.le_of_not_gt entryCap,
        slice, stored, cap, by cases status <;> exact crc, member, window, expandedSize, outputCap,
        decoded, by simpa using count⟩
  | dataV1 _ | dataV2 _ | skipped _ => simp [readEntries, kind] at read

theorem decodePage_wireWith {admits : Int → Bool} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planDataWith admits bound page.frame = .ok page) (reference : page.params.encoding = 8)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots := by
  obtain ⟨_, header, kind, _, fields⟩ := planDataWith_wire planned
  have tag : header.encoding = 8 := by simpa [fields] using reference
  unfold decodePage at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨prepared, preparedOk, read⟩ := bind_ok read
  obtain ⟨_, layout, _, _, _, expanded, wire⟩ := FlatColumn.Zstd.prepareFor_sound (mapError_ok preparedOk)
  obtain ⟨slice, stored, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified (mapError_ok verified)
  have references := mapError_ok read
  unfold decodeReferences at references
  obtain ⟨indices, indexOk, references⟩ := bind_ok references
  obtain ⟨values, selected, restored⟩ := bind_ok references
  obtain ⟨orderedMask, orderedValues⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok restored)
  obtain ⟨indexCap, width, runs, exactRuns, widthCap, _, _, hybrid⟩ :=
    DictionaryIndex.readIndices_ok_iff.mp indexOk
  rw [FlatColumn.Zstd.PreparedWire, fields] at wire
  obtain ⟨nulls, rows, repetition, defStored, defExpanded, defCap, definitions, encoded,
    definitionSize, split, mask, present, payload⟩ := wire
  have suffix : Leaf.Zstd.V2.SuffixWire (scalarLimits limits) leafLimits page.frame header encoded prepared.scalars.toList :=
    Leaf.Zstd.V2.suffixWire_of payload
  have count := congrArg List.length orderedMask
  rw [List.length_map, FlatPage.readMask_length mask] at count
  have presentCount := (FlatPage.reconstruct_exists_iff prepared.mask values).mp ⟨slots, mapError_ok restored⟩
  have exactNulls : (slots.filterMap id).length + header.numNulls = header.numValues := by
    rw [orderedValues, ← presentCount]
    change prepared.mask.count true = header.numValues - header.numNulls at present
    change header.numNulls ≤ header.numValues at nulls
    omega
  exact ⟨by simpa [fields] using count, status, header, layout, definitions, encoded, prepared, width, runs,
    indices, kind, tag, slice, stored, stored ▸ cap, by simpa [fields, Leaf.Zstd.V2.columnLimits] using expanded,
    by cases status <;> exact crc, rows, nulls, repetition, defStored, defExpanded, defCap, definitionSize,
    split, suffix, mask, indexCap, exactRuns, widthCap, hybrid,
    orderedValues ▸ DictionaryIndex.select_ok_iff.mp selected, orderedMask, exactNulls⟩

theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots := by
  obtain ⟨_, _, _, _, params⟩ := planData_wire planned
  exact decodePage_wireWith (admits := (· == 8)) planned (by rw [params]) read

theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) := by
  simp [decodePage, failed, Bind.bind, Except.bind, Except.mapError]

/-- After planning, the first data error uses the original page number and offset. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      DictionaryWire limits leafLimits bound checked.dictionary checked.entries ∧
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, accepted, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨_, _, _, _, _, _, _, _, dictionary, plans, rows⟩ := checkGroup_wire accepted
  have paired : List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages := by
    have frames : ∀ entry ∈ checked.data.zipIdx 1, planData bound entry.1.frame = .ok entry.1 := by
      intro entry mem
      apply plans
      rw [← List.zipIdx_map_fst 1 checked.data]
      exact List.mem_map.mpr ⟨entry, mem, rfl⟩
    have indexed := List.mapM_eq_ok_iff_forall₂.mp decoded
    have raw : List.Forall₂
        (fun (entry : DataPage × Nat) slots => PageWire limits leafLimits bound checked.entries.toArray entry.1 slots)
        (checked.data.zipIdx 1) pages := by
      clear read decoded
      generalize checked.data.zipIdx 1 = data at frames indexed
      induction indexed with
      | nil => exact .nil
      | cons first _ ih =>
        exact .cons (decodePage_wire (frames _ List.mem_cons_self) first)
          (ih fun item member => frames item (List.mem_cons_of_mem _ member))
    simpa using List.forall₂_map_left_iff.mpr raw
  have counts : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded plans rows accepted
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons first _ ih => exact congrArg₂ List.cons first.count ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, accepted, readEntries_wire dictionary, paired, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · rw [mapped, List.length_map, List.length_flatten, counts, rows]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2

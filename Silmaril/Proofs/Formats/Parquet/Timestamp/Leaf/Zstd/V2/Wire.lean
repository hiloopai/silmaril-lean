module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits leafLimits bound index = .ok group) :
    selectChunkWith .zstdPlainV2 leafLimits bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      group.chunk.span.stop - group.chunk.span.start ≤ limits.maxStoredChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset := by
  unfold checkGroup at checked
  obtain ⟨chunk, selection, checked⟩ := bind_ok checked
  have selected := mapError_ok selection
  by_cases cap : limits.maxStoredChunkBytes < chunk.span.stop - chunk.span.start
  · simp [cap, Bind.bind, Except.bind] at checked
  · simp only [cap, ↓reduceIte] at checked
    obtain ⟨frames, framed, checked⟩ := bind_ok checked
    have wire := mapError_ok framed
    by_cases expanded : limits.maxExpandedChunkBytes < (frames.map (·.value.uncompressedSize)).sum
    · simp [expanded, Bind.bind, Except.bind] at checked
    · simp only [expanded, ↓reduceIte] at checked
      by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat
      · simp [rows, pure, Except.pure] at checked
        subst group
        obtain ⟨_, _, _, _, _, codec, metadata, _, span, _⟩ := Leaf.selectChunkWith_sound selected
        have noDictionary := Leaf.ChunkEncoding.zstdPlainV2_noDictionary metadata
        have offset := Footer.checkDataSpan_some_iff.mp (by
          simpa [Parquet.Page.columnSpan, noDictionary] using span)
        exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
          Nat.le_of_not_gt cap, wire, (Parquet.Page.readChunk_chain wire).2.2, Nat.le_of_not_gt expanded,
          rows, noDictionary, offset.1⟩
      · simp [rows, Bind.bind, Except.bind] at checked

private theorem params_v2 {bound : Bound} {frame : Parquet.Page.Frame} {header : Parquet.Page.DataV2}
    {params : ScalarPage.Parameters} (v2 : frame.value.kind = .dataV2 header)
    (read : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.zstd.id frame.value =
      .ok params) :
    params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
      header.numValues, Payload.Codec.zstd.id, header.encoding,
      .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  unfold Timestamp.Page.parameters at read
  split at read
  · simp only [v2, Except.ok.injEq] at read
    exact read.symm
  · contradiction

theorem suffixWire_of {limits : Limits} {leafLimits : Leaf.Limits} {frame : Parquet.Page.Frame}
    {header : Parquet.Page.DataV2} {encoded decoded : List UInt8}
    (wire : FlatColumn.Zstd.PayloadWire limits.compression
      (leafLimits.page.payloadBounds ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ header.definitionBytes)
      (ScalarPage.v2Codec 6 (some header.isCompressed)) encoded decoded) :
    SuffixWire limits leafLimits frame header encoded decoded := by
  obtain ⟨storedSize, _, plainSize, _, profile⟩ := wire
  refine ⟨storedSize, plainSize, ?_⟩
  cases flag : header.isCompressed <;>
    simpa [ScalarPage.v2Codec, flag, Payload.Codec.id] using profile

private theorem pageWire_of {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {header : Parquet.Page.DataV2} {slots : List (Option Int64)}
    {params : ScalarPage.Parameters} {status : Parquet.Page.Checksum.Status}
    (v2 : frame.value.kind = .dataV2 header)
    (parsed : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.zstd.id frame.value =
      .ok params)
    (verified : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame = .ok status)
    (read : decodeBody (columnLimits limits leafLimits) params
      (Leaf.Internal.body bound frame) = .ok slots) :
    PageWire limits leafLimits bound frame slots := by
  have fields := params_v2 v2 parsed
  unfold decodeBody at read
  obtain ⟨prepared, preparedOk, read⟩ := bind_ok read
  obtain ⟨words, wordsOk, slotsOk⟩ := bind_ok read
  obtain ⟨_, layout, valid, _, _, expanded, wire⟩ := FlatColumn.Zstd.prepareFor_sound preparedOk
  have decoded := mapError_ok wordsOk
  have restored := mapError_ok slotsOk
  obtain ⟨slice, stored, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  have tag : header.encoding = 0 := by
    by_contra different
    simp [ScalarPage.validateFor, fields, different] at valid
  rw [FlatColumn.Zstd.PreparedWire, fields] at wire
  obtain ⟨nulls, rows, repetition, defStored, defExpanded, defCap, definitions, encoded,
    definitionSize, split, mask, present, payload⟩ := wire
  have suffix : SuffixWire limits leafLimits frame header encoded prepared.scalars.toList :=
    suffixWire_of payload
  obtain ⟨orderedMask, orderedWords⟩ := FlatPage.reconstruct_ok_iff.mp restored
  have count := congrArg List.length orderedMask
  rw [List.length_map, FlatPage.readMask_length mask] at count
  have presentCount := (FlatPage.reconstruct_exists_iff prepared.mask words).mp ⟨slots, restored⟩
  have exactNulls : (slots.filterMap id).length + header.numNulls = header.numValues := by
    rw [orderedWords, ← presentCount]
    change prepared.mask.count true = header.numValues - header.numNulls at present
    change header.numNulls ≤ header.numValues at nulls
    omega
  exact ⟨by simpa [Leaf.Internal.pageSlots, v2] using count, status, header, layout, definitions,
    encoded, prepared, words, v2, tag, slice, stored, stored ▸ cap, by simpa [fields, columnLimits] using expanded,
    by cases status <;> exact crc, rows, nulls, repetition, defStored, defExpanded, defCap,
    definitionSize, split, suffix, mask, decoded, orderedMask, orderedWords, exactNulls⟩

theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodePage limits leafLimits bound frame ordinal = .ok slots) :
    PageWire limits leafLimits bound frame slots := by
  unfold decodePage at read
  cases kind : frame.value.kind with
  | dataV2 header =>
    simp only [kind] at read
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨params, parsed, read⟩ := bind_ok read
    exact pageWire_of kind (mapError_ok parsed) (mapError_ok verified) (mapError_ok read)
  | dataV1 _ | dictionary _ | skipped _ => simp [kind] at read

theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {ordinal : Nat} {header : Parquet.Page.DataV2}
    {cause : Parquet.Page.Checksum.Error} (v2 : frame.value.kind = .dataV2 header)
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame = .error cause) :
    decodePage limits leafLimits bound frame ordinal = .error (.checksum ordinal frame.header.start cause) := by
  simp [decodePage, v2, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ group pages, checkGroup limits leafLimits bound index = .ok group ∧
      List.Forall₂ (PageWire limits leafLimits bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨group, checked, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (PageWire limits leafLimits bound) group.frames pages := by
    rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => decodePage_wire read
  have counts : pages.map List.length = group.frames.map Leaf.Internal.pageSlots := by
    clear read checked decoded
    generalize group.frames = frames at raw ⊢
    induction raw with
    | nil => rfl
    | cons head _ ih =>
      exact congrArg₂ List.cons head.count ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨group, pages, checked, raw, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · rw [mapped, List.length_map, List.length_flatten, counts, (checkGroup_wire checked).2.2.2.2.2.2.1]

theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (checked : checkGroup limits leafLimits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound frame ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, checked, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.V2

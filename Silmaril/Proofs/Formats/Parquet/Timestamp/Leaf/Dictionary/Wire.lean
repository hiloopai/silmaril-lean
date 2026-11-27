module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Page.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem readEntries_wire {limits : Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {entries : List Int64} (read : readEntries limits bound frame = .ok entries) :
    ∃ header, frame.value.kind = .dictionary header ∧
      frame.value.crc = none ∧ header.encoding = 0 ∧
      frame.value.compressedSize = frame.value.uncompressedSize ∧
      header.numValues ≤ limits.maxEntries ∧ frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
      Plain.decodeInt64 header.numValues (Leaf.Internal.body bound frame) = .ok entries ∧
      entries.length = header.numValues := by
  cases kind : frame.value.kind with
  | dictionary header =>
    simp only [readEntries, kind, Bind.bind, Except.bind] at read
    split_ifs at read with crc encoding extent count size
    have decoded := mapError_ok read
    have words := Plain.decodeFixedWidth_ok_iff.mp (by
      simpa only [Plain.decodeInt64] using decoded)
    obtain ⟨_, raw, _, rows, _, rfl⟩ := words
    exact ⟨header, rfl, Option.not_isSome_iff_eq_none.mp crc,
      Decidable.not_not.mp encoding, Decidable.not_not.mp extent, Nat.le_of_not_gt count,
      Nat.le_of_not_gt size, decoded, by simpa using rows⟩
  | dataV1 _ | dataV2 _ | skipped _ =>
    simp [readEntries, kind] at read

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ page.frame.value.crc = none ∧
      page.frame.value.compressedSize = page.frame.value.uncompressedSize ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value = .ok page.params ∧
      admits page.params.encoding = true := by
  cases kind : frame.value.kind with
  | dictionary _ => simp [planDataWith, kind, Bind.bind, Except.bind] at read
  | dataV1 _ | dataV2 _ | skipped _ =>
    simp only [planDataWith, kind, Bind.bind, Except.bind] at read
    split_ifs at read with crc extent
    cases params : Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value with
    | error e => simp [params, Except.mapError] at read
    | ok value =>
      simp only [params, Except.mapError] at read
      split_ifs at read with encoding
      cases Except.ok.inj read
      exact ⟨rfl, Option.not_isSome_iff_eq_none.mp crc,
        Decidable.not_not.mp extent, rfl, by simpa using encoding⟩

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ page.frame.value.crc = none ∧
      page.frame.value.compressedSize = page.frame.value.uncompressedSize ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value = .ok page.params ∧
      page.params.encoding = 8 := by
  obtain ⟨frame, crc, sizes, params, encoding⟩ := planDataWith_wire (admits := (· == 8)) read
  exact ⟨frame, crc, sizes, params, by simpa using encoding⟩

private theorem planPages_wire (plan : Parquet.Page.Frame → Except Leaf.DictionaryPageError DataPage)
    (keepsFrame : ∀ {frame page}, plan frame = .ok page → page.frame = frame) {frames : List Parquet.Page.Frame}
    {start : Nat} {pages : List DataPage}
    (planned : (frames.zipIdx start).mapM (fun (frame, ordinal) =>
      (plan frame).mapError (atFrame ordinal frame)) = .ok pages) :
    pages.map (·.frame) = frames ∧ ∀ page ∈ pages, plan page.frame = .ok page := by
  induction frames generalizing start pages with
  | nil =>
    cases Except.ok.inj planned
    simp
  | cons frame rest ih =>
    rw [List.zipIdx_cons, List.mapM_cons] at planned
    obtain ⟨page, first, remaining⟩ := bind_ok planned
    obtain ⟨following, kept, output⟩ := bind_ok remaining
    cases Except.ok.inj output
    have original := mapError_ok first
    cases keepsFrame original
    obtain ⟨order, each⟩ := ih kept
    constructor
    · simp [order]
    · intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact original
      · exact each item later

theorem frameGroupUsing_wire {encoding : Leaf.ChunkEncoding} {limits : Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : FramedChunk}
    (accepted : frameGroupUsing encoding limits leafLimits bound index = .ok framed) :
    selectChunkWith encoding leafLimits bound index = .ok framed.chunk ∧
      framed.chunk.span.stop - framed.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes framed.chunk.span = .ok framed.frames ∧
      Parquet.Page.Chain framed.chunk.span framed.chunk.span.start framed.chunk.span.stop framed.frames ∧
      framed.chunk.column.metadata.dictionaryPageOffset = some (framed.dictionary.header.start : Int) ∧
      framed.chunk.column.metadata.dataPageOffset = (framed.firstData.header.start : Int) := by
  unfold frameGroupUsing at accepted
  obtain ⟨chunk, selected, accepted⟩ := bind_ok accepted
  split at accepted
  · contradiction
  rename_i cap
  obtain ⟨frames, scanned, accepted⟩ := bind_ok accepted
  have wire := mapError_ok scanned
  cases frames with
  | nil => contradiction
  | cons dictionary rest =>
    dsimp only at accepted
    split at accepted
    · contradiction
    rename_i dictionaryOffset
    cases rest with
    | nil => contradiction
    | cons first following =>
      dsimp only at accepted
      split at accepted
      · contradiction
      rename_i dataOffset
      cases Except.ok.inj accepted
      exact ⟨selected, Nat.le_of_not_gt cap, wire, (Parquet.Page.readChunk_chain wire).2.2,
        Decidable.not_not.mp dictionaryOffset, Decidable.not_not.mp dataOffset⟩

private theorem checkFramedUsing_wire {framed : FramedChunk}
    {plan : Parquet.Page.Frame → Except Leaf.DictionaryPageError DataPage}
    {validate : List DataPage → Except Leaf.Error Unit}
    {read : Parquet.Page.Frame → Except Leaf.DictionaryPageError (List Int64)} {checked : CheckedChunk}
    (keepsFrame : ∀ {frame page}, plan frame = .ok page → page.frame = frame)
    (accepted : checkFramedUsing framed plan validate read = .ok checked) :
    checked.chunk = framed.chunk ∧ checked.dictionary = framed.dictionary ∧
      checked.data.map (·.frame) = framed.data ∧
      read checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, plan page.frame = .ok page) ∧
      validate checked.data = .ok () ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  unfold checkFramedUsing at accepted
  obtain ⟨data, planned, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, valid, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i count
  obtain ⟨entries, decoded, accepted⟩ := bind_ok accepted
  cases Except.ok.inj accepted
  obtain ⟨order, dataReads⟩ := planPages_wire plan keepsFrame planned
  exact ⟨rfl, rfl, order, mapError_ok decoded, dataReads, valid, Decidable.not_not.mp count⟩

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
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  unfold checkGroupUsing at accepted
  obtain ⟨framed, framedOk, accepted⟩ := bind_ok accepted
  obtain ⟨selected, cap, wire, chain, dictionaryOffset, dataOffset⟩ := frameGroupUsing_wire framedOk
  obtain ⟨chunk, dictionary, order, decoded, dataReads, valid, count⟩ := checkFramedUsing_wire keepsFrame accepted
  have frameOrder : checked.frames = framed.frames := by
    simp [CheckedChunk.frames, FramedChunk.frames, dictionary, order]
  have dataHead := congrArg List.head? order
  rw [List.head?_map] at dataHead
  have offset := congrArg (Option.map (fun frame : Parquet.Page.Frame => (frame.header.start : Int))) dataHead
  refine ⟨chunk ▸ selected, chunk ▸ cap, ?_, ?_, ?_, ?_, decoded, dataReads, valid, count⟩
  · simpa [chunk, frameOrder] using wire
  · simpa [chunk, frameOrder] using chain
  · simpa [chunk, dictionary] using dictionaryOffset
  · simpa [Option.map_map, Function.comp_def, FramedChunk.data, ← dataOffset, chunk] using offset

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
  checkGroupUsing_wire (fun success => (planDataWith_wire success).1) accepted

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
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, framed, chain, dictionary, data, entries, pages, _, rows⟩ :=
    checkGroupWith_wire (admits := (· == 8)) (validate := fun _ => .ok ()) accepted
  exact ⟨selected, cap, framed, chain, dictionary, data, entries, pages, rows⟩

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (fun page raw => DictionaryIndex.decode checked.entries.toArray page.params
        leafLimits.page limits.indices (Leaf.Internal.body bound page.frame) = .ok raw) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, admitted, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have each := List.mapM_eq_ok_iff_forall₂.mp decoded
  have raw : List.Forall₂ (fun page words => DictionaryIndex.decode checked.entries.toArray page.params
        leafLimits.page limits.indices (Leaf.Internal.body bound page.frame) = .ok words) checked.data pages := by
    rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
    exact each.imp fun _ _ h => mapError_ok h
  have sizes : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear decoded read each
    generalize checked.data = data at raw ⊢
    induction raw with
    | nil => rfl
    | cons current _ rest =>
      exact congrArg₂ List.cons (DictionaryIndex.decode_counts current).1 rest
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, admitted, raw, mapped, ?_⟩
  rw [mapped, List.length_map, List.length_flatten, sizes]
  exact (checkGroup_wire admitted).2.2.2.2.2.2.2.2

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
      indices.map (fun index => entries.toArray[index]?) = (raw.filterMap id).map some := by
  obtain ⟨_, prepared, references, read, indexes, mask, selected⟩ := DictionaryIndex.decode_ok_iff.mp decoded
  obtain ⟨layout, checked, wire⟩ := ScalarPage.prepareFor_sound read
  obtain ⟨_, width, runs, suffix, _, _, _, extent⟩ := DictionaryIndex.readIndices_ok_iff.mp indexes
  exact ⟨layout, prepared, width, runs, references, checked, wire, suffix, extent, mask, selected⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary

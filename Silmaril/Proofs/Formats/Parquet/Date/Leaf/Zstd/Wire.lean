module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import all Silmaril.Formats.Parquet.FlatColumn.Defs
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd

open Silmaril.Formats Parquet
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Zstd

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : Date.Leaf.Gzip.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked := by
  apply Date.Leaf.Gzip.checkGroupFor_wire _ accepted
  intro frame ordinal page planned
  have decoded := mapError_ok planned
  have same := (Date.Leaf.Gzip.planDataFor_wire decoded).1
  exact ⟨same, by simpa only [same] using decoded⟩

theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits bound metadata page ordinal = .ok slots) :
    PageWire limits bound metadata page slots := by
  unfold decodePage at read
  obtain ⟨status, verified, decoded⟩ := bind_ok read
  exact ⟨⟨status, mapError_ok verified⟩, FlatColumn.Zstd.decodePage_sound (mapError_ok decoded)⟩

private theorem exactV1Parameters {bound : Bound} {frame : Page.Frame} {page : Date.Leaf.Gzip.DataPage}
    (planned : planData bound frame = .ok page) :
    ∃ header, page.frame.value.kind = .dataV1 header ∧
      FlatColumn.pageParameters (columnLayout bound) 6 page.frame.value = some page.params ∧
      page.params.version = .v1 header.definitionLevelEncoding header.repetitionLevelEncoding ∧
      page.params.sizes = ⟨page.frame.value.compressedSize, page.frame.value.uncompressedSize⟩ := by
  obtain ⟨same, header, kind, _, params⟩ := Date.Leaf.Gzip.planDataFor_wire planned
  refine ⟨header, by rwa [same], ?_, by rw [params], by rw [params, same]⟩
  rw [params, same]
  unfold FlatColumn.pageParameters
  rw [kind]
  cases h : bound.nullable <;>
    simp [columnLayout, Date.Leaf.Bound.field, h, FlatColumn.Layout.levels, Payload.Codec.id]

theorem pageWire_exact {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {slots : Slots} (planned : planData bound page.frame = .ok page)
    (read : PageWire limits bound metadata page slots) :
    let source := bound.snapshot.bytes
    let stored := Page.Checksum.payloadBytes source page.frame
    let frameLimits := FlatColumn.Zstd.frameLimits limits.compression
      (limits.pages.scalar.payloadBounds page.params.sizes 0)
    slots.length = page.params.numValues ∧
    ∃ status expanded frameHeader layout sections mask words,
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.pages.scalar.compressedBytes ∧
      (match status with
       | Page.Checksum.Status.absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      CheckedFrame.Huffman.FrameWire frameLimits stored.toList expanded frameHeader ∧
      frameHeader.windowSize ≤ limits.compression.window ∧
      expanded.length = page.frame.value.uncompressedSize ∧
      expanded.length ≤ limits.pages.scalar.uncompressedBytes ∧
      FlatPage.split layout limits.pages.scalar.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues limits.pages.scalar.levels sections.definitions = .ok mask ∧
      Plain.decodeInt32 (mask.count true) sections.scalars = .ok words ∧
      slots.map Option.isSome = mask ∧ slots.filterMap id = words := by
  obtain ⟨_, _, actualParams, version, sizes⟩ := exactV1Parameters planned
  obtain ⟨⟨status, verified⟩, codec, params, layout, decoded, words, actual, _, _, _, expandedCap,
    prepared, scalar, restored⟩ := read
  have paramsEq : params = page.params := by
    rw [codec, actualParams] at actual
    exact (Option.some.inj actual).symm
  subst params
  rw [FlatColumn.Zstd.PreparedWire, version] at prepared
  obtain ⟨_, _, expanded, sections, payload, split, mask, values⟩ := prepared
  obtain ⟨_, _, expandedSize, _, profile⟩ := payload
  obtain ⟨frameHeader, frameWire, window⟩ := (profile.resolve_left (by simp)).2
  obtain ⟨slice, size, cap, crc⟩ := Date.Leaf.Gzip.stored_exact verified
  obtain ⟨orderedMask, orderedWords⟩ := FlatPage.reconstruct_ok_iff.mp restored
  have count := congrArg List.length orderedMask
  rw [List.length_map, FlatPage.readMask_length mask] at count
  rw [values] at scalar
  have expandedExact : expanded.length = page.frame.value.uncompressedSize := by
    simpa [ScalarPage.Limits.payloadBounds, sizes] using expandedSize
  exact ⟨count, status, expanded, frameHeader, layout, sections, decoded.mask, words,
    slice, size, cap, by cases status <;> exact crc, frameWire, window, expandedExact,
    expandedExact.trans_le (by simpa [columnLimits] using expandedCap),
    split, mask, scalar, orderedMask, orderedWords⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound checked.selection.column.metadata) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have paired : List.Forall₂ (PageWire limits bound checked.selection.column.metadata) checked.data pages := by
    have zipped := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ h => decodePage_wire h
    simpa using List.forall₂_map_left_iff.mpr zipped
  have wire := checkGroup_wire planned
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    have admitted := wire.data
    clear read decoded
    generalize checked.data = data at admitted paired ⊢
    induction paired with
    | nil => rfl
    | cons first _ ih =>
      have plan := admitted _ List.mem_cons_self
      exact congrArg₂ List.cons (pageWire_exact plan first).1
        (ih (fun p member => admitted p (List.mem_cons_of_mem _ member)))
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Date.Leaf.Gzip.CheckedGroup} {page : Date.Leaf.Gzip.DataPage}
    {before after : List (Date.Leaf.Gzip.DataPage × Nat)} {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.selection.column.metadata item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.selection.column.metadata page ordinal = .error cause) :
    readGroup limits bound index = .error cause := by
  simp [readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd

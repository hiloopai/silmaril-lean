module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {page : Date.Leaf.Gzip.DataPage}
    (planned : planData bound frame ordinal = .ok page) :
    page.frame = frame ∧ ∃ data, frame.value.kind = .dataV2 data ∧ data.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          (Date.Leaf.Zstd.columnLayout bound).levels, data.numValues, Payload.Codec.zstd.id,
          data.encoding, .v2 data.numNulls data.numRows data.repetitionBytes
            data.definitionBytes (some data.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 data =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i encoding
    simp [FlatColumn.pageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, data, rfl, not_not.mp encoding, rfl⟩
  | dataV1 _ | dictionary _ | skipped _ => simp [planData, kind] at planned

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : Date.Leaf.Gzip.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked := by
  apply Date.Leaf.Gzip.checkGroupFor_wire _ accepted
  intro frame ordinal page planned
  have same := (planData_wire planned).1
  exact ⟨same, ordinal, by rwa [same]⟩

theorem suffixWire_of {limits : Limits} {frame : Page.Frame} {data : Page.DataV2}
    {stored plain : List UInt8} (payload : FlatColumn.Zstd.PayloadWire limits.compression
      (limits.pages.scalar.payloadBounds ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ data.definitionBytes)
      (ScalarPage.v2Codec 6 (some data.isCompressed)) stored plain) :
    SuffixWire limits frame data stored plain := by
  obtain ⟨inputSize, _, outputSize, _, profile⟩ := payload
  refine ⟨inputSize, outputSize, ?_⟩
  cases flag : data.isCompressed <;>
    simpa [ScalarPage.v2Codec, flag, Payload.Codec.id] using profile

theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {page : Date.Leaf.Gzip.DataPage} {ordinal plannedOrdinal : Nat} {slots : Slots}
    (planned : planData bound page.frame plannedOrdinal = .ok page)
    (read : decodePage limits bound metadata page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes page slots := by
  obtain ⟨_, data, kind, tag, exactParams⟩ := planData_wire planned
  have inner := Date.Leaf.Zstd.decodePage_wire (mapError_ok read)
  obtain ⟨⟨status, verified⟩, codec, params, layout, prepared, words, paramsAt, valid, _, _, expandedCap, wire,
    decoded, restored⟩ := inner
  have paramsEq : params = page.params := by
    rw [codec] at paramsAt
    simp [FlatColumn.pageParameters, kind, exactParams, Payload.Codec.id] at paramsAt ⊢
    exact paramsAt.symm
  subst params
  rw [FlatColumn.Zstd.PreparedWire, exactParams] at wire
  obtain ⟨nulls, rows, repetition, defStored, defExpanded, defCap, levels, encoded,
    levelSize, split, mask, present, payload⟩ := wire
  have suffix : SuffixWire limits page.frame data encoded prepared.scalars.toList := suffixWire_of payload
  obtain ⟨slice, storedSize, storedCap, crc⟩ := Date.Leaf.Gzip.stored_exact verified
  obtain ⟨orderedMask, orderedWords⟩ := FlatPage.reconstruct_ok_iff.mp restored
  have count := congrArg List.length orderedMask
  rw [List.length_map, FlatPage.readMask_length mask] at count
  have presentCount := (FlatPage.reconstruct_exists_iff prepared.mask words).mp ⟨slots, restored⟩
  have headerCount : (slots.filterMap id).length + data.numNulls = data.numValues := by
    rw [orderedWords, ← presentCount]
    change prepared.mask.count true = data.numValues - data.numNulls at present
    change data.numNulls ≤ data.numValues at nulls
    omega
  exact ⟨by simpa [exactParams] using count, status, data, layout, levels, encoded, prepared, words,
    kind, tag, slice, storedSize, storedCap, by simpa [Date.Leaf.Zstd.columnLimits] using expandedCap,
    by cases status <;> exact crc, rows, nulls, repetition, defStored, defExpanded, defCap,
    levelSize, split, suffix, by simpa [Date.Leaf.Zstd.columnLimits] using valid,
    mask, decoded, orderedMask, orderedWords, count, headerCount⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have wire := checkGroup_wire planned
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages := by
    have admitted := wire.data
    have indexed := List.mapM_eq_ok_iff_forall₂.mp decoded
    have plans : ∀ entry ∈ checked.data.zipIdx, ∃ i, planData bound entry.1.frame i = .ok entry.1 := by
      intro entry member
      apply admitted
      rw [← List.zipIdx_map_fst 0 checked.data]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    have pairedIndexed : List.Forall₂
        (fun (entry : Date.Leaf.Gzip.DataPage × Nat) slots => PageWire limits bound.snapshot.bytes entry.1 slots)
        checked.data.zipIdx pages := by
      clear read decoded
      generalize checked.data.zipIdx = entries at plans indexed
      induction indexed with
      | nil => exact .nil
      | cons first _ ih =>
        obtain ⟨i, plan⟩ := plans _ List.mem_cons_self
        exact .cons (decodePage_wire plan first) (ih fun entry member => plans entry (List.mem_cons_of_mem _ member))
    simpa using List.forall₂_map_left_iff.mpr pairedIndexed
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons first _ ih => exact congrArg₂ List.cons first.count ih
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

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.V2

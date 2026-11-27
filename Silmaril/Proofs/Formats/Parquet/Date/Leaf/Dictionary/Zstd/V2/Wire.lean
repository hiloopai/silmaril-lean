module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2
open Silmaril.Formats.Parquet.DictionaryChunk (DataPage)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ page.params.encoding = 8 ∧
      ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
        page.params =
          ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
            (Date.Leaf.Zstd.columnLayout bound).levels, header.numValues, Payload.Codec.zstd.id,
            header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
              header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i rejected
    simp [FlatColumn.pageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, not_not.mp rejected, header, rfl, not_not.mp rejected, rfl⟩
  | dataV1 _ | dictionary _ | skipped _ => simp [planData, kind] at planned

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) := by
  unfold planPages at planned
  have zipped := (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun _ _ read => mapError_ok read
  have paired : List.Forall₂ (fun frame page => planData bound frame = .ok page) frames pages := by
    rw [← List.zipIdx_map_fst 1 frames, List.forall₂_map_left_iff]
    exact zipped
  clear planned zipped
  induction paired with
  | nil => simp
  | cons head _ ih =>
    have original := (planData_wire head).1
    refine ⟨by simp [original, ih.1], ?_⟩
    intro page member
    rcases List.mem_cons.mp member with rfl | later
    · rwa [original]
    · exact ih.2 page later

theorem planPages_firstError {bound : Bound} {frames : List Page.Frame}
    {before after : List (Page.Frame × Nat)} {frame : Page.Frame} {ordinal : Nat}
    {pages : List DataPage} {cause : HeaderError}
    (split : frames.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (GroupError.header i item.header.start)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    planPages bound frames = .error (.header ordinal frame.header.start cause) := by
  unfold planPages
  rw [split, List.mapM_append, earlier]
  simp [failed, Bind.bind, Except.bind, Except.mapError]

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      ∀ page ∈ checked.data, page.params.encoding = 8 := by
  have wire := (Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_wire (valid := fun _ => True)
    (fun planned => let ⟨order, data⟩ := planPages_wire planned; ⟨order, data, trivial⟩) accepted).1
  refine ⟨wire, ?_, fun page member => (planData_wire (wire.data page member)).2.1⟩
  intro empty
  have offset := wire.dataOffset
  simp [empty] at offset

theorem readEntries_wire {limits : Limits} {source : Bytes} {frame : Page.Frame} {entries : List Int32}
    (read : readEntries limits source frame = .ok entries) : DictionaryWire limits source frame entries := by
  cases kind : frame.value.kind with
  | dataV1 _ | dataV2 _ | skipped _ => simp [readEntries, kind] at read
  | dictionary data =>
    simp only [readEntries, kind] at read
    split at read
    · contradiction
    rename_i encoding
    split at read
    · contradiction
    rename_i count
    obtain ⟨status, checked, read⟩ := bind_ok read
    obtain ⟨expanded, decoded, read⟩ := bind_ok read
    obtain ⟨slice, storedSize, storedCap, crc⟩ := Date.Leaf.Gzip.stored_exact (mapError_ok checked)
    obtain ⟨_, _, size, cap, profile⟩ := FlatColumn.Zstd.decodePayload_sound (mapError_ok decoded)
    obtain ⟨header, wire, window⟩ := (profile.resolve_left (by simp [Payload.Codec.id])).2
    have words := mapError_ok read
    obtain ⟨_, _, _, rows, _, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp
      (by simpa only [Plain.decodeInt32] using words)
    exact ⟨status, data, expanded, header, kind, not_not.mp encoding, Nat.le_of_not_gt count,
      slice, storedSize, storedCap, by cases status <;> exact crc, wire, window, size, cap, words,
      by simpa using rows⟩

theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries :=
  readEntries_wire (checkGroup_wire accepted).1.dictionary

theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  obtain ⟨_, _, data, kind, tag, params⟩ := planData_wire planned
  unfold decodePage at decoded
  obtain ⟨status, crcRead, decoded⟩ := bind_ok decoded
  obtain ⟨prepared, prepRead, decoded⟩ := bind_ok decoded
  have verified : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status :=
    mapError_ok (mapError_ok crcRead)
  obtain ⟨slice, storedSize, storedCap, crc⟩ := Date.Leaf.Gzip.stored_exact verified
  obtain ⟨_, layout, valid, _, _, expansionBound, wire⟩ := FlatColumn.Zstd.prepareFor_sound (mapError_ok prepRead)
  rw [FlatColumn.Zstd.PreparedWire, params] at wire
  obtain ⟨nulls, rows, repetitions, levelStored, levelExpanded, levelCap, definitions, encoded,
    defSize, split, mask, present, payload⟩ := wire
  have suffix : Date.Leaf.Zstd.V2.SuffixWire (scalarLimits limits) page.frame data encoded prepared.scalars.toList :=
    Date.Leaf.Zstd.V2.suffixWire_of payload
  have refs := mapError_ok decoded
  unfold decodeReferences at refs
  obtain ⟨indices, refs, selected⟩ := bind_ok refs
  obtain ⟨words, selected, restored⟩ := bind_ok selected
  have restored := mapError_ok restored
  obtain ⟨_, width, runs, octets, maxWidth, _, _, hybrid⟩ := DictionaryIndex.readIndices_ok_iff.mp refs
  obtain ⟨slotsMask, slotsWords⟩ := FlatPage.reconstruct_ok_iff.mp restored
  have ordered := DictionaryIndex.select_ok_iff.mp selected
  rw [← slotsWords] at ordered
  have count := congrArg List.length slotsMask
  rw [List.length_map, FlatPage.readMask_length mask] at count
  have presentCount := (FlatPage.reconstruct_exists_iff prepared.mask words).mp ⟨slots, restored⟩
  have headerCount : (slots.filterMap id).length + data.numNulls = data.numValues := by
    rw [slotsWords, ← presentCount]
    change prepared.mask.count true = data.numValues - data.numNulls at present
    change data.numNulls ≤ data.numValues at nulls
    omega
  exact ⟨by simpa [params] using count, status, data, layout, definitions, encoded, prepared, width, runs, indices,
    kind, tag, slice, storedSize, storedCap, by simpa [params, scalarLimits, Date.Leaf.Zstd.columnLimits] using expansionBound,
    by cases status <;> exact crc, rows, nulls, repetitions, levelStored, levelExpanded, levelCap,
    defSize, split, suffix, valid, mask, octets, maxWidth, hybrid, ordered, slotsMask, count, headerCount⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ (∀ page ∈ checked.data, page.params.encoding = 8) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Dictionary.Zstd.V2.readGroup Date.Leaf.Fallback.Gzip.readGroupWith at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨wire, nonempty, tags⟩ := checkGroup_wire planned
  have zipped := List.mapM_eq_ok_iff_forall₂.mp decoded
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages := by
    have raw : List.Forall₂
        (fun page out => ∃ ordinal, decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal =
          .ok out) checked.data pages := by
      rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
      exact zipped.imp fun item _ read => ⟨item.2, read⟩
    have admitted := wire.data
    clear wire nonempty tags zipped decoded planned read
    generalize checked.data = data at admitted raw ⊢
    induction raw with
    | nil => exact .nil
    | cons head _ ih =>
      obtain ⟨_, decoded⟩ := head
      exact .cons (decodePage_wire (admitted _ (List.mem_cons_self ..)) decoded)
        (ih fun page member => admitted page (List.mem_cons_of_mem _ member))
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded wire nonempty tags zipped
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail => exact congrArg₂ List.cons head.count tail
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, nonempty, tags, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Dictionary.Zstd.V2.readGroup, Date.Leaf.Fallback.Gzip.readGroupWith, admitted,
    split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2

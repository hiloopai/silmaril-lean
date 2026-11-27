module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = 1 ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Snappy.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data,
        Leaf.Dictionary.Snappy.planDataWith Leaf.Fallback.admits bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, data, entries, plans, sequence, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (encoding := .snappyDictionary)
      (plan := Leaf.Dictionary.Snappy.planDataWith Leaf.Fallback.admits bound)
      (validate := Leaf.Fallback.checkSequence) (read := Leaf.Dictionary.Snappy.readEntries limits leafLimits bound)
      (fun success => (Leaf.Dictionary.Snappy.planDataWith_wire success).1) accepted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec] using codec,
    cap, frames, chain, dictionary, data, entries, plans, Leaf.Fallback.checkSequence_wire sequence, rows⟩

theorem decodePage_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : Leaf.Fallback.admits page.params.encoding = true)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    DataWire limits leafLimits bound entries page slots := by
  unfold decodePage at read
  obtain ⟨status, verified, physical⟩ := bind_ok read
  exact ⟨status, mapError_ok verified, Leaf.Fallback.decodePage_wire admitted physical⟩

theorem plain_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (plain : page.params.encoding = 0) (read : DataWire limits leafLimits bound entries page slots) :
    ∃ status layout prepared words,
      Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ leafLimits.page.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params leafLimits.page layout (Leaf.Internal.body bound page.frame) prepared ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨status, checkedCRC, _, dictionary | physical⟩ := read
  · rw [plain] at dictionary
    exact (by decide : ¬ (0 : Int) = 8) dictionary.1 |>.elim
  · obtain ⟨prepared, words, body, decoded, mask, signed, _, _⟩ :=
      ScalarPage.decode_sound physical.2
    obtain ⟨layout, admitted, wire⟩ := ScalarPage.prepare_sound body
    exact ⟨status, layout, prepared, words, checkedCRC, Leaf.Dictionary.Snappy.expanded_bound admitted,
      wire, decoded, mask, signed⟩

private theorem pages_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {pages : List DataPage} {slots : List (List (Option Int64))}
    (reads : List.Forall₂ (fun item output =>
      decodePage limits leafLimits bound entries item.1 item.2 = .ok output) (pages.zipIdx 1) slots)
    (admitted : ∀ page ∈ pages, Leaf.Fallback.admits page.params.encoding = true) :
    List.Forall₂ (DataWire limits leafLimits bound entries) pages slots := by
  have paired : List.Forall₂ (fun page output => ∃ ordinal,
      decodePage limits leafLimits bound entries page ordinal = .ok output) pages slots := by
    rw [← List.zipIdx_map_fst 1 pages, List.forall₂_map_left_iff]
    exact reads.imp fun item _ read => ⟨item.2, read⟩
  clear reads
  induction paired with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨_, decoded⟩ := head
    exact .cons (decodePage_wire (admitted _ (List.mem_cons_self ..)) decoded)
      (ih fun page member => admitted page (List.mem_cons_of_mem _ member))

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (DataWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, selected, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨_, _, _, _, _, _, _, _, plans, _, total⟩ := checkGroup_wire selected
  have admitted : ∀ page ∈ checked.data, Leaf.Fallback.admits page.params.encoding = true := by
    intro page member
    exact (Leaf.Dictionary.Snappy.planDataWith_wire (plans page member)).2.2
  have raw := pages_wire (List.mapM_eq_ok_iff_forall₂.mp decoded) admitted
  have sizes : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded admitted total plans
    generalize checked.data = data at raw ⊢
    induction raw with
    | nil => rfl
    | cons first _ rest =>
      obtain ⟨_, _, size, _⟩ := first
      exact congrArg₂ List.cons size rest
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, selected, raw, mapped, ?_⟩
  rw [mapped, List.length_map, List.length_flatten, sizes, total]

theorem readGroup_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy

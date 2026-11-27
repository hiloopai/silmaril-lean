module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (CheckedChunk DataPage)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2
open Silmaril.Numeric.Timestamp (Ticks)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (read : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ (header.encoding = 8 ∨ header.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        header.numValues, Payload.Codec.zstd.id, header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  obtain ⟨same, header, kind, tag, params⟩ :=
    Leaf.Dictionary.Zstd.V2.planDataWith_wire (admits := Leaf.Fallback.admits) read
  exact ⟨same, header, kind, by simpa [Leaf.Fallback.admits] using tag, params⟩

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
      Leaf.Dictionary.Zstd.V2.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, codec, stored, wire, chain, expanded, dictionary, data, entries, planned, phase, rows⟩ :=
    Leaf.Dictionary.Zstd.V2.checkGroupWith_wire (admits := Leaf.Fallback.admits)
      (validate := Leaf.Fallback.checkSequence) accepted
  exact ⟨selected, codec, stored, wire, chain, expanded, dictionary, data, entries, planned,
    Leaf.Fallback.checkSequence_wire phase, rows⟩

theorem checkGroup_no_reentry {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk} {i j : Nat} {a b : DataPage}
    (accepted : checkGroup limits leafLimits bound index = .ok checked)
    (earlier : checked.data[i]? = some a) (later : checked.data[j]? = some b)
    (before : i < j) (plain : a.params.encoding = 0) : b.params.encoding = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ordered, _⟩ := checkGroup_wire accepted
  obtain ⟨references, suffix, sequence, _, _, refTags, plainTags⟩ := ordered
  rw [sequence] at earlier later
  have past : references.length ≤ i := by
    by_contra! shorter
    rw [List.getElem?_append_left shorter] at earlier
    have tag := refTags a (List.mem_of_getElem? earlier)
    omega
  rw [List.getElem?_append_right (by omega : references.length ≤ j)] at later
  exact plainTags b (List.mem_of_getElem? later)

theorem checkGroup_first_header_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .ok framed)
    (cap : (framed.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => (planData bound item).mapError
      (Leaf.Zstd.V2.GroupError.selection ∘ Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    checkGroup limits leafLimits bound index =
      .error (.selection (.dictionaryPage ordinal frame.header.start cause)) := by
  rw [planData] at failed
  have prefixOk := earlier
  simp only [planData] at prefixOk
  have rejected : Leaf.Dictionary.Zstd.V2.planPagesWith Leaf.Fallback.admits bound framed.data =
      .error (.selection (.dictionaryPage ordinal frame.header.start cause)) := by
    rw [Leaf.Dictionary.Zstd.V2.planPagesWith, split, List.mapM_append, prefixOk]
    simp [failed, Leaf.Dictionary.atFrame, Except.mapError, Bind.bind, Except.bind]
  simp [checkGroup, Leaf.Dictionary.Zstd.V2.checkGroupWith, Leaf.Dictionary.Zstd.V2.checkFramedWith,
    framedOk, Nat.not_lt.mpr cap,
    rejected, Except.mapError, Bind.bind, Except.bind]

theorem checkGroup_phase_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {framed : Leaf.Dictionary.FramedChunk} {pages : List DataPage} {cause : Leaf.Error}
    (framedOk : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .ok framed)
    (cap : (framed.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes)
    (planned : Leaf.Dictionary.Zstd.V2.planPagesWith Leaf.Fallback.admits bound framed.data = .ok pages)
    (failed : Leaf.Fallback.checkSequence pages = .error cause) :
    checkGroup limits leafLimits bound index = .error (.selection cause) := by
  simp [checkGroup, Leaf.Dictionary.Zstd.V2.checkGroupWith, Leaf.Dictionary.Zstd.V2.checkFramedWith,
    framedOk, Nat.not_lt.mpr cap,
    planned, failed, Except.mapError, Bind.bind, Except.bind]

theorem dictionary_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {header : Parquet.Page.Dictionary} {cause : Parquet.Page.Checksum.Error}
    (kind : frame.value.kind = .dictionary header) (plain : header.encoding = 0)
    (entries : header.numValues ≤ limits.dictionary.maxEntries)
    (failed : Parquet.Page.Checksum.verify
      (Leaf.Dictionary.Snappy.dictionaryBounds limits.dictionary leafLimits frame).compressedLimit
      bound.snapshot.bytes frame = .error cause) :
    Leaf.Dictionary.Zstd.V2.readEntries limits leafLimits bound frame =
      .error (.checksum 0 frame.header.start cause) := by
  simp [Leaf.Dictionary.Zstd.V2.readEntries, kind, plain, Nat.not_lt.mpr entries,
    failed, Except.mapError, Bind.bind, Except.bind]

theorem decodePage_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {entries : Array Int64}
    {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots := by
  obtain ⟨_, header, kind, tag, fields⟩ := planData_wire planned
  by_cases plain : page.params.encoding = 0
  · simp only [decodePage, plain, ite_true] at read
    have wire := Leaf.Zstd.V2.decodePage_wire read
    exact ⟨by simpa [fields, Leaf.Internal.pageSlots, kind] using wire.count, .inr ⟨plain, wire⟩⟩
  · have reference : page.params.encoding = 8 := by
      rw [fields] at plain ⊢
      exact tag.resolve_right plain
    simp only [decodePage, plain, ite_false] at read
    have wire := Leaf.Dictionary.Zstd.V2.decodePage_wireWith (admits := Leaf.Fallback.admits) planned reference read
    exact ⟨wire.count, .inl ⟨reference, wire⟩⟩

theorem decodePage_checksum_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {cause : Parquet.Page.Checksum.Error}
    (planned : planData bound page.frame = .ok page)
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) := by
  obtain ⟨_, _, v2, _, _⟩ := planData_wire planned
  by_cases tag : page.params.encoding = 0
  · simpa only [decodePage, tag, ite_true] using
      Leaf.Zstd.V2.decodePage_checksum_error (limits := Leaf.Dictionary.Zstd.V2.scalarLimits limits)
        (ordinal := ordinal) v2 failed
  · simpa only [decodePage, tag, ite_false] using
      Leaf.Dictionary.Zstd.V2.decodePage_checksum_error (limits := limits) (entries := entries)
        (ordinal := ordinal) failed

theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : GroupError}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits leafLimits bound checked.entries.toArray item i) = .ok outputs)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, Leaf.Dictionary.Zstd.V2.readGroupUsing, admitted, split, earlier, failed, Bind.bind, Except.bind]

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      Leaf.Dictionary.Zstd.V2.DictionaryWire limits leafLimits bound checked.dictionary checked.entries ∧
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  unfold readGroup Leaf.Dictionary.Zstd.V2.readGroupUsing at read
  obtain ⟨checked, accepted, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨_, _, _, _, _, _, _, _, dictionary, plans, _, rows⟩ := checkGroup_wire accepted
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
    | cons first _ ih => exact congrArg₂ List.cons first.1 ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, accepted, Leaf.Dictionary.Zstd.V2.readEntries_wire dictionary, paired, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · rw [mapped, List.length_map, List.length_flatten, counts, rows]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2

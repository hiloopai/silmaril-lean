module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy
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

theorem planPrefix_firstError {bound : Bound} {before after : List (Page.Frame × Nat)}
    {frame : Page.Frame} {ordinal : Nat} {pages : List DataPage}
    {cause : Date.Leaf.Dictionary.Snappy.PageError}
    (earlier : before.mapM
      (fun entry => Date.Leaf.Dictionary.Snappy.planDataWith admits bound entry.1) = .ok pages)
    (failed : Date.Leaf.Dictionary.Snappy.planDataWith admits bound frame = .error cause) :
    planPrefix bound (before ++ (frame, ordinal) :: after) =
      (pages, some (Date.Leaf.Dictionary.Snappy.atFrame ordinal frame cause)) :=
  Date.Leaf.Fallback.planPrefixWith_firstError earlier failed

theorem planPages_earlierPhaseError {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option Date.Leaf.Dictionary.Snappy.GroupError} {ordinal offset : Nat} {tag : Int}
    (scanned : planPrefix bound (frames.zipIdx 1) = (pages, failure)) :
    (Date.Leaf.Fallback.checkSequence pages = .error (.prefixEncoding ordinal offset tag) →
      planPages bound frames = .error (.sequence (.prefixEncoding ordinal offset tag))) ∧
    (Date.Leaf.Fallback.checkSequence pages = .error (.suffixEncoding ordinal offset tag) →
      planPages bound frames = .error (.sequence (.suffixEncoding ordinal offset tag))) :=
  Date.Leaf.Fallback.planPagesWith_earlierPhaseError scanned

theorem planPages_headerError {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {cause : Date.Leaf.Dictionary.Snappy.GroupError}
    (scanned : planPrefix bound (frames.zipIdx 1) = (pages, some cause))
    (phase : Date.Leaf.Fallback.checkSequence pages = .ok () ∨
      Date.Leaf.Fallback.checkSequence pages = .error .missingReferences ∨
      Date.Leaf.Fallback.checkSequence pages = .error .missingPlain) :
    planPages bound frames = .error (.snappy cause) :=
  Date.Leaf.Fallback.planPagesWith_headerError scanned phase

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Dictionary.Snappy.planDataWith admits bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Date.Leaf.Fallback.planPagesWith_wire (fun h => (Date.Leaf.Dictionary.Snappy.planDataWith_wire h).1) planned

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Date.Leaf.Dictionary.Snappy.GroupWire limits bound index checked admits ∧
      Date.Leaf.Fallback.Ordered checked.data :=
  Date.Leaf.Dictionary.Snappy.checkGroupWith_wire (fun h => planPages_wire h) accepted

theorem transition_totals {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    ∃ references plain, checked.data = references ++ plain ∧
      references ≠ [] ∧ plain ≠ [] ∧
      (∀ page ∈ references, page.params.encoding = 8) ∧
      (∀ page ∈ plain, page.params.encoding = 0) ∧
      (references.map (·.params.numValues)).sum + (plain.map (·.params.numValues)).sum =
        checked.selection.group.numRows.toNat ∧
      checked.dictionary.value.uncompressedSize +
        ((references.map (·.frame.value.uncompressedSize)).sum +
          (plain.map (·.frame.value.uncompressedSize)).sum) ≤ limits.maxExpandedChunkBytes := by
  obtain ⟨wire, references, plain, order, first, second, refs, raw⟩ := checkGroup_wire accepted
  exact ⟨references, plain, order, first, second, refs, raw,
    by simpa [order, List.sum_append] using wire.rows,
    by simpa [Date.Leaf.Dictionary.Snappy.CheckedGroup.frames, order, List.sum_append, List.map_map,
      Function.comp_def] using wire.expandedCap⟩

theorem decodePage_wire {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots} (admitted : admits page.params.encoding = true)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  by_cases plain : page.params.encoding = 0
  · simp only [decodePage, plain, ite_true] at decoded
    obtain ⟨status, crc, read⟩ := bind_ok decoded
    have body := mapError_ok read
    exact ⟨(ScalarPage.decode_counts body).1, .inr ⟨plain, status,
      Date.Leaf.Dictionary.Snappy.verifyData_wire (mapError_ok crc), body⟩⟩
  · have tag : page.params.encoding = 8 := by simpa [admits, plain] using admitted
    have body := mapError_ok (by simpa only [decodePage, plain, ite_false] using decoded)
    have wire := Date.Leaf.Dictionary.Snappy.decodePage_wire body
    have count : slots.length = page.params.numValues := by
      obtain ⟨_, _, refs⟩ := wire
      exact (DictionaryIndex.decode_counts refs).1
    exact ⟨count, .inl ⟨tag, wire⟩⟩

theorem plainWire_exact {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {slots : Slots} (wire : PageWire limits source entries page slots)
    (plain : page.params.encoding = 0) :
    let body := Page.Checksum.payloadBytes source page.frame
    ∃ status layout prepared words,
      Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
      ScalarPage.validate page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  rcases wire.2 with ⟨references, _⟩ | ⟨_, status, crc, read⟩
  · rw [plain] at references
    contradiction
  · obtain ⟨layout, prepared, words, valid, decoded, signed, mask, order⟩ :=
      Date.Leaf.Fallback.plainWire_exact read
    exact ⟨status, layout, prepared, words, crc, valid, decoded, signed, mask, order⟩

private theorem pages_wire {limits : Limits} {source : Bytes} {entries : Array Int32}
    {pages : List DataPage} {slots : List Slots}
    (reads : List.Forall₂ (fun item out => decodePage limits source entries item.1 item.2 = .ok out)
      (pages.zipIdx 1) slots)
    (admitted : ∀ page ∈ pages, admits page.params.encoding = true) :
    List.Forall₂ (PageWire limits source entries) pages slots := by
  have paired : List.Forall₂
      (fun page out => ∃ ordinal, decodePage limits source entries page ordinal = .ok out) pages slots := by
    rw [← List.zipIdx_map_fst 1 pages, List.forall₂_map_left_iff]
    exact reads.imp fun item _ read => ⟨item.2, read⟩
  clear reads
  induction paired with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨_, decoded⟩ := head
    exact .cons (decodePage_wire (admitted _ (List.mem_cons_self ..)) decoded)
      (ih fun page member => admitted page (List.mem_cons_of_mem _ member))

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Fallback.Snappy.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Date.Leaf.Dictionary.Snappy.GroupWire limits bound index checked admits ∧
      Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Fallback.Snappy.readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨wire, phases⟩ := checkGroup_wire planned
  have paired := pages_wire (List.mapM_eq_ok_iff_forall₂.mp decoded)
    (fun page member => (Date.Leaf.Dictionary.Snappy.planDataWith_wire (wire.data page member)).2.1)
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded wire phases
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail => exact congrArg₂ List.cons head.1 tail
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, phases, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup} {page : DataPage}
    {before after : List (DataPage × Nat)} {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    Date.Leaf.Fallback.Snappy.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Fallback.Snappy.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Snappy

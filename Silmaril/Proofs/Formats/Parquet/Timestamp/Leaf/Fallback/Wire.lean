module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.TakeWhile
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem checkSequenceWith_wire {dictionaryTag : Int} {data : List DataPage}
    (checked : checkSequenceWith dictionaryTag data = .ok ()) : OrderedWith dictionaryTag data := by
  cases data with
  | nil => contradiction
  | cons first rest =>
    simp only [checkSequenceWith] at checked
    split at checked
    · contradiction
    rename_i firstIsDictionary
    let data := first :: rest
    let referencePages := data.takeWhile (isDictionaryWith dictionaryTag)
    let suffix := data.dropWhile (isDictionaryWith dictionaryTag)
    let start := data.length - suffix.length + 1
    change (if suffix.isEmpty then Except.error _ else
      match (suffix.zipIdx start).find? (fun (page, _) => page.params.encoding != 0) with
      | none => .ok ()
      | some (page, index) => .error _) = Except.ok () at checked
    split at checked
    · contradiction
    rename_i nonempty
    split at checked
    · rename_i found
      have firstOk : isDictionaryWith dictionaryTag first = true := by simpa using firstIsDictionary
      have before : referencePages ≠ [] := by simp [referencePages, data, firstOk]
      refine ⟨referencePages, suffix, List.takeWhile_append_dropWhile.symm, before,
        fun empty => nonempty (List.isEmpty_iff.mpr empty), ?_, ?_⟩
      · intro page member
        have yes := List.mem_takeWhile_imp member
        simpa only [isDictionaryWith, beq_iff_eq] using yes
      · intro page member
        have inMap : page ∈ (suffix.zipIdx start).map Prod.fst := by
          simpa only [List.zipIdx_map_fst] using member
        obtain ⟨⟨item, ordinal⟩, zipped, rfl⟩ := List.mem_map.mp inMap
        have valid := List.find?_eq_none.mp found (item, ordinal) zipped
        simpa using valid
    · contradiction

theorem checkSequence_wire {data : List DataPage} (checked : checkSequence data = .ok ()) :
    Ordered data :=
  checkSequenceWith_wire checked

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.readEntries limits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, Leaf.Dictionary.planDataWith admits bound page.frame = .ok page) ∧
      Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selection, cap, frames, chain, dictionary, data, entries, pages, sequence, rows⟩ :=
    Leaf.Dictionary.checkGroupWith_wire (admits := admits) (validate := checkSequence) accepted
  exact ⟨selection, cap, frames, chain, dictionary, data, entries, pages,
    checkSequence_wire sequence, rows⟩

theorem decodePage_wireWith {dictionaryTag : Int} {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : page.params.encoding = dictionaryTag ∨ page.params.encoding = 0)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWireWith dictionaryTag limits leafLimits bound entries page slots := by
  by_cases plain : page.params.encoding = 0
  · have decoded := mapError_ok (by simpa only [decodePage, plain, ite_true] using read)
    exact ⟨(ScalarPage.decode_counts decoded).1, .inr ⟨plain, decoded⟩⟩
  · have encoding := admitted.resolve_right plain
    have decoded := mapError_ok (by simpa only [decodePage, plain, ite_false, Leaf.Dictionary.decodePage] using read)
    exact ⟨(DictionaryIndex.decode_counts decoded).1, .inl ⟨encoding, decoded⟩⟩

theorem decodePage_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : admits page.params.encoding = true)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots := by
  apply decodePage_wireWith (dictionaryTag := 8) _ read
  simpa [admits] using admitted

private theorem pages_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {pages : List DataPage} {slots : List (List (Option Int64))}
    (reads : List.Forall₂ (fun item output =>
      decodePage limits leafLimits bound entries item.1 item.2 = .ok output) (pages.zipIdx 1) slots)
    (admitted : ∀ page ∈ pages, admits page.params.encoding = true) :
    List.Forall₂ (PageWire limits leafLimits bound entries) pages slots := by
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
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, selected, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨_, _, _, _, _, _, _, plans, _, total⟩ := checkGroup_wire selected
  have admitted : ∀ page ∈ checked.data, admits page.params.encoding = true := by
    intro page member
    exact (Leaf.Dictionary.planDataWith_wire (plans page member)).2.2.2.2
  have raw := pages_wire (List.mapM_eq_ok_iff_forall₂.mp decoded) admitted
  have sizes : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded admitted total plans
    generalize checked.data = data at raw ⊢
    induction raw with
    | nil => rfl
    | cons first _ rest => exact congrArg₂ List.cons first.1 rest
  have mapped := (Except.ok.inj read).symm
  refine ⟨checked, pages, selected, raw, mapped, ?_⟩
  rw [mapped, List.length_map, List.length_flatten, sizes, total]

theorem readGroup_first_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {referencePages : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok referencePages)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback

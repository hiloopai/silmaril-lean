module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1
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
      ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 8 ∧
        page.params =
          ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
            ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
            header.encoding, .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩ := by
  unfold planData at planned
  obtain ⟨checked, accepted, planned⟩ := bind_ok planned
  split at planned
  · contradiction
  rename_i tag
  have encoding := not_not.mp tag
  cases Except.ok.inj planned
  obtain ⟨same, header, kind, _, params⟩ := Date.Leaf.Fallback.Gzip.planData_wire accepted
  exact ⟨same, encoding, header, kind, by simpa [params] using encoding, params⟩

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
  have wire := (Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire (valid := fun _ => True)
    (fun planned => let ⟨order, data⟩ := planPages_wire planned; ⟨order, data, trivial⟩) accepted).1
  refine ⟨wire, ?_, fun page member => (planData_wire (wire.data page member)).2.1⟩
  intro empty
  have offset := wire.dataOffset
  simp [empty] at offset

theorem checkGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    let frame := checked.dictionary
    let source := bound.snapshot.bytes
    let bounds := Date.Leaf.Dictionary.Snappy.dictionaryBounds limits.toDictionaryLimits frame
    ∃ header expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Date.Leaf.Fallback.Gzip.StoredMember source frame bounds.compressedLimit bounds.outputLimit expanded ∧
      Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok checked.entries ∧
      checked.entries.length = header.numValues :=
  Date.Leaf.Fallback.Gzip.readEntries_wire (checkGroup_wire accepted).1.dictionary

theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  obtain ⟨_, _, header, kind, tag, params⟩ := planData_wire planned
  have schema : page.params.schema = ⟨0, if bound.field.layout == .required then 0 else 1⟩ := by
    rw [params]
  have parameters := params
  rw [← schema] at parameters
  obtain ⟨_, crc, read⟩ := Date.Leaf.Dictionary.Snappy.decodePage_wire (mapError_ok decoded)
  obtain ⟨_, prepared, indices, prep, runs, mask, ordered⟩ := DictionaryIndex.decode_ok_iff.mp read
  obtain ⟨_, width, bytes, octets, maxWidth, _, _, wire⟩ := DictionaryIndex.readIndices_ok_iff.mp runs
  obtain ⟨expanded, layout, sections, layoutMatch, member, split, levels, scalars⟩ :=
    Date.Leaf.Fallback.Gzip.prepareFor_frame parameters crc prep
  exact ⟨(DictionaryIndex.decode_counts read).1, header, expanded, layout, sections, prepared, width,
    bytes, indices, kind, tag, by rw [params], layoutMatch, member, split, levels, scalars,
    mask, octets, maxWidth, wire, ordered⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Dictionary.Gzip.V1.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ (∀ page ∈ checked.data, page.params.encoding = 8) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Dictionary.Gzip.V1.readGroup Date.Leaf.Fallback.Gzip.readGroupWith at read
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
    Date.Leaf.Dictionary.Gzip.V1.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Dictionary.Gzip.V1.readGroup, Date.Leaf.Fallback.Gzip.readGroupWith, admitted,
    split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1

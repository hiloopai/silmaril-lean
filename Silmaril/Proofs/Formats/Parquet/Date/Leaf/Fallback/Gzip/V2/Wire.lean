module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2.Defs
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2
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
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧
      (header.encoding = 8 ∨ header.encoding = 0) ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
          header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i tag
    simp [FlatScan.int32PageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, header, rfl, by tauto, by simp⟩
  | dictionary _ | dataV1 _ | skipped _ => simp [planData, kind] at planned

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Date.Leaf.Fallback.planPagesWith_wire (fun planned => (planData_wire planned).1) planned

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (Date.Leaf.Fallback.Gzip.readEntries limits)
      (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data :=
  Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire planPages_wire accepted

theorem transition_totals {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    ∃ references plain, checked.data = references ++ plain ∧ references ≠ [] ∧ plain ≠ [] ∧
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
  obtain ⟨_, header, kind, tag, params⟩ := planData_wire planned
  have actualTag : page.params.encoding = header.encoding := by rw [params]
  have schema : page.params.schema = ⟨0, if bound.field.layout == .required then 0 else 1⟩ := by
    rw [params]
  have parameters := params
  rw [← schema] at parameters
  unfold decodePage Date.Leaf.Fallback.Gzip.decodePageWith at decoded
  obtain ⟨_, verified, decoded⟩ := bind_ok decoded
  have crc := Date.Leaf.Dictionary.Snappy.verifyData_wire (mapError_ok verified)
  by_cases plain : page.params.encoding = 0
  · simp only [plain, ite_true] at decoded
    have read := mapError_ok decoded
    obtain ⟨prepared, words, prep, signed, mask, order, _, _⟩ := ScalarPage.decode_sound read
    have frame := Date.Leaf.Gzip.V2.prepareFor_frame kind parameters crc prep
    have counts := ScalarPage.decode_counts read
    have total := counts.1
    simp only [params] at counts
    have present := counts.2
    have nulls := frame.nulls
    exact ⟨total, header, prepared, frame, actualTag.symm, by rw [params], mask, by omega,
      .inr ⟨actualTag ▸ plain, order ▸ signed⟩⟩
  · simp only [plain, ite_false] at decoded
    have read := mapError_ok decoded
    have references := tag.resolve_right fun eq => plain (actualTag.trans eq)
    obtain ⟨_, prepared, indices, prep, runs, mask, ordered⟩ := DictionaryIndex.decode_ok_iff.mp read
    obtain ⟨_, width, bytes, octets, maxWidth, _, _, wire⟩ := DictionaryIndex.readIndices_ok_iff.mp runs
    have frame := Date.Leaf.Gzip.V2.prepareFor_frame kind parameters crc prep
    have counts := DictionaryIndex.decode_counts read
    have total := counts.1
    simp only [params] at counts
    have present := counts.2
    have nulls := frame.nulls
    exact ⟨total, header, prepared, frame, actualTag.symm, by rw [params], mask, by omega,
      .inl ⟨references, width, bytes, indices, octets, maxWidth, wire, ordered⟩⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Fallback.Gzip.V2.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (Date.Leaf.Fallback.Gzip.readEntries limits)
        (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Fallback.Gzip.V2.readGroup Date.Leaf.Fallback.Gzip.readGroupWith at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨wire, phases⟩ := checkGroup_wire planned
  have zipped := List.mapM_eq_ok_iff_forall₂.mp decoded
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages := by
    have raw : List.Forall₂
        (fun page out => ∃ ordinal, decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal =
          .ok out) checked.data pages := by
      rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
      exact zipped.imp fun item _ read => ⟨item.2, read⟩
    have admitted := wire.data
    clear wire phases zipped decoded planned read
    generalize checked.data = data at admitted raw ⊢
    induction raw with
    | nil => exact .nil
    | cons head _ ih =>
      obtain ⟨_, decoded⟩ := head
      exact .cons (decodePage_wire (admitted _ (List.mem_cons_self ..)) decoded)
        (ih fun page member => admitted page (List.mem_cons_of_mem _ member))
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded wire phases zipped
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail => exact congrArg₂ List.cons head.count tail
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, phases, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    Date.Leaf.Fallback.Gzip.V2.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Fallback.Gzip.V2.readGroup, Date.Leaf.Fallback.Gzip.readGroupWith, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2

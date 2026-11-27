module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1
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

private theorem dictionary_plan_data {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : Date.Leaf.Dictionary.Gzip.V1.planData bound frame = .ok page) :
    Date.Leaf.Fallback.Gzip.planData bound frame = .ok page := by
  unfold Date.Leaf.Dictionary.Gzip.V1.planData at planned
  obtain ⟨candidate, admitted, returned⟩ := bind_ok planned
  split at returned
  · contradiction
  cases Except.ok.inj returned
  exact admitted

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Gzip.planData bound page.frame = .ok page) ∧
      Phase (profile frames) pages := by
  cases chosen : profile frames with
  | dictionary =>
    have admitted := mapError_ok (by simpa only [planPages, chosen] using planned)
    obtain ⟨order, reads⟩ := Date.Leaf.Dictionary.Gzip.V1.planPages_wire admitted
    exact ⟨order, fun page member => dictionary_plan_data (reads page member),
      fun page member => (Date.Leaf.Dictionary.Gzip.V1.planData_wire (reads page member)).2.1⟩
  | fallback =>
    exact Date.Leaf.Fallback.Gzip.planPages_wire (by simpa only [planPages, chosen] using planned)

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      Phase (profile (checked.data.map (·.frame))) checked.data := by
  have keeps {frames pages} (planned : planPages bound frames = .ok pages) :
      pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Gzip.planData bound page.frame = .ok page) ∧
      Phase (profile (pages.map (·.frame))) pages := by
    obtain ⟨order, data, phases⟩ := planPages_wire planned
    exact ⟨order, data, by simpa only [order] using phases⟩
  obtain ⟨wire, phases⟩ := Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire keeps accepted
  refine ⟨wire, ?_, phases⟩
  intro empty
  have offset := wire.dataOffset
  simp [empty] at offset

theorem checkGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    checkGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.checkGroup limits bound index).mapError dictionaryError := by
  obtain ⟨_, _, selected, framed⟩ := original
  exact Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_agrees
    (plan := Date.Leaf.Dictionary.Gzip.V1.planPages bound) (otherPlan := planPages bound)
    selected framed (fun _ => rfl) (by simp [planPages, chosen])

theorem checkGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    checkGroup limits bound index = Date.Leaf.Fallback.Gzip.checkGroup limits bound index := by
  obtain ⟨_, _, selected, framed⟩ := original
  have same := Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_agrees
    (wrap := Date.Leaf.Fallback.Gzip.GroupError.chunk) (otherWrap := .chunk) (lift := id)
    (plan := Date.Leaf.Fallback.Gzip.planPages bound) (otherPlan := planPages bound)
    (codec := .gzip) (readDictionary := Date.Leaf.Fallback.Gzip.readEntries limits)
    selected framed (fun _ => rfl) (by
      rw [planPages, chosen]
      cases Date.Leaf.Fallback.Gzip.planPages bound frames <;> rfl)
  change checkGroup limits bound index = (Date.Leaf.Fallback.Gzip.checkGroup limits bound index).mapError id at same
  exact same.trans (by cases Date.Leaf.Fallback.Gzip.checkGroup limits bound index <;> rfl)

private theorem dictionary_decode_agrees {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} (reference : page.params.encoding = 8) :
    Date.Leaf.Fallback.Gzip.decodePage limits source entries page ordinal =
      (Date.Leaf.Dictionary.Gzip.V1.decodePage limits source entries page ordinal).mapError dictionaryError := by
  unfold Date.Leaf.Fallback.Gzip.decodePage Date.Leaf.Dictionary.Gzip.V1.decodePage
  rw [Date.Leaf.Fallback.Gzip.decodePageWith_reference_agrees _ _ reference]
  cases Date.Leaf.Dictionary.Snappy.decodePage limits.toDictionaryLimits source entries page ordinal <;> rfl

theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.readGroup limits bound index).mapError dictionaryError := by
  refine Date.Leaf.Fallback.Gzip.readGroupWith_agrees (checkGroup_dictionary_agrees original chosen) ?_
  intro group accepted page member ordinal
  exact dictionary_decode_agrees ((Date.Leaf.Dictionary.Gzip.V1.checkGroup_wire accepted).2.2 page member)

theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    readGroup limits bound index = Date.Leaf.Fallback.Gzip.readGroup limits bound index := by
  simp only [Date.Leaf.Gzip.Dispatch.V1.readGroup, Date.Leaf.Fallback.Gzip.readGroup,
    Date.Leaf.Fallback.Gzip.readGroupWith, checkGroup_fallback_agrees original chosen]

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Gzip.Dispatch.V1.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      checked.data ≠ [] ∧ Phase (profile (checked.data.map (·.frame))) checked.data ∧
      PagesWire limits bound.snapshot.bytes (profile (checked.data.map (·.frame))) checked pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  have planned : ∃ checked, checkGroup limits bound index = .ok checked := by
    unfold Date.Leaf.Gzip.Dispatch.V1.readGroup Date.Leaf.Fallback.Gzip.readGroupWith at read
    obtain ⟨checked, accepted, _⟩ := bind_ok read
    exact ⟨checked, accepted⟩
  obtain ⟨checked, accepted⟩ := planned
  obtain ⟨wire, nonempty, phases⟩ := checkGroup_wire accepted
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.selected, wire.frames⟩
  cases chosen : profile (checked.data.map (·.frame)) with
  | dictionary =>
    have admitted := mapError_ok ((checkGroup_dictionary_agrees original chosen).symm.trans accepted)
    have decoded := mapError_ok ((readGroup_dictionary_agrees original chosen).symm.trans read)
    obtain ⟨group, pages, same, _, _, _, physical, order, count⟩ :=
      Date.Leaf.Dictionary.Gzip.V1.readGroup_wire decoded
    cases Except.ok.inj (same.symm.trans admitted)
    exact ⟨checked, pages, accepted, wire, nonempty, phases, by simpa only [PagesWire, chosen] using physical, order, count⟩
  | fallback =>
    have admitted := (checkGroup_fallback_agrees original chosen).symm.trans accepted
    have decoded := (readGroup_fallback_agrees original chosen).symm.trans read
    obtain ⟨group, pages, same, _, _, physical, order, count⟩ :=
      Date.Leaf.Fallback.Gzip.readGroup_wire decoded
    cases Except.ok.inj (same.symm.trans admitted)
    exact ⟨checked, pages, accepted, wire, nonempty, phases, by simpa only [PagesWire, chosen] using physical, order, count⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      Date.Leaf.Fallback.Gzip.decodePage limits bound.snapshot.bytes checked.entries.toArray item i) =
        .ok prefixSlots)
    (failed : Date.Leaf.Fallback.Gzip.decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal =
      .error cause) :
    Date.Leaf.Gzip.Dispatch.V1.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Gzip.Dispatch.V1.readGroup, Date.Leaf.Fallback.Gzip.readGroupWith, admitted,
    split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1

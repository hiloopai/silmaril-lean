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

private theorem except_throw {α ε : Type} (cause : ε) :
    (throw cause : Except ε α) = .error cause := rfl

private theorem mapError_value {α ε δ : Type} (lift : ε → δ) (value : α) :
    (Except.ok value).mapError lift = .ok value := rfl

private theorem mapError_cause {α ε δ : Type} (lift : ε → δ) (cause : ε) :
    (Except.error (α := α) cause).mapError lift = .error (lift cause) := rfl

private theorem mapError_ite {α ε δ : Type} (lift : ε → δ) (test : Prop) [Decidable test]
    (yes no : Except ε α) :
    (if test then yes else no).mapError lift = if test then yes.mapError lift else no.mapError lift :=
  apply_ite (Except.mapError lift) test yes no

private theorem checkGroupWith_agrees {ε : Type} {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (wrap : Date.Leaf.Dictionary.Snappy.GroupError → ε) (lift : ε → GroupError)
    (oldPlan : List Page.Frame → Except ε (List DataPage))
    (wrap_eq : ∀ cause, lift (wrap cause) = .chunk cause)
    (plan_eq : planPages bound frames = (oldPlan frames).mapError lift) :
    checkGroup limits bound index =
      (Date.Leaf.Dictionary.Snappy.checkGroupWithCodec .gzip wrap
        (Date.Leaf.Fallback.Gzip.readEntries limits) oldPlan limits.toDictionaryLimits bound index).mapError lift := by
  obtain ⟨_, dictionary, selected, framed⟩ := original
  unfold checkGroup Date.Leaf.Dictionary.Snappy.checkGroupWithCodec
  cases frames with
  | nil =>
    simp only [selected, framed, mapError_value, Bind.bind, Except.bind,
      mapError_ite, except_throw, mapError_cause, wrap_eq]
  | cons first rest =>
    simp only [selected, framed, mapError_value, Bind.bind, Except.bind,
      mapError_ite, mapError_cause, wrap_eq]
    rw [plan_eq]
    cases oldPlan (first :: rest) with
    | error => simp only [mapError_cause]
    | ok =>
      cases Date.Leaf.Fallback.Gzip.readEntries limits bound.snapshot.bytes dictionary <;>
        simp only [mapError_value, mapError_cause, Function.comp_apply, mapError_ite, wrap_eq,
          Pure.pure, Except.pure]

theorem checkGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    checkGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.checkGroup limits bound index).mapError dictionaryError := by
  exact checkGroupWith_agrees original .chunk dictionaryError (Date.Leaf.Dictionary.Gzip.V1.planPages bound)
    (fun _ => rfl) (by simp [planPages, chosen])

theorem checkGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    checkGroup limits bound index = Date.Leaf.Fallback.Gzip.checkGroup limits bound index := by
  have same := checkGroupWith_agrees original Date.Leaf.Fallback.Gzip.GroupError.chunk id
    (Date.Leaf.Fallback.Gzip.planPages bound) (fun _ => rfl) (by
      rw [planPages, chosen]
      cases Date.Leaf.Fallback.Gzip.planPages bound frames <;> rfl)
  change checkGroup limits bound index = (Date.Leaf.Fallback.Gzip.checkGroup limits bound index).mapError id at same
  exact same.trans (by cases Date.Leaf.Fallback.Gzip.checkGroup limits bound index <;> rfl)

private theorem dictionary_decode_agrees {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} (reference : page.params.encoding = 8) :
    Date.Leaf.Fallback.Gzip.decodePage limits source entries page ordinal =
      (Date.Leaf.Dictionary.Gzip.V1.decodePage limits source entries page ordinal).mapError dictionaryError := by
  unfold Date.Leaf.Fallback.Gzip.decodePage Date.Leaf.Fallback.Gzip.decodePageWith
    Date.Leaf.Dictionary.Gzip.V1.decodePage Date.Leaf.Dictionary.Snappy.decodePage
  cases Date.Leaf.Dictionary.Snappy.verifyData limits.toDictionaryLimits source page ordinal
  · simp [Except.mapError, Bind.bind, Except.bind, dictionaryError]
  · cases read : DictionaryIndex.decode entries page.params limits.scalar limits.indices
        (Page.Checksum.payloadBytes source page.frame) <;>
      simp [read, reference, Except.mapError, Bind.bind, Except.bind, dictionaryError]

private theorem mapM_errors {α β ε δ : Type} {items : List α} {left : α → Except δ β}
    {right : α → Except ε β} {lift : ε → δ}
    (one : ∀ item ∈ items, left item = (right item).mapError lift) :
    items.mapM left = (items.mapM right).mapError lift := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have head := one first (List.mem_cons_self ..)
    have tail := ih fun item member => one item (List.mem_cons_of_mem first member)
    cases read : right first with
    | error => simp [List.mapM_cons, head, read, Except.mapError, Bind.bind, Except.bind]
    | ok value =>
      simp only [List.mapM_cons, head, read, Except.mapError, Bind.bind, Except.bind]
      rw [tail]
      cases rest.mapM right <;> rfl

theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Gzip.V1.readGroup limits bound index).mapError dictionaryError := by
  have checked := checkGroup_dictionary_agrees original chosen
  unfold Date.Leaf.Gzip.Dispatch.V1.readGroup Date.Leaf.Dictionary.Gzip.V1.readGroup
    Date.Leaf.Fallback.Gzip.readGroupWith
  rw [checked]
  cases accepted : Date.Leaf.Dictionary.Gzip.V1.checkGroup limits bound index with
  | error => rfl
  | ok group =>
    have tags := (Date.Leaf.Dictionary.Gzip.V1.checkGroup_wire accepted).2.2
    have reads :
        (group.data.zipIdx 1).mapM (fun (page, ordinal) =>
          Date.Leaf.Fallback.Gzip.decodePage limits bound.snapshot.bytes group.entries.toArray page ordinal) =
        ((group.data.zipIdx 1).mapM (fun (page, ordinal) =>
          Date.Leaf.Dictionary.Gzip.V1.decodePage limits bound.snapshot.bytes group.entries.toArray page ordinal)
        ).mapError dictionaryError :=
      mapM_errors (fun item member => dictionary_decode_agrees (tags item.1 (by
        rw [← List.zipIdx_map_fst 1 group.data]
        exact List.mem_map_of_mem member)))
    simp only [Except.mapError, Bind.bind, Except.bind]
    rw [reads]
    cases (group.data.zipIdx 1).mapM (fun (page, ordinal) =>
      Date.Leaf.Dictionary.Gzip.V1.decodePage limits bound.snapshot.bytes group.entries.toArray page ordinal) <;> rfl

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

module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem route_selected {bound : Bound} {index : Nat} {selected : Date.Leaf.Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    route bound index = .ok (if selected.column.metadata.dictionaryPageOffset.isSome then
      .dictionaryBacked else .plain) := by
  obtain ⟨group, column, _⟩ := Date.Leaf.selectChunk_exact admitted
  simp [route, group, column, Pure.pure, Except.pure]

theorem readGroup_routeError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : route bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) := by
  simp [readGroup, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_plain_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .plain) :
    readGroup limits bound index =
      (Date.Leaf.Zstd.V2.readGroup (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) bound index).mapError
        .plain := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

private theorem readGroup_backed {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .dictionaryBacked) :
    readGroup limits bound index = (readDictionaryGroup limits bound index).mapError .dictionaryBacked := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

private theorem dictionary_plan_data {bound : Bound} {frame : Page.Frame} {page : DictionaryChunk.DataPage}
    (planned : Date.Leaf.Dictionary.Zstd.V2.planData bound frame = .ok page) :
    Date.Leaf.Fallback.Zstd.V2.planData bound frame = .ok page := by
  obtain ⟨same, _, header, kind, tag, params⟩ := Date.Leaf.Dictionary.Zstd.V2.planData_wire planned
  cases page with
  | mk actual parameters =>
    simp only at same params
    subst actual
    subst parameters
    simp [Date.Leaf.Fallback.Zstd.V2.planData, kind, tag, FlatColumn.pageParameters, Pure.pure, Except.pure]

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DictionaryChunk.DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Zstd.V2.planData bound page.frame = .ok page) ∧
      Phase (profile frames) pages := by
  cases chosen : profile frames with
  | dictionary =>
    have accepted := mapError_ok (by simpa only [planPages, chosen] using planned)
    obtain ⟨order, reads⟩ := Date.Leaf.Dictionary.Zstd.V2.planPages_wire accepted
    exact ⟨order, fun page member => dictionary_plan_data (reads page member),
      fun page member => (Date.Leaf.Dictionary.Zstd.V2.planData_wire (reads page member)).2.1⟩
  | fallback =>
    exact Date.Leaf.Fallback.Zstd.V2.planPages_wire (by simpa only [planPages, chosen] using planned)

theorem checkDictionaryGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkDictionaryGroup limits bound index = .ok checked) :
    Date.Leaf.Fallback.Zstd.V2.GroupWire limits bound index checked ∧ checked.data ≠ [] ∧
      Phase (profile (checked.data.map (·.frame))) checked.data := by
  have keeps {frames pages} (planned : planPages bound frames = .ok pages) :
      pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Fallback.Zstd.V2.planData bound page.frame = .ok page) ∧
      Phase (profile (pages.map (·.frame))) pages := by
    obtain ⟨order, data, phase⟩ := planPages_wire planned
    exact ⟨order, data, by simpa only [order] using phase⟩
  obtain ⟨wire, phase⟩ := Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_wire keeps accepted
  refine ⟨wire, ?_, phase⟩
  intro empty
  have offset := wire.dataOffset
  simp [empty] at offset

theorem checkDictionaryGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    checkDictionaryGroup limits bound index =
      (Date.Leaf.Dictionary.Zstd.V2.checkGroup limits bound index).mapError
        Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary := by
  obtain ⟨_, _, selected, framed⟩ := original
  exact Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_agrees
    (plan := Date.Leaf.Dictionary.Zstd.V2.planPages bound) (otherPlan := planPages bound)
    selected framed (fun _ => rfl) (fun _ _ => rfl) (by simp [planPages, chosen])

theorem checkDictionaryGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    checkDictionaryGroup limits bound index = Date.Leaf.Fallback.Zstd.V2.checkGroup limits bound index := by
  obtain ⟨_, _, selected, framed⟩ := original
  have same := Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_agrees
    (codec := .zstd) (readDictionary := Date.Leaf.Dictionary.Zstd.V2.readEntries limits)
    (wrap := Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary ∘ Date.Leaf.Dictionary.Zstd.V2.GroupError.chunk)
    (otherWrap := Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary ∘ Date.Leaf.Dictionary.Zstd.V2.GroupError.chunk)
    (dictError := fun frame cause => .dictionary (.dictionary frame.header.start cause))
    (otherDictError := fun frame cause => .dictionary (.dictionary frame.header.start cause))
    (lift := id) (plan := Date.Leaf.Fallback.Zstd.V2.planPages bound) (otherPlan := planPages bound)
    selected framed (fun _ => rfl) (fun _ _ => rfl) (by
      rw [planPages, chosen]
      cases Date.Leaf.Fallback.Zstd.V2.planPages bound frames <;> rfl)
  change checkDictionaryGroup limits bound index =
    (Date.Leaf.Fallback.Zstd.V2.checkGroup limits bound index).mapError id at same
  exact same.trans (by cases Date.Leaf.Fallback.Zstd.V2.checkGroup limits bound index <;> rfl)

private theorem mapM_errors {α β ε δ : Type} {items : List α} {left : α → Except δ β}
    {right : α → Except ε β} {lift : ε → δ}
    (one : ∀ item ∈ items, left item = (right item).mapError lift) :
    items.mapM left = (items.mapM right).mapError lift := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have head := one first List.mem_cons_self
    have tail := ih fun item member => one item (List.mem_cons_of_mem first member)
    cases read : right first with
    | error => simp [List.mapM_cons, head, read, Except.mapError, Bind.bind, Except.bind]
    | ok value =>
      simp only [List.mapM_cons, head, read, Except.mapError, Bind.bind, Except.bind]
      rw [tail]
      cases rest.mapM right <;> rfl

private theorem readDictionaryGroup_dictionary {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .dictionary) :
    readDictionaryGroup limits bound index =
      (Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index).mapError
        Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary := by
  unfold readDictionaryGroup Date.Leaf.Dictionary.Zstd.V2.readGroup Date.Leaf.Fallback.Gzip.readGroupWith
  rw [checkDictionaryGroup_dictionary_agrees original chosen]
  cases admitted : Date.Leaf.Dictionary.Zstd.V2.checkGroup limits bound index with
  | error => rfl
  | ok group =>
    have tags := (Date.Leaf.Dictionary.Zstd.V2.checkGroup_wire admitted).2.2
    let decode := fun (entry : DictionaryChunk.DataPage × Nat) =>
      Date.Leaf.Dictionary.Zstd.V2.decodePage limits bound.snapshot.bytes group.entries.toArray entry.1 entry.2
    have reads : (group.data.zipIdx 1).mapM (fun (page, i) =>
        Date.Leaf.Fallback.Zstd.V2.decodePage limits bound group.selection.column.metadata
          group.entries.toArray page i) =
        ((group.data.zipIdx 1).mapM decode).mapError Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary := by
      apply mapM_errors
      intro entry member
      have inGroup : entry.1 ∈ group.data := by
        rw [← List.zipIdx_map_fst 1 group.data]
        exact List.mem_map_of_mem member
      simp [Date.Leaf.Fallback.Zstd.V2.decodePage, tags entry.1 inGroup, decode]
    simp only [Except.mapError, Bind.bind, Except.bind, Date.Leaf.Fallback.Zstd.V2.decodeGroup]
    rw [reads]
    cases (group.data.zipIdx 1).mapM decode <;> simp [Except.mapError, Pure.pure, Except.pure]

private theorem readDictionaryGroup_fallback {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames)
    (chosen : profile frames = .fallback) :
    readDictionaryGroup limits bound index = Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index := by
  simp only [readDictionaryGroup, Date.Leaf.Fallback.Zstd.V2.readGroup,
    checkDictionaryGroup_fallback_agrees original chosen]

theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (routed : route bound index = .ok .dictionaryBacked)
    (original : FramedGroup limits bound index frames) (chosen : profile frames = .dictionary) :
    readGroup limits bound index =
      ((Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index).mapError
        Date.Leaf.Fallback.Zstd.V2.GroupError.dictionary).mapError .dictionaryBacked := by
  rw [readGroup_backed routed, readDictionaryGroup_dictionary original chosen]

theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (routed : route bound index = .ok .dictionaryBacked)
    (original : FramedGroup limits bound index frames) (chosen : profile frames = .fallback) :
    readGroup limits bound index =
      (Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index).mapError .dictionaryBacked := by
  rw [readGroup_backed routed, readDictionaryGroup_fallback original chosen]

private theorem readDictionaryGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (routed : route bound index = .ok .dictionaryBacked)
    (read : readDictionaryGroup limits bound index = .ok slots) : GroupWire limits bound index slots := by
  have planned : ∃ checked, checkDictionaryGroup limits bound index = .ok checked := by
    unfold readDictionaryGroup at read
    obtain ⟨checked, accepted, _⟩ := bind_ok read
    exact ⟨checked, accepted⟩
  obtain ⟨checked, accepted⟩ := planned
  obtain ⟨wire, nonempty, phase⟩ := checkDictionaryGroup_wire accepted
  have dictionary := Date.Leaf.Dictionary.Zstd.V2.readEntries_wire wire.dictionary
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.selected, wire.frames⟩
  cases chosen : profile (checked.data.map (·.frame)) with
  | dictionary =>
    have admitted := mapError_ok ((checkDictionaryGroup_dictionary_agrees original chosen).symm.trans accepted)
    have decoded := mapError_ok ((readDictionaryGroup_dictionary original chosen).symm.trans read)
    obtain ⟨group, pages, same, _, _, _, physical, order, count⟩ :=
      Date.Leaf.Dictionary.Zstd.V2.readGroup_wire decoded
    cases Except.ok.inj (same.symm.trans admitted)
    exact .dictionaryBacked routed accepted wire dictionary nonempty phase
      (by simpa only [PagesWire, chosen] using physical) order count
  | fallback =>
    have admitted := (checkDictionaryGroup_fallback_agrees original chosen).symm.trans accepted
    have decoded := (readDictionaryGroup_fallback original chosen).symm.trans read
    obtain ⟨group, pages, same, _, _, physical, order, count⟩ :=
      Date.Leaf.Fallback.Zstd.V2.readGroup_wire decoded
    cases Except.ok.inj (same.symm.trans admitted)
    exact .dictionaryBacked routed accepted wire dictionary nonempty phase
      (by simpa only [PagesWire, chosen] using physical) order count

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots := by
  cases routed : route bound index with
  | error => rw [readGroup_routeError routed] at read; contradiction
  | ok selected =>
    cases selected with
    | plain =>
      have decoded := mapError_ok ((readGroup_plain_agrees routed).symm.trans read)
      obtain ⟨_, _, accepted, wire, physical, order, count⟩ := Date.Leaf.Zstd.V2.readGroup_wire decoded
      exact .plain routed accepted wire physical order count
    | dictionaryBacked =>
      exact readDictionaryGroup_wire routed (mapError_ok ((readGroup_backed routed).symm.trans read))

private theorem plain_of_success {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Zstd.V2.readGroup (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) bound index =
      .ok slots) : readGroup limits bound index = .ok slots := by
  obtain ⟨checked, _, accepted, wire, _, _, _⟩ := Date.Leaf.Zstd.V2.readGroup_wire read
  have routed : route bound index = .ok .plain := by
    cases present : checked.selection.column.metadata.dictionaryPageOffset.isSome with
    | false => simpa [present] using route_selected wire.selected
    | true =>
      simp only [Date.Leaf.Zstd.V2.checkGroup, Date.Leaf.Gzip.checkGroupFor, wire.selected,
        Except.mapError, Bind.bind, Except.bind, present, Bool.true_or] at accepted
      split at accepted <;> contradiction
  rw [readGroup_plain_agrees routed, read]
  rfl

private theorem backed_route {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (wire : Date.Leaf.Fallback.Zstd.V2.GroupWire limits bound index checked) :
    route bound index = .ok .dictionaryBacked := by
  simpa [wire.dictionaryOffset] using route_selected wire.selected

private theorem planned_tag {bound : Bound} {page : DictionaryChunk.DataPage}
    (planned : Date.Leaf.Fallback.Zstd.V2.planData bound page.frame = .ok page) :
    isPlainV2 page.frame = (page.params.encoding == 0) := by
  obtain ⟨_, header, kind, _, params⟩ := Date.Leaf.Fallback.Zstd.V2.planData_wire planned
  simp [isPlainV2, kind, params]

private theorem dictionary_of_success {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index = .ok slots) :
    readGroup limits bound index = .ok slots := by
  obtain ⟨checked, _, _, wire, _, tags, _, _, _⟩ := Date.Leaf.Dictionary.Zstd.V2.readGroup_wire read
  have routed : route bound index = .ok .dictionaryBacked := by
    simpa [wire.dictionaryOffset] using route_selected wire.selected
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.selected, wire.frames⟩
  have noPlain : (checked.data.map (·.frame)).any isPlainV2 = false := by
    apply List.any_eq_false.mpr
    intro frame member
    obtain ⟨page, inData, rfl⟩ := List.mem_map.mp member
    simp [planned_tag (dictionary_plan_data (wire.data page inData)), tags page inData]
  rw [readGroup_dictionary_agrees routed original (by simp [profile, noPlain]), read]
  rfl

private theorem fallback_of_success {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .ok slots) :
    readGroup limits bound index = .ok slots := by
  obtain ⟨checked, _, _, wire, phases, _, _, _⟩ := Date.Leaf.Fallback.Zstd.V2.readGroup_wire read
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.selected, wire.frames⟩
  obtain ⟨references, plain, order, _, hasPlain, _, tags⟩ := phases
  have seenPlain : (checked.data.map (·.frame)).any isPlainV2 = true := by
    cases plain with
    | nil => contradiction
    | cons page rest =>
      have member : page ∈ checked.data := by rw [order]; exact List.mem_append_right references List.mem_cons_self
      exact List.any_eq_true.mpr ⟨page.frame, List.mem_map_of_mem member, by
        simp [planned_tag (wire.data page member), tags page List.mem_cons_self]⟩
  rw [readGroup_fallback_agrees (backed_route wire) original (by simp [profile, seenPlain]), read]
  rfl

theorem readGroup_success_iff {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots} :
    readGroup limits bound index = .ok slots ↔
      Date.Leaf.Zstd.V2.readGroup (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) bound index = .ok slots ∨
      Date.Leaf.Dictionary.Zstd.V2.readGroup limits bound index = .ok slots ∨
      Date.Leaf.Fallback.Zstd.V2.readGroup limits bound index = .ok slots := by
  constructor
  · intro read
    cases readGroup_wire read with
    | plain routed =>
      exact .inl (mapError_ok ((readGroup_plain_agrees routed).symm.trans read))
    | @dictionaryBacked checked _ routed _ chunk =>
      have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
        ⟨checked.selection, checked.dictionary, chunk.selected, chunk.frames⟩
      cases chosen : profile (checked.data.map (·.frame)) with
      | dictionary =>
        exact .inr (.inl (mapError_ok (mapError_ok ((readGroup_dictionary_agrees routed original chosen).symm.trans read))))
      | fallback =>
        exact .inr (.inr (mapError_ok ((readGroup_fallback_agrees routed original chosen).symm.trans read)))
  · rintro (plain | dictionary | fallback)
    · exact plain_of_success plain
    · exact dictionary_of_success dictionary
    · exact fallback_of_success fallback

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

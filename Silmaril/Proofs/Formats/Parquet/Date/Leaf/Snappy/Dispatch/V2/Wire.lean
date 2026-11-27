module

public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

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
      (Date.Leaf.Snappy.V2.readGroup (plainLimits limits) bound index).mapError .plain := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

private theorem readGroup_backed {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .dictionaryBacked) :
    readGroup limits bound index = (readDictionaryGroup limits bound index).mapError .dictionaryBacked := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DictionaryChunk.DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, Date.Leaf.Dictionary.Snappy.V2.planData (profile frames) bound page.frame = .ok page) ∧
      Date.Leaf.Dictionary.Snappy.V2.Phase (profile frames) pages :=
  Date.Leaf.Dictionary.Snappy.V2.planPages_wire planned

private theorem framed_unique {limits : Limits} {bound : Bound} {index : Nat}
    {left right : List Page.Frame} (first : FramedGroup limits bound index left)
    (second : FramedGroup limits bound index right) : left = right := by
  obtain ⟨selected, dictionary, selectedOk, framed⟩ := first
  obtain ⟨other, leading, otherOk, otherFramed⟩ := second
  cases Except.ok.inj (selectedOk.symm.trans otherOk)
  exact (List.cons.inj (Except.ok.inj (framed.symm.trans otherFramed))).2

private theorem check_framed {limits : Limits} {bound : Bound} {index : Nat}
    {frames : List Page.Frame} (original : FramedGroup limits bound index frames) :
    checkDictionaryGroup limits bound index =
      Date.Leaf.Dictionary.Snappy.V2.checkGroup (profile frames) limits bound index := by
  obtain ⟨_, _, selected, framed⟩ := original
  have same := Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_agrees
    (codec := .snappy) (readDictionary := Date.Leaf.Dictionary.Snappy.readEntries limits)
    (wrap := Date.Leaf.Dictionary.Snappy.V2.GroupError.chunk)
    (otherWrap := Date.Leaf.Dictionary.Snappy.V2.GroupError.chunk) (lift := id)
    (plan := Date.Leaf.Dictionary.Snappy.V2.planPages (profile frames) bound) (otherPlan := planPages bound)
    selected framed (fun _ => rfl) (by
      unfold planPages
      cases Date.Leaf.Dictionary.Snappy.V2.planPages (profile frames) bound frames <;> rfl)
  change checkDictionaryGroup limits bound index =
    (Date.Leaf.Dictionary.Snappy.V2.checkGroup (profile frames) limits bound index).mapError id at same
  exact same.trans (by cases Date.Leaf.Dictionary.Snappy.V2.checkGroup (profile frames) limits bound index <;> rfl)

private theorem check_unframed {limits : Limits} {bound : Bound} {index : Nat} {choice : DictionaryProfile}
    (unframed : ¬ ∃ frames, FramedGroup limits bound index frames) :
    checkDictionaryGroup limits bound index = Date.Leaf.Dictionary.Snappy.V2.checkGroup choice limits bound index := by
  unfold checkDictionaryGroup Date.Leaf.Dictionary.Snappy.V2.checkGroup
    Date.Leaf.Dictionary.Snappy.checkGroupWith Date.Leaf.Dictionary.Snappy.checkGroupWithCodec
    Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary
  cases selected : selectChunk bound index with
  | error => simp [Except.mapError, Bind.bind, Except.bind]
  | ok selectedChunk =>
    cases framed : Page.readChunk limits.page bound.snapshot.bytes selectedChunk.span with
    | error => simp [framed, Except.mapError, Bind.bind, Except.bind]
    | ok chain =>
      cases chain with
      | nil => simp [framed, Except.mapError, Bind.bind, Except.bind]
      | cons dictionary frames => exact (unframed ⟨frames, selectedChunk, dictionary, selected, framed⟩).elim

theorem checkDictionaryGroup_agrees {limits : Limits} {bound : Bound} {index : Nat} {choice : DictionaryProfile}
    (chosen : ∀ frames, FramedGroup limits bound index frames → profile frames = choice) :
    checkDictionaryGroup limits bound index = Date.Leaf.Dictionary.Snappy.V2.checkGroup choice limits bound index := by
  by_cases framed : ∃ frames, FramedGroup limits bound index frames
  · obtain ⟨frames, original⟩ := framed
    rw [check_framed original, chosen frames original]
  · exact check_unframed framed

theorem readGroup_dictionaryBacked_agrees {limits : Limits} {bound : Bound} {index : Nat}
    {choice : DictionaryProfile} (routed : route bound index = .ok .dictionaryBacked)
    (chosen : ∀ frames, FramedGroup limits bound index frames → profile frames = choice) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Snappy.V2.readGroup choice limits bound index).mapError .dictionaryBacked := by
  rw [readGroup_backed routed]
  simp only [readDictionaryGroup, Date.Leaf.Dictionary.Snappy.V2.readGroup, checkDictionaryGroup_agrees chosen]

theorem readGroup_framed_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked) (original : FramedGroup limits bound index frames) :
    readGroup limits bound index =
      (Date.Leaf.Dictionary.Snappy.V2.readGroup (profile frames) limits bound index).mapError .dictionaryBacked :=
  readGroup_dictionaryBacked_agrees routed fun _ other => congrArg profile (framed_unique other original)

theorem checkDictionaryGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Date.Leaf.Dictionary.Snappy.CheckedGroup}
    (accepted : checkDictionaryGroup limits bound index = .ok checked) :
    FramedGroup limits bound index (checked.data.map (·.frame)) ∧
      Date.Leaf.Dictionary.Snappy.V2.GroupWire (profile (checked.data.map (·.frame))) limits bound index checked := by
  obtain ⟨wire, _⟩ := Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire
    (codec := .snappy) (admitted := fun _ => True) (valid := fun _ => True)
    (plan := planPages bound) (fun planned => ⟨(planPages_wire planned).1, fun _ _ => trivial, trivial⟩) accepted
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.selected, wire.frames⟩
  exact ⟨original, Date.Leaf.Dictionary.Snappy.V2.checkGroup_wire ((check_framed original).symm.trans accepted)⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) : GroupWire limits bound index slots := by
  cases routed : route bound index with
  | error => rw [readGroup_routeError routed] at read; contradiction
  | ok routeTag =>
    cases routeTag with
    | plain =>
      have strict := mapError_ok ((readGroup_plain_agrees routed).symm.trans read)
      exact .plain routed strict (Date.Leaf.Snappy.V2.readGroup_wire strict)
    | dictionaryBacked =>
      have readBacked := mapError_ok ((readGroup_backed routed).symm.trans read)
      cases accepted : checkDictionaryGroup limits bound index with
      | error => simp [readDictionaryGroup, accepted, Bind.bind, Except.bind] at readBacked
      | ok checked =>
        have original := (checkDictionaryGroup_wire accepted).1
        have strict := mapError_ok ((readGroup_framed_agrees routed original).symm.trans read)
        exact .dictionaryBacked routed original strict (Date.Leaf.Dictionary.Snappy.V2.readGroup_wire strict)

private theorem plain_of_success {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Snappy.V2.readGroup (plainLimits limits) bound index = .ok slots) :
    readGroup limits bound index = .ok slots := by
  obtain ⟨checked, _, accepted, wire, _, _, _⟩ := Date.Leaf.Snappy.V2.readGroup_wire read
  have routed : route bound index = .ok .plain := by
    cases present : checked.selection.column.metadata.dictionaryPageOffset.isSome with
    | false => simpa [present] using route_selected wire.1.selected
    | true =>
      simp only [Date.Leaf.Snappy.V2.checkGroup, Date.Leaf.Gzip.checkGroupFor, wire.1.selected,
        Except.mapError, Bind.bind, Except.bind, present, Bool.true_or] at accepted
      split at accepted <;> contradiction
  rw [readGroup_plain_agrees routed, read]
  rfl

private theorem planned_tag {choice : DictionaryProfile} {bound : Bound} {page : DictionaryChunk.DataPage}
    (planned : Date.Leaf.Dictionary.Snappy.V2.planData choice bound page.frame = .ok page) :
    isPlainV2 page.frame = (page.params.encoding == 0) := by
  obtain ⟨_, header, kind, _, params⟩ := Date.Leaf.Dictionary.Snappy.V2.planData_wire planned
  simp [isPlainV2, kind, params]

private theorem profile_of_phase {choice : DictionaryProfile} {bound : Bound} {pages : List DictionaryChunk.DataPage}
    (planned : ∀ page ∈ pages, Date.Leaf.Dictionary.Snappy.V2.planData choice bound page.frame = .ok page)
    (phase : Date.Leaf.Dictionary.Snappy.V2.Phase choice pages) :
    profile (pages.map (·.frame)) = choice := by
  cases choice with
  | dictionaryOnly =>
    have noPlain : (pages.map (·.frame)).any isPlainV2 = false := by
      apply List.any_eq_false.mpr
      intro frame member
      obtain ⟨page, inData, rfl⟩ := List.mem_map.mp member
      simp [planned_tag (planned page inData), phase page inData]
    simp [profile, noPlain]
  | fallback =>
    obtain ⟨references, plain, order, _, hasPlain, _, tags⟩ := phase
    have seenPlain : (pages.map (·.frame)).any isPlainV2 = true := by
      cases plain with
      | nil => contradiction
      | cons page rest =>
        have member : page ∈ pages := by rw [order]; exact List.mem_append_right references List.mem_cons_self
        exact List.any_eq_true.mpr ⟨page.frame, List.mem_map_of_mem member, by
          simp [planned_tag (planned page member), tags page List.mem_cons_self]⟩
    simp [profile, seenPlain]

private theorem backed_of_success {choice : DictionaryProfile} {limits : Limits} {bound : Bound}
    {index : Nat} {slots : Slots} (read : Date.Leaf.Dictionary.Snappy.V2.readGroup choice limits bound index = .ok slots) :
    readGroup limits bound index = .ok slots := by
  obtain ⟨checked, _, _, wire, _, _, _, _⟩ := Date.Leaf.Dictionary.Snappy.V2.readGroup_wire read
  have routed : route bound index = .ok .dictionaryBacked := by
    simpa [wire.1.dictionaryOffset] using route_selected wire.1.selected
  have original : FramedGroup limits bound index (checked.data.map (·.frame)) :=
    ⟨checked.selection, checked.dictionary, wire.1.selected, wire.1.frames⟩
  rw [readGroup_framed_agrees routed original, profile_of_phase wire.1.data wire.2.2, read]
  rfl

theorem readGroup_success_iff {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots} :
    readGroup limits bound index = .ok slots ↔
      Date.Leaf.Snappy.V2.readGroup (plainLimits limits) bound index = .ok slots ∨
      Date.Leaf.Dictionary.Snappy.V2.readGroup .dictionaryOnly limits bound index = .ok slots ∨
      Date.Leaf.Dictionary.Snappy.V2.readGroup .fallback limits bound index = .ok slots := by
  constructor
  · intro read
    cases readGroup_wire read with
    | plain _ strict _ => exact .inl strict
    | @dictionaryBacked frames _ _ strict _ =>
      cases selected : profile frames with
      | dictionaryOnly => exact .inr (.inl (by simpa only [selected] using strict))
      | fallback => exact .inr (.inr (by simpa only [selected] using strict))
  · rintro (plain | dictionary | fallback)
    · exact plain_of_success plain
    · exact backed_of_success dictionary
    · exact backed_of_success fallback

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

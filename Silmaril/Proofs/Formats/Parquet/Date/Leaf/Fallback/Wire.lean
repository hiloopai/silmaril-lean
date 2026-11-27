module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.TakeWhile

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback

open Silmaril.Formats Parquet Date.Leaf Date.Leaf.Fallback
open Silmaril.Formats.Parquet.DictionaryChunk (DataPage)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem checkSequence_wire {data : List DataPage} (checked : checkSequence data = .ok ()) :
    Ordered data := by
  cases data with
  | nil => contradiction
  | cons first rest =>
    simp only [checkSequence] at checked
    split at checked
    · contradiction
    rename_i firstIsReference
    let data := first :: rest
    let referencePages := data.takeWhile isReference
    let suffix := data.dropWhile isReference
    let start := data.length - suffix.length + 1
    change (if suffix.isEmpty then Except.error _ else
      match (suffix.zipIdx start).find? (fun (page, _) => page.params.encoding != 0) with
      | none => .ok ()
      | some (page, index) => .error _) = .ok () at checked
    split at checked
    · contradiction
    rename_i nonempty
    split at checked
    · rename_i found
      have firstOk : isReference first = true := by simpa using firstIsReference
      have before : referencePages ≠ [] := by simp [referencePages, data, firstOk]
      refine ⟨referencePages, suffix, List.takeWhile_append_dropWhile.symm, before,
        fun empty => nonempty (List.isEmpty_iff.mpr empty), ?_, ?_⟩
      · intro page member
        simpa only [isReference, beq_iff_eq] using List.mem_takeWhile_imp member
      · intro page member
        have inMap : page ∈ (suffix.zipIdx start).map Prod.fst := by
          simpa only [List.zipIdx_map_fst] using member
        obtain ⟨⟨item, ordinal⟩, zipped, rfl⟩ := List.mem_map.mp inMap
        simpa using List.find?_eq_none.mp found (item, ordinal) zipped
    · contradiction

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : Dictionary.CheckedGroup} (read : checkGroup limits bound index = .ok checked) :
    Dictionary.GroupWire limits bound index checked ∧ Ordered checked.chunk.data := by
  cases leading : Dictionary.checkGroup limits bound index with
  | error cause => simp [checkGroup, leading, Except.mapError, Bind.bind, Except.bind] at read
  | ok group =>
    cases sequence : checkSequence group.chunk.data with
    | error cause => simp [checkGroup, leading, sequence, Except.mapError, Bind.bind, Except.bind] at read
    | ok result =>
      have same : group = checked := by
        simpa [checkGroup, leading, sequence, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using read
      subst checked
      exact ⟨Dictionary.checkGroup_exact leading, checkSequence_wire sequence⟩

theorem decodePage_wire {limits : Limits} {bound : Bound} {dictionary : DictionaryChunk.Dictionary}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits bound dictionary page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes dictionary page slots := by
  by_cases plain : page.params.encoding = 0
  · have decoded := mapError_ok (by simpa only [decodePage, plain, ite_true] using read)
    exact ⟨(ScalarPage.decode_counts decoded).1, .inr ⟨plain, decoded⟩⟩
  · have decoded := mapError_ok (by simpa only [decodePage, plain, ite_false] using read)
    have wire := Dictionary.decodePage_wire decoded
    exact ⟨(DictionaryIndex.decode_counts wire.2).1, .inl wire⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Fallback.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Dictionary.GroupWire limits bound index checked ∧ Ordered checked.chunk.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.dictionary) checked.chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  cases planned : checkGroup limits bound index with
  | error cause => simp [Fallback.readGroup, planned, Bind.bind, Except.bind] at read
  | ok checked =>
    let decode := fun (entry : DataPage × Nat) => decodePage limits bound checked.dictionary entry.1 entry.2
    cases decoded : (checked.chunk.data.zipIdx 1).mapM decode with
    | error cause =>
      simp [Fallback.readGroup, planned, decode, decoded, Bind.bind, Except.bind] at read
    | ok pages =>
      have same : pages.flatten = slots := by
        simpa [Fallback.readGroup, planned, decode, decoded, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using read
      have zipped := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp (fun _ _ h => decodePage_wire h)
      have ordered : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.dictionary)
          checked.chunk.data pages := by
        simpa using List.forall₂_map_left_iff.mpr zipped
      have profile := checkGroup_wire planned
      have sizes : pages.map List.length = checked.chunk.data.map (·.params.numValues) := by
        clear read decoded zipped same
        generalize checked.chunk.data = data at ordered ⊢
        induction ordered with
        | nil => rfl
        | cons first _ rest => exact congrArg₂ List.cons first.1 rest
      refine ⟨checked, pages, rfl, profile.1, profile.2, ordered, same.symm, ?_⟩
      rw [← same, List.length_flatten, sizes, profile.1.admitted.slots]

theorem plainWire_exact {limits : Limits} {source : Bytes} {page : DataPage} {slots : Slots}
    (decoded : ScalarPage.decode .int32 page.params limits.scalar
      (DictionaryChunk.body source page.frame) = .ok slots) :
    let body := DictionaryChunk.body source page.frame
    ∃ layout prepared words, ScalarPage.validate page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨prepared, words, preparation, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepare_sound preparation
  exact ⟨layout, prepared, words, valid, wire, plain, mask, ordered⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : Dictionary.CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.chunk.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.dictionary item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.dictionary page ordinal = .error cause) :
    Fallback.readGroup limits bound index = .error cause := by
  simp [Fallback.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

private theorem prefix_wire {ε δ : Type} {plan : Page.Frame → Except ε DataPage}
    {atFrame : Nat → Page.Frame → ε → δ}
    (keeps : ∀ {frame page}, plan frame = .ok page → page.frame = frame) {indexed : List (Page.Frame × Nat)} {pages : List DataPage}
    (accepted : planPrefixWith plan atFrame indexed = (pages, none)) :
    pages.map (·.frame) = indexed.map Prod.fst ∧
      ∀ page ∈ pages, plan page.frame = .ok page := by
  induction indexed generalizing pages with
  | nil =>
    simp [planPrefixWith] at accepted
    subst pages
    simp
  | cons item rest ih =>
    obtain ⟨frame, ordinal⟩ := item
    cases planned : plan frame with
    | error cause => simp [planPrefixWith, planned] at accepted
    | ok page =>
      cases tailEq : planPrefixWith plan atFrame rest with
      | mk tail failure =>
        simp [planPrefixWith, planned, tailEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        obtain ⟨order, reads⟩ := ih tailEq
        have original := keeps planned
        refine ⟨by simp [original, order], ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with rfl | later
        · rwa [original]
        · exact reads candidate later

theorem planPrefixWith_firstError {ε δ : Type} {plan : Page.Frame → Except ε DataPage}
    {atFrame : Nat → Page.Frame → ε → δ} {before after : List (Page.Frame × Nat)}
    {frame : Page.Frame} {ordinal : Nat} {pages : List DataPage}
    {cause : ε}
    (earlier : before.mapM
      (fun entry => plan entry.1) = .ok pages)
    (failed : plan frame = .error cause) :
    planPrefixWith plan atFrame (before ++ (frame, ordinal) :: after) =
      (pages, some (atFrame ordinal frame cause)) := by
  induction before generalizing pages with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst pages
    simp [planPrefixWith, failed]
  | cons item rest ih =>
    obtain ⟨page, position⟩ := item
    cases planned : plan page with
    | error error => simp [List.mapM_cons, planned, Bind.bind, Except.bind] at earlier
    | ok first =>
      cases tail : rest.mapM
          (fun entry => plan entry.1) with
      | error error => simp [List.mapM_cons, planned, tail, Bind.bind, Except.bind] at earlier
      | ok following =>
        have same : first :: following = pages := by
          simpa [List.mapM_cons, planned, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using earlier
        subst pages
        simp [planPrefixWith, planned, ih tail]

theorem planPagesWith_earlierPhaseError {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option δ} {ordinal offset : Nat} {tag : Int}
    (scanned : planPrefixWith plan atFrame (frames.zipIdx 1) = (pages, failure)) :
    (checkSequence pages = .error (.prefixEncoding ordinal offset tag) →
      planPagesWith plan atFrame headerError phaseError frames = .error (phaseError (.prefixEncoding ordinal offset tag))) ∧
    (checkSequence pages = .error (.suffixEncoding ordinal offset tag) →
      planPagesWith plan atFrame headerError phaseError frames = .error (phaseError (.suffixEncoding ordinal offset tag))) := by
  constructor <;> intro phase <;> simp [planPagesWith, scanned, phase]

theorem planPagesWith_headerError {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε} {frames : List Page.Frame} {pages : List DataPage}
    {cause : δ}
    (scanned : planPrefixWith plan atFrame (frames.zipIdx 1) = (pages, some cause))
    (phase : checkSequence pages = .ok () ∨
      checkSequence pages = .error .missingReferences ∨
      checkSequence pages = .error .missingPlain) :
    planPagesWith plan atFrame headerError phaseError frames = .error (headerError cause) := by
  rcases phase with h | h | h <;> simp [planPagesWith, scanned, h]

theorem planPagesWith_wire {ε δ εPage : Type}
    {plan : Page.Frame → Except εPage DataPage} {atFrame : Nat → Page.Frame → εPage → δ}
    {headerError : δ → ε} {phaseError : GroupError → ε}
    (keeps : ∀ {frame page}, plan frame = .ok page → page.frame = frame) {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPagesWith plan atFrame headerError phaseError frames = .ok pages) :
    pages.map (·.frame) = frames ∧
      (∀ page ∈ pages, plan page.frame = .ok page) ∧
      Ordered pages := by
  cases original : planPrefixWith plan atFrame (frames.zipIdx 1) with
  | mk preceding failure =>
    cases sequence : checkSequence preceding with
    | error cause =>
      cases cause <;> cases failure <;>
        simp [planPagesWith, original, sequence, Except.map, Except.mapError] at planned
    | ok value =>
      cases failure with
      | some cause => simp [planPagesWith, original, sequence] at planned
      | none =>
        have same : preceding = pages := by
          simpa [planPagesWith, original, sequence, Except.map, Except.mapError] using planned
        subst pages
        obtain ⟨order, headers⟩ := prefix_wire keeps original
        exact ⟨by simpa using order, headers, checkSequence_wire sequence⟩

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback

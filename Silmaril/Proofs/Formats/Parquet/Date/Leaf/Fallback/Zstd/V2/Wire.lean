module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2
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
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
        (Date.Leaf.Zstd.columnLayout bound).levels, header.numValues, Payload.Codec.zstd.id,
        header.encoding,
        .v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i tag
    simp [FlatColumn.pageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, header, rfl, by tauto, rfl⟩
  | dictionary _ | dataV1 _ | skipped _ => simp [planData, kind] at planned

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Date.Leaf.Fallback.planPagesWith_wire (fun planned => (planData_wire planned).1) planned

private theorem sequence_reentry {references plain after : List DataPage} {reentry : DataPage}
    (hasReferences : references ≠ []) (hasPlain : plain ≠ [])
    (referencesOnly : ∀ page ∈ references, page.params.encoding = 8)
    (plainOnly : ∀ page ∈ plain, page.params.encoding = 0)
    (tag : reentry.params.encoding = 8) :
    Date.Leaf.Fallback.checkSequence (references ++ plain ++ reentry :: after) =
      .error (.suffixEncoding (references.length + plain.length + 1) reentry.frame.header.start 8) := by
  have skip : ∀ page ∈ references, Date.Leaf.Fallback.isReference page = true := by
    intro page member
    simp [Date.Leaf.Fallback.isReference, referencesOnly page member]
  have firstPlain : (plain ++ reentry :: after).dropWhile Date.Leaf.Fallback.isReference =
      plain ++ reentry :: after := by
    cases plain with
    | nil => contradiction
    | cons first rest =>
      simp [Date.Leaf.Fallback.isReference, plainOnly first List.mem_cons_self]
  have allPlain (start : Nat) :
      (plain.zipIdx start).find? (fun entry => entry.1.params.encoding != 0) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    have inPlain : entry.1 ∈ plain := by
      rw [← List.zipIdx_map_fst start plain]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    simp [plainOnly entry.1 inPlain]
  cases references with
  | nil => contradiction
  | cons first rest =>
    have firstRef := skip first List.mem_cons_self
    have dropped : (rest ++ (plain ++ reentry :: after)).dropWhile Date.Leaf.Fallback.isReference =
        plain ++ reentry :: after := by
      rw [List.dropWhile_append_of_pos (fun page member => skip page (List.mem_cons_of_mem _ member)), firstPlain]
    simp [Date.Leaf.Fallback.checkSequence, firstRef, dropped, List.zipIdx_append, allPlain,
      List.zipIdx_cons, tag, Nat.add_comm, Nat.add_left_comm]
    change Except.error _ = Except.error _
    congr 2
    omega

theorem planPages_reentry {bound : Bound} {frames : List Page.Frame} {references plain after : List DataPage}
    {reentry : DataPage} {failure : Option GroupError}
    (scanned : Date.Leaf.Fallback.planPrefixWith (planData bound)
      (fun ordinal frame => GroupError.header ordinal frame.header.start) (frames.zipIdx 1) =
      (references ++ plain ++ reentry :: after, failure))
    (hasReferences : references ≠ []) (hasPlain : plain ≠ [])
    (referencesOnly : ∀ page ∈ references, page.params.encoding = 8)
    (plainOnly : ∀ page ∈ plain, page.params.encoding = 0) (tag : reentry.params.encoding = 8) :
    planPages bound frames =
      .error (.sequence (.suffixEncoding (references.length + plain.length + 1) reentry.frame.header.start 8)) :=
  (Date.Leaf.Fallback.planPagesWith_earlierPhaseError (headerError := id) (phaseError := GroupError.sequence)
    scanned).2 (sequence_reentry hasReferences hasPlain referencesOnly plainOnly tag)

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked ∧ Date.Leaf.Fallback.Ordered checked.data :=
  Date.Leaf.Dictionary.Snappy.checkGroupWithDictionary_wire planPages_wire accepted

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

theorem decodePage_wire {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits bound metadata entries page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes entries page slots := by
  obtain ⟨_, header, kind, tags, params⟩ := planData_wire planned
  by_cases plain : page.params.encoding = 0
  · have tag : header.encoding = 0 := by simpa [params] using plain
    have admitted : Date.Leaf.Zstd.V2.planData bound page.frame ordinal = .ok ⟨page.frame, page.params⟩ := by
      simp [Date.Leaf.Zstd.V2.planData, kind, tag, FlatColumn.pageParameters, params, Pure.pure, Except.pure]
    have physical := mapError_ok (by simpa only [decodePage, ite_eq_left plain] using decoded)
    have read : Date.Leaf.Zstd.V2.decodePage (Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits)
        bound metadata ⟨page.frame, page.params⟩ ordinal = .ok slots := by
      simp [Date.Leaf.Zstd.V2.decodePage, physical, Except.mapError]
    exact .plain plain (Date.Leaf.Zstd.V2.decodePage_wire admitted read)
  · have tag : header.encoding = 8 := tags.resolve_right (fun tag => plain (by simp [params, tag]))
    have admitted : Date.Leaf.Dictionary.Zstd.V2.planData bound page.frame = .ok page := by
      cases page
      simp at params kind
      simp [Date.Leaf.Dictionary.Zstd.V2.planData, kind, tag, FlatColumn.pageParameters, params,
        Pure.pure, Except.pure]
    have read := mapError_ok (by simpa only [decodePage, ite_eq_right plain] using decoded)
    exact .reference (by simp [params, tag]) (Date.Leaf.Dictionary.Zstd.V2.decodePage_wire admitted read)

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  unfold decodeGroup at read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨wire, phases⟩ := checkGroup_wire planned
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages := by
    have zipped := List.mapM_eq_ok_iff_forall₂.mp decoded
    have raw : List.Forall₂ (fun page out => ∃ ordinal,
        decodePage limits bound checked.selection.column.metadata checked.entries.toArray page ordinal = .ok out)
        checked.data pages := by
      rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
      exact zipped.imp fun entry _ read => ⟨entry.2, read⟩
    have admitted := wire.data
    clear wire phases zipped decoded planned read
    generalize checked.data = data at admitted raw ⊢
    induction raw with
    | nil => exact .nil
    | cons head _ ih =>
      obtain ⟨_, decoded⟩ := head
      exact .cons (decodePage_wire (admitted _ List.mem_cons_self) decoded)
        (ih fun page member => admitted page (List.mem_cons_of_mem _ member))
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail =>
      have headCount := by cases head with
        | reference _ ref => exact ref.count
        | plain _ plain => exact plain.count
      exact congrArg₂ List.cons headCount tail
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, phases, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound checked.selection.column.metadata checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound checked.selection.column.metadata checked.entries.toArray page ordinal = .error cause) :
    readGroup limits bound index = .error cause := by
  simp [readGroup, decodeGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

theorem decodePage_checksum_error {limits : Limits} {bound : Bound} {metadata : Footer.ColumnMetadata}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes bound.snapshot.bytes page.frame = .error cause) :
    decodePage limits bound metadata entries page ordinal =
      .error (if page.params.encoding = 0 then .plain (.checksum ordinal page.frame.header.start cause)
        else .dictionary (.chunk (Date.Leaf.Dictionary.Snappy.atFrame ordinal page.frame (.checksum cause)))) := by
  by_cases plain : page.params.encoding = 0
  · have crc := Date.Leaf.Zstd.decodePage_checksum_error
        (limits := Date.Leaf.Dictionary.Zstd.V2.scalarLimits limits) (bound := bound) (metadata := metadata)
        (page := ⟨page.frame, page.params⟩) (ordinal := ordinal) failed
    simp [decodePage, plain, crc, Except.mapError]
  · simp [decodePage, plain, Date.Leaf.Dictionary.Zstd.V2.decodePage_checksum_error failed, Except.mapError]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2

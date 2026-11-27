module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Defs
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy (Limits CheckedGroup)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2
open DictionaryChunk (DataPage)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {profile : Profile} {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData profile bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ profile.admits header.encoding = true ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues,
          Payload.Codec.snappy.id, header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    have inner : Date.Leaf.Dictionary.Snappy.planDataWith profile.admits bound frame = .ok page :=
      mapError_ok (wrap := HeaderError.data) (by simpa only [planData, kind] using planned)
    obtain ⟨same, tag, base, original, params⟩ := Date.Leaf.Dictionary.Snappy.planDataWith_wire inner
    simp [FlatScan.int32PageParameters, kind] at original
    subst base
    exact ⟨same, header, rfl, by simpa [params] using tag, by simpa using params⟩
  | dictionary _ | dataV1 _ | skipped _ => simp [planData, kind] at planned

theorem planData_rejectV1 {profile : Profile} {bound : Bound} {frame : Page.Frame} {header : Page.DataV1}
    (kind : frame.value.kind = .dataV1 header) :
    planData profile bound frame = .error .expectedV2 := by
  simp [planData, kind]

private theorem dictionary_plan {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages .dictionaryOnly bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ ∀ page ∈ pages, planData .dictionaryOnly bound page.frame = .ok page := by
  unfold planPages at planned
  have indexed := (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun _ _ read =>
    mapError_ok read
  have paired : List.Forall₂ (fun frame page => planData .dictionaryOnly bound frame = .ok page) frames pages := by
    rw [← List.zipIdx_map_fst 1 frames, List.forall₂_map_left_iff]
    exact indexed
  clear planned indexed
  induction paired with
  | nil => simp
  | cons head _ ih =>
    have same := (planData_wire head).1
    constructor
    · simp [same, ih.1]
    · intro page member
      rcases List.mem_cons.mp member with rfl | rest
      · rwa [same]
      · exact ih.2 page rest

theorem planPages_wire {profile : Profile} {bound : Bound} {frames : List Page.Frame}
    {pages : List DataPage} (planned : planPages profile bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData profile bound page.frame = .ok page) ∧
      Phase profile pages := by
  cases profile with
  | dictionaryOnly =>
    obtain ⟨frames, headers⟩ := dictionary_plan planned
    refine ⟨frames, headers, ?_⟩
    intro page member
    obtain ⟨_, _, _, tag, params⟩ := planData_wire (headers page member)
    simpa [Profile.admits, params] using tag
  | fallback =>
    exact Date.Leaf.Fallback.planPagesWith_wire (fun read => (planData_wire read).1) planned

theorem planPages_dictionaryFirstError {bound : Bound} {frames : List Page.Frame}
    {before after : List (Page.Frame × Nat)} {frame : Page.Frame} {ordinal : Nat}
    {pages : List DataPage} {cause : HeaderError}
    (split : frames.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => (planData .dictionaryOnly bound item).mapError (atHeader i item)) =
      .ok pages)
    (failed : planData .dictionaryOnly bound frame = .error cause) :
    planPages .dictionaryOnly bound frames = .error (atHeader ordinal frame cause) := by
  unfold planPages
  rw [split, List.mapM_append, earlier]
  simp [failed, Bind.bind, Except.bind, Except.mapError]

theorem planPages_fallbackReentry {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    {failure : Option GroupError} {ordinal offset : Nat} {tag : Int}
    (scanned : Date.Leaf.Fallback.planPrefixWith (planData .fallback bound) atHeader (frames.zipIdx 1) =
      (pages, failure))
    (reentry : Date.Leaf.Fallback.checkSequence pages = .error (.suffixEncoding ordinal offset tag)) :
    planPages .fallback bound frames = .error (.sequence (.suffixEncoding ordinal offset tag)) :=
  (Date.Leaf.Fallback.planPagesWith_earlierPhaseError scanned (headerError := id)
    (phaseError := GroupError.sequence)).2 reentry

theorem checkGroup_wire {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (admitted : checkGroup profile limits bound index = .ok checked) :
    GroupWire profile limits bound index checked := by
  obtain ⟨wire, phase⟩ := Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire
    (codec := .snappy) (plan := planPages profile bound) (fun read => planPages_wire read) admitted
  refine ⟨wire, ?_, phase⟩
  intro empty
  have offset := wire.dataOffset
  simp [empty] at offset

theorem checkGroup_dictionary {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (admitted : checkGroup profile limits bound index = .ok checked) :
    DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries := by
  have group := checkGroup_wire admitted
  obtain ⟨header, status, expanded, kind, tag, entriesCap, verified, payload, expandedSize, expandedCap,
    entries, count⟩ := Date.Leaf.Dictionary.Snappy.readEntries_wire group.1.dictionary
  obtain ⟨slice, storedLength, storedCap, crc⟩ := Date.Leaf.Dictionary.Snappy.stored_verified verified
  exact ⟨header, status, expanded, kind, tag, entriesCap, verified, slice, storedLength, storedCap,
    by cases status <;> exact crc, payload, expandedSize, expandedCap, entries, count⟩

theorem decodePage_agrees {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} :
    decodePage limits source entries page ordinal =
      (Date.Leaf.Fallback.Snappy.decodePage limits source entries page ordinal).mapError .decode :=
  rfl

private theorem prepared_exact {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {slots : Slots}
    (wire : Date.Leaf.Fallback.Snappy.PageWire limits source entries page slots) :
    let stored := Page.Checksum.payloadBytes source page.frame
    ∃ status layout prepared,
      Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params limits.scalar layout stored prepared ∧
      ValuesWire page.params.encoding entries prepared slots ∧ slots.map Option.isSome = prepared.mask ∧
      slots.length = page.params.numValues ∧
      match page.params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (slots.filterMap id).length = page.params.numValues - nulls := by
  rcases wire.2 with ⟨tag, reference⟩ | ⟨tag, status, verified, scalar⟩
  · obtain ⟨status, layout, prepared, width, runs, indices, verified, expanded, prep, split, widthCap,
      hybrid, mask, values, count⟩ := Date.Leaf.Dictionary.Snappy.pageWire_exact reference
    obtain ⟨_, _, decoded⟩ := reference
    exact ⟨status, layout, prepared, verified, expanded, prep,
      .inl ⟨tag, width, runs, indices, split, widthCap, hybrid, values⟩, mask, count,
      (DictionaryIndex.decode_counts decoded).2⟩
  · obtain ⟨prepared, words, prep, decoded, mask, ordered, _, _⟩ := ScalarPage.decode_sound scalar
    obtain ⟨layout, valid, body⟩ := ScalarPage.prepare_sound prep
    exact ⟨status, layout, prepared, verified, Date.Leaf.Gzip.expanded_bound valid, body,
      .inr ⟨tag, ordered ▸ decoded⟩, mask, wire.1, (ScalarPage.decode_counts scalar).2⟩

theorem decodePage_wire {profile : Profile} {limits : Limits} {bound : Bound} {source : Bytes}
    {entries : Array Int32} {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData profile bound page.frame = .ok page)
    (read : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  obtain ⟨_, header, kind, selected, params⟩ := planData_wire planned
  have tag : Date.Leaf.Fallback.Snappy.admits page.params.encoding = true := by
    cases profile with
    | dictionaryOnly =>
      have ref : header.encoding = 8 := by simpa [Profile.admits] using selected
      simp [params, ref, Date.Leaf.Fallback.Snappy.admits]
    | fallback => simpa [params, Profile.admits] using selected
  have old := Date.Leaf.Fallback.Snappy.decodePage_wire tag (mapError_ok read)
  obtain ⟨status, layout, prepared, verified, expanded, body, values, mask, length, present⟩ :=
    prepared_exact old
  obtain ⟨slice, storedLength, storedCap, crc⟩ := Date.Leaf.Dictionary.Snappy.stored_verified verified
  simp only [params, ScalarPage.PreparedWire] at body
  simp only [params] at expanded values length present
  obtain ⟨nulls, rows, repetitions, defStored, defExpanded, defCap, levels, suffix,
    levelsLength, split, readMask, _, payload⟩ := body
  refine ⟨by simpa only [params] using length, ?_⟩
  refine ⟨header, status, layout, levels, suffix, prepared, kind, verified, slice, storedLength, storedCap,
    expanded, by cases status <;> exact crc, rows, repetitions, defStored, defExpanded, defCap,
    levelsLength, split, readMask, ?_, values, mask, length, by omega⟩
  simpa [ScalarPage.v2Codec] using payload

theorem readGroup_wire {profile : Profile} {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup profile limits bound index = .ok slots) : SlotsWire profile limits bound index slots := by
  obtain ⟨checked, admitted, decoded⟩ := bind_ok read
  obtain ⟨pages, pagesRead, result⟩ := bind_ok decoded
  have group := checkGroup_wire admitted
  have zipped := List.mapM_eq_ok_iff_forall₂.mp pagesRead
  have paired : List.Forall₂ (fun page slots =>
      ∃ ordinal, decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .ok slots)
      checked.data pages := by
    rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
    exact zipped.imp fun x _ read => ⟨x.2, read⟩
  have complete : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray)
        checked.data pages ∧ pages.map List.length = checked.data.map (·.params.numValues) := by
    have plans := group.1.data
    clear zipped pagesRead result group admitted decoded read
    generalize checked.data = data at paired plans ⊢
    induction paired with
    | nil => exact ⟨.nil, rfl⟩
    | cons first _ ih =>
      obtain ⟨_, read⟩ := first
      have plan := plans _ List.mem_cons_self
      have wire := decodePage_wire plan read
      obtain ⟨tail, count⟩ := ih (fun page member => plans page (List.mem_cons_of_mem _ member))
      exact ⟨.cons wire tail, congrArg₂ List.cons wire.1 count⟩
  have same := (Except.ok.inj result).symm
  exact ⟨checked, pages, admitted, group, checkGroup_dictionary admitted, complete.1, same, by
    rw [same, List.length_flatten, complete.2, group.1.rows]⟩

theorem readGroup_firstPageError {profile : Profile} {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup profile limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    readGroup profile limits bound index = .error cause := by
  simp [readGroup, decodeGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2

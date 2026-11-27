module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs

open Silmaril.Formats Parquet Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf hiding Limits readGroup
open Leaf.ScalarAndDictionary (Limits)
open Leaf.ScalarAndDictionary.WithV1.AllCodecs
open Silmaril.Numeric.Timestamp (Ticks)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {codec : Codec} {fallback : Bool} {bound : Bound} {frame : Parquet.Page.Frame}
    {page : Dictionary.DataPage} (read : planData codec fallback bound frame = .ok page) :
    PlanWire codec fallback bound frame page := by
  cases kind : frame.value.kind with
  | dataV1 header =>
    by_cases tag : admits fallback header.encoding = true
    · simp only [planData, kind, tag, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at read
      obtain ⟨params, parsed, read⟩ := bind_ok read
      cases Except.ok.inj read
      have fields := mapError_ok parsed
      unfold Timestamp.Page.parameters at fields
      split at fields
      · simp only [kind, Except.ok.injEq] at fields
        exact ⟨rfl, header, kind, tag, fields.symm⟩
      · contradiction
    · simp [planData, kind, tag, Bind.bind, Except.bind] at read
  | dataV2 _ | dictionary _ | skipped _ => simp [planData, kind, Bind.bind, Except.bind] at read

private theorem stored_wire {cap : Nat} {bound : Bound} {frame : Parquet.Page.Frame}
    {status : Parquet.Page.Checksum.Status}
    (verified : Parquet.Page.Checksum.verify cap bound.snapshot.bytes frame = .ok status) :
    StoredWire cap bound frame status := by
  cases status <;> exact Dictionary.Snappy.stored_verified verified

private theorem readEntries_wire {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : codec.readEntries limits leafLimits bound frame = .ok entries) :
    EntriesWire codec limits leafLimits bound frame entries := by
  cases codec with
  | zstd => exact Dictionary.Zstd.V2.readEntries_wire read
  | uncompressed =>
    have decoded := mapError_ok read
    obtain ⟨header, status, expanded, kind, tag, cap, crc, payload, size, outputCap, values, count⟩ :=
      Dictionary.Snappy.readEntriesWithCodec_wire decoded
    cases payload
    exact ⟨header, status, kind, tag, cap, stored_wire crc,
      by simpa using size, by simpa using outputCap, by simpa using values, count⟩

private theorem prepare_wire {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {params : ScalarPage.Parameters} {body : Bytes} {prepared : ScalarPage.Prepared}
    {definitions repetitions : Int} (version : params.version = .v1 definitions repetitions)
    (read : codec.prepare limits leafLimits params body = .ok prepared) :
    PreparedWire codec limits leafLimits params body prepared ∧ prepared.mask.length = params.numValues := by
  cases codec with
  | uncompressed =>
    have decoded := mapError_ok read
    obtain ⟨layout, admitted, wire⟩ := ScalarPage.prepareFor_sound decoded
    exact ⟨⟨layout, admitted, wire⟩, (ScalarPage.preparedFor_counts decoded).1⟩
  | zstd =>
    obtain ⟨_, layout, admitted, _, _, _, wire⟩ := FlatColumn.Zstd.prepareFor_sound read
    have slices := wire
    rw [FlatColumn.Zstd.PreparedWire, version] at slices
    obtain ⟨_, _, _, _, _, _, mask, _⟩ := slices
    exact ⟨⟨layout, admitted, wire⟩, FlatPage.readMask_length mask⟩

theorem decodePage_wire {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {frame : Parquet.Page.Frame} {entries : Array Int64} {page : Dictionary.DataPage}
    {ordinal : Nat} {slots : List (Option Int64)}
    (planned : PlanWire codec fallback bound frame page)
    (read : decodePage codec limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire codec limits leafLimits bound entries page slots := by
  obtain ⟨_, header, _, _, params⟩ := planned
  unfold decodePage at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨prepared, preparedOk, read⟩ := bind_ok read
  obtain ⟨wire, count⟩ := prepare_wire (by rw [params]) (mapError_ok preparedOk)
  refine ⟨status, prepared, stored_wire (mapError_ok verified), wire, ?_⟩
  by_cases plain : page.params.encoding = 0
  · simp only [plain, ↓reduceIte] at read ⊢
    obtain ⟨values, decoded, restored⟩ := bind_ok read
    obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok restored)
    exact ⟨mask, by simpa only [List.length_map, count] using congrArg List.length mask,
      ordered ▸ mapError_ok decoded⟩
  · simp only [plain, ↓reduceIte] at read ⊢
    have refs := mapError_ok read
    unfold Dictionary.Zstd.V2.decodeReferences at refs
    obtain ⟨indices, indexOk, refs⟩ := bind_ok refs
    obtain ⟨values, selected, restored⟩ := bind_ok refs
    obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok restored)
    exact ⟨mask, by simpa only [List.length_map, count] using congrArg List.length mask,
      indices, indexOk, ordered ▸ DictionaryIndex.select_ok_iff.mp selected⟩

theorem decodePage_checksum_error {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : Dictionary.DataPage} {ordinal : Nat}
    {cause : Parquet.Page.Checksum.Error}
    (failed : Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame =
      .error cause) :
    decodePage codec limits leafLimits bound entries page ordinal =
      .error (.checksum ordinal page.frame.header.start cause) := by
  simp [decodePage, failed, Except.mapError, Bind.bind, Except.bind]

private theorem checkFramed_wire {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {framed : Dictionary.FramedChunk} {checked : Dictionary.CheckedChunk}
    (read : checkFramed codec fallback limits leafLimits bound framed = .ok checked) :
    codec.expansionLimit limits framed ∧ checked.chunk = framed.chunk ∧ checked.dictionary = framed.dictionary ∧
      List.Forall₂ (PlanWire codec fallback bound) framed.data checked.data ∧
      Leaf.ScalarAndDictionary.WithV1.validate fallback checked.data = .ok () ∧
      codec.readEntries limits leafLimits bound framed.dictionary = .ok checked.entries ∧
      (checked.data.map (·.params.numValues)).sum = framed.chunk.group.numRows.toNat := by
  unfold checkFramed at read
  obtain ⟨_, budget, read⟩ := bind_ok read
  obtain ⟨data, planned, read⟩ := bind_ok read
  obtain ⟨_, phase, read⟩ := bind_ok read
  have plans : List.Forall₂ (PlanWire codec fallback bound) framed.data data := by
    rw [← List.zipIdx_map_fst 1 framed.data, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun _ _ h => planData_wire (mapError_ok h)
  have cap : codec.expansionLimit limits framed := by
    cases codec <;> simp_all [checkExpansion, Codec.expansionLimit]
  dsimp only at read
  split at read
  · contradiction
  · rename_i rows
    obtain ⟨entries, decoded, read⟩ := bind_ok read
    cases Except.ok.inj read
    exact ⟨cap, rfl, rfl, plans, mapError_ok phase, decoded, by simpa using rows⟩

private theorem plan_member {codec : Codec} {fallback : Bool} {bound : Bound}
    {frames : List Parquet.Page.Frame} {pages : List Dictionary.DataPage}
    (plans : List.Forall₂ (PlanWire codec fallback bound) frames pages)
    {page : Dictionary.DataPage} (member : page ∈ pages) :
    ∃ frame, PlanWire codec fallback bound frame page := by
  induction plans with
  | nil => simp at member
  | cons head _ ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨_, head⟩
    · exact ih rest

private theorem page_lengths {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {plans : List Dictionary.DataPage} {pages : List (List (Option Int64))}
    (wire : List.Forall₂ (PageWire codec limits leafLimits bound entries) plans pages) :
    pages.map List.length = plans.map (·.params.numValues) := by
  induction wire with
  | nil => rfl
  | cons current _ rest =>
    obtain ⟨_, _, _, _, _, count, _⟩ := current
    exact congrArg₂ List.cons count rest

theorem readV1_wire {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk} {slots : Slots bound}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (read : readV1 codec fallback limits leafLimits bound framed = .ok slots) :
    DictionaryWire codec fallback limits leafLimits bound index framed slots := by
  obtain ⟨selected, storedCap, frames, chain, dictionaryOffset, dataOffset⟩ :=
    Dictionary.frameGroupUsing_wire framedOk
  obtain ⟨group, column, _, _, _, codecId, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  have codecExact : framed.chunk.column.metadata.codec = codec.payload.id := by
    cases codec <;> simpa [Codec.encoding, Codec.payload, Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codecId
  unfold readV1 Dictionary.Zstd.V2.readGroupUsing at read
  obtain ⟨checked, checkedOk, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨cap, sameChunk, sameDictionary, plans, phase, entries, rows⟩ := checkFramed_wire checkedOk
  cases Except.ok.inj read
  have decodedWire : List.Forall₂ (PageWire codec limits leafLimits bound checked.entries.toArray) checked.data pages := by
    have pp : List.Forall₂ (fun item output => decodePage codec limits leafLimits bound
        checked.entries.toArray item.1 item.2 = .ok output) (checked.data.zipIdx 1) pages :=
      List.mapM_eq_ok_iff_forall₂.mp decoded
    have indexed : ∀ item ∈ checked.data.zipIdx 1, ∃ frame, PlanWire codec fallback bound frame item.1 := by
      intro item member
      apply plan_member plans
      rw [← List.zipIdx_map_fst 1 checked.data]
      exact List.mem_map.mpr ⟨item, member, rfl⟩
    have both := (List.forall₂_and_left (checked.data.zipIdx 1) pages).mpr ⟨indexed, pp⟩
    rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
    exact both.imp fun _ _ ⟨⟨_, planned⟩, h⟩ => decodePage_wire planned h
  refine ⟨selected, group, column, codecExact, frames, chain, storedCap, dictionaryOffset, dataOffset, cap,
    checked, pages, sameChunk, sameDictionary, plans, readEntries_wire entries, ?_, decodedWire, rfl, ?_, ?_⟩
  · intro isFallback
    exact Fallback.checkSequence_wire (by simpa [Leaf.ScalarAndDictionary.WithV1.validate, isFallback] using phase)
  · simp only [List.map_map, List.map_inj_left]
    intro item _
    cases item <;> rfl
  · rw [List.length_map, List.length_flatten, page_lengths decodedWire, rows]

theorem readV1_zstd_expansion_error {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {framed : Dictionary.FramedChunk}
    (excess : (zstdLimits limits).maxExpandedChunkBytes < (framed.frames.map (·.value.uncompressedSize)).sum) :
    readV1 .zstd fallback limits leafLimits bound framed = .error .expandedChunkLimit := by
  simp [readV1, Dictionary.Zstd.V2.readGroupUsing, checkFramed, checkExpansion, excess, Bind.bind, Except.bind]

theorem readV1_first_page_error {codec : Codec} {fallback : Bool} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {framed : Dictionary.FramedChunk} {checked : Dictionary.CheckedChunk}
    {before after : List (Dictionary.DataPage × Nat)} {page : Dictionary.DataPage} {ordinal : Nat}
    {outputs : List (List (Option Int64))} {cause : V1Error}
    (admitted : checkFramed codec fallback limits leafLimits bound framed = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun item => decodePage codec limits leafLimits bound checked.entries.toArray
      item.1 item.2) = .ok outputs)
    (failed : decodePage codec limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readV1 codec fallback limits leafLimits bound framed = .error cause := by
  simp [readV1, Dictionary.Zstd.V2.readGroupUsing, admitted, split, List.mapM_append, earlier, failed,
    Bind.bind, Except.bind]


theorem readDictionary_v1 {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {framed : Dictionary.FramedChunk} {fallback : Bool}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : Leaf.ScalarAndDictionary.WithV1.classifyFrames framed = .ok ⟨.v1, fallback⟩) :
    readDictionary codec limits leafLimits bound index =
      (readV1 codec fallback limits leafLimits bound framed).mapError (.v1 codec) := by
  simp [readDictionary, framedOk, chosen, Except.mapError, Bind.bind, Except.bind]

private theorem readV2_agrees {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {framed : Dictionary.FramedChunk}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed) :
    readV2 codec limits leafLimits bound framed =
      (Leaf.ScalarAndDictionary.readSelected limits leafLimits bound index codec.branch).mapError
        (.existing ∘ .existing) := by
  cases codec <;> simp only [frameGroup, Codec.encoding, Codec.dictionaryLimits] at framedOk <;>
    simp [readV2, Codec.branch, Leaf.ScalarAndDictionary.readSelected, Uncompressed.Dispatch.V2.readDictionary,
      Uncompressed.Dispatch.V2.planDictionary, Zstd.Dispatch.V2.readDictionary, Zstd.Dispatch.V2.planDictionary,
      framedOk, Except.map, Except.mapError, Bind.bind, Except.bind] <;>
    split <;> simp_all

theorem readDictionary_v2_agrees {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Leaf.ScalarAndDictionary.WithV1.Profile}
    (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : Leaf.ScalarAndDictionary.WithV1.classifyFrames framed = .ok profile)
    (version : profile.version = .v2) :
    readDictionary codec limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readSelected limits leafLimits bound index codec.branch).mapError
        (.existing ∘ .existing) := by
  simpa only [readDictionary, framedOk, chosen, version, Except.mapError, Bind.bind, Except.bind] using
    (readV2_agrees framedOk)

theorem readGroup_dictionary {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} (routed : Leaf.ScalarAndDictionary.route bound index = .ok codec.branch) :
    readGroup limits leafLimits bound index = readDictionary codec limits leafLimits bound index := by
  cases codec <;> simp only [Codec.branch] at routed <;>
    simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_existing {branch : Leaf.ScalarAndDictionary.Branch} {limits : Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : Leaf.ScalarAndDictionary.route bound index = .ok branch)
    (uncompressed : branch ≠ .dictionary .uncompressed) (zstd : branch ≠ .dictionary .zstd) :
    readGroup limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.WithV1.readGroup limits leafLimits bound index).mapError .existing := by
  cases branch with
  | scalar _ =>
    simp [readGroup, Leaf.ScalarAndDictionary.WithV1.readGroup, routed, Except.mapError, Bind.bind, Except.bind]
    split <;> rfl
  | dictionary codec =>
    cases codec <;> simp_all [readGroup, Leaf.ScalarAndDictionary.WithV1.readGroup, Except.mapError, Bind.bind, Except.bind]

private theorem readDictionary_wire {codec : Codec} {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (routed : Leaf.ScalarAndDictionary.route bound index = .ok codec.branch)
    (read : readDictionary codec limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  cases framedOk : frameGroup codec limits leafLimits bound index with
  | error cause => simp [readDictionary, framedOk, Except.mapError, Bind.bind, Except.bind] at read
  | ok framed =>
    cases chosen : Leaf.ScalarAndDictionary.WithV1.classifyFrames framed with
    | error cause => simp [readDictionary, framedOk, chosen, Except.mapError, Bind.bind, Except.bind] at read
    | ok profile =>
      rcases profile with ⟨version, fallback⟩
      cases version with
      | v1 =>
        rw [readDictionary_v1 framedOk chosen] at read
        exact .inr ⟨codec, framed, fallback, routed, framedOk, chosen, readV1_wire framedOk (mapError_ok read)⟩
      | v2 =>
        rw [readDictionary_v2_agrees framedOk chosen rfl] at read
        have base : Leaf.ScalarAndDictionary.readGroup limits leafLimits bound index = .ok slots := by
          simpa only [Leaf.ScalarAndDictionary.readGroup, routed, Bind.bind, Except.bind] using mapError_ok read
        exact .inl (.inr (Leaf.ScalarAndDictionary.readGroup_wire base))

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  cases routed : Leaf.ScalarAndDictionary.route bound index with
  | error cause => simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind] at read
  | ok branch =>
    by_cases raw : branch = .dictionary .uncompressed
    · subst branch
      rw [readGroup_dictionary (codec := .uncompressed) routed] at read
      exact readDictionary_wire (codec := .uncompressed) routed read
    by_cases compressed : branch = .dictionary .zstd
    · subst branch
      rw [readGroup_dictionary (codec := .zstd) routed] at read
      exact readDictionary_wire (codec := .zstd) routed read
    rw [readGroup_existing routed raw compressed] at read
    exact .inl (Leaf.ScalarAndDictionary.WithV1.readGroup_wire (mapError_ok read))

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs

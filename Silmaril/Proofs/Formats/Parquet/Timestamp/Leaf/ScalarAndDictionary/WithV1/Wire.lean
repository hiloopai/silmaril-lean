module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1

open Silmaril.Formats Parquet Timestamp Leaf
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
open Silmaril.Numeric.Timestamp (Ticks)

private theorem gzip_framing (limits : Dictionary.Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat) :
    Dictionary.frameGroupUsing .gzipDictionaryV1 limits leafLimits bound index =
      Dictionary.frameGroupUsing .gzipDictionaryV2 limits leafLimits bound index := by
  have same : selectChunkWith .gzipDictionaryV1 leafLimits bound index =
      selectChunkWith .gzipDictionaryV2 leafLimits bound index := by
    simp only [selectChunkWith, ChunkEncoding.gzipDictionaryV1_admitsMetadata, ChunkEncoding.admitsCodec]
  simp only [Dictionary.frameGroupUsing, same]

theorem classifyFrames_ok {framed : Dictionary.FramedChunk} {profile : Profile}
    (chosen : classifyFrames framed = .ok profile) :
    profile.version = firstVersion framed ∧ profile.fallback = hasPlain profile.version framed ∧
      ∀ pair ∈ framed.data.zipIdx 1, hasOtherVersion profile.version pair.1 = false := by
  simp only [classifyFrames] at chosen
  split at chosen
  · contradiction
  · rename_i indexed
    cases chosen
    exact ⟨rfl, rfl, fun pair member => Bool.eq_false_iff.mpr (List.find?_eq_none.mp indexed pair member)⟩

theorem classifyFrames_mixed {framed : Dictionary.FramedChunk} {page offset : Nat}
    (rejected : classifyFrames framed = .error (.mixedVersions page offset)) :
    ∃ before frame after, framed.data.zipIdx 1 = before ++ (frame, page) :: after ∧
      frame.header.start = offset ∧ hasOtherVersion (firstVersion framed) frame = true ∧
      ∀ pair ∈ before, hasOtherVersion (firstVersion framed) pair.1 = false := by
  simp only [classifyFrames] at rejected
  split at rejected
  · rename_i frame page found
    cases rejected
    obtain ⟨mismatch, before, after, listed, earlier⟩ := List.find?_eq_some_iff_append.mp found
    exact ⟨before, frame, after, listed, rfl, mismatch, fun pair member => by simpa using earlier pair member⟩
  · contradiction

private theorem gzip_plan_parameters {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame}
    {page : Dictionary.DataPage} (planned : Dictionary.Gzip.planDataWith admits bound frame = .ok page) :
    Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.gzip.id frame.value =
      .ok page.params := by
  obtain ⟨_, info, kind, tag, _⟩ := Dictionary.Gzip.planDataWith_wire planned
  cases chosen : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.gzip.id frame.value <;>
    simp [Dictionary.Gzip.planDataWith, kind, tag, chosen, Bind.bind, Except.bind, Except.mapError,
      pure, Except.pure] at planned
  subst page
  rfl

private theorem plan_keeps_frame {codec : Codec} {profile : Profile} {bound : Bound}
    {frame : Parquet.Page.Frame} {page : Dictionary.DataPage}
    (planned : planData codec profile bound frame = .ok page) :
    page.frame = frame ∧ (profile.version = .v1 → Timestamp.Page.parameters bound.binding.leaf bound.levels
      codec.payload.id frame.value = .ok page.params) := by
  rcases profile with ⟨version, fallback⟩
  cases codec <;> cases version <;> cases fallback <;> simp only [planData] at planned
  · exact ⟨(Dictionary.Snappy.planData_wire planned).1, fun _ => (Dictionary.Snappy.planData_wire planned).2.1⟩
  · exact ⟨(Dictionary.Snappy.planDataWith_wire planned).1, fun _ => (Dictionary.Snappy.planDataWith_wire planned).2.1⟩
  · exact ⟨(Dictionary.Snappy.V2.planData_wire planned).1, by simp⟩
  · exact ⟨(Fallback.Snappy.V2.planData_wire planned).1, by simp⟩
  · exact ⟨(Dictionary.Gzip.planData_wire planned).1, fun _ => gzip_plan_parameters planned⟩
  · exact ⟨(Fallback.Gzip.planData_wire planned).1, fun _ => gzip_plan_parameters planned⟩
  · exact ⟨(Dictionary.Gzip.V2.planData_wire planned).1, by simp⟩
  · exact ⟨(Fallback.Gzip.V2.planData_wire planned).1, by simp⟩

private theorem checkFramed_wire {codec : Codec} {profile : Profile} {bound : Bound}
    {framed : Dictionary.FramedChunk} {checked : Dictionary.CheckedChunk}
    {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits}
    (admitted : Dictionary.checkFramedUsing framed (planData codec profile bound)
      (validate profile.fallback) (codec.readEntries limits leafLimits bound) = .ok checked) :
    checked.chunk = framed.chunk ∧ checked.dictionary = framed.dictionary ∧
    List.Forall₂ (fun frame page => planData codec profile bound frame = .ok page ∧ page.frame = frame ∧
      (profile.version = .v1 → Timestamp.Page.parameters bound.binding.leaf bound.levels
        codec.payload.id frame.value = .ok page.params)) framed.data checked.data ∧
    validate profile.fallback checked.data = .ok () ∧
    codec.readEntries limits leafLimits bound framed.dictionary = .ok checked.entries ∧
    (checked.data.map (·.params.numValues)).sum = framed.chunk.group.numRows.toNat := by
  unfold Dictionary.checkFramedUsing at admitted
  dsimp [Bind.bind, Except.bind] at admitted
  split at admitted
  · contradiction
  · rename_i data planned
    unfold Dictionary.checkPlannedUsing at admitted
    dsimp [Bind.bind, Except.bind] at admitted
    split at admitted
    · contradiction
    · rename_i valid
      split at admitted
      · contradiction
      · rename_i rows
        split at admitted
        · contradiction
        · rename_i entries read
          cases admitted
          have plans : List.Forall₂ (fun pair page => planData codec profile bound pair.1 = .ok page)
              (framed.data.zipIdx 1) data := (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun pair page h => by
            cases result : planData codec profile bound pair.1 <;> simp [Except.mapError, result] at h ⊢
            exact h
          have frames : List.Forall₂ (fun frame page => planData codec profile bound frame = .ok page)
              ((framed.data.zipIdx 1).map Prod.fst) data := List.forall₂_map_left_iff.mpr plans
          rw [List.zipIdx_map_fst] at frames
          refine ⟨rfl, rfl, frames.imp (fun _ _ h => ⟨h, plan_keeps_frame h⟩),
            valid, ?_, by simpa using rows⟩
          cases result : codec.readEntries limits leafLimits bound framed.dictionary <;>
            simp [Except.mapError, result] at read ⊢
          exact read

theorem readDictionary_agrees {codec : Codec} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Profile} (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : classifyFrames framed = .ok profile) :
    readDictionary codec limits leafLimits bound index =
      (standalone codec profile limits leafLimits bound index).mapError (codec.error profile.version) := by
  simp only [readDictionary, framedOk, chosen, Except.mapError, Bind.bind, Except.bind]
  rcases profile with ⟨version, fallback⟩
  cases codec <;>
    simp only [frameGroup, Codec.encoding, Codec.dictionaryLimits] at framedOk <;>
    cases version <;> cases fallback <;>
    simp [standalone, readFramed, planData, validate, Codec.scalarLimits, Codec.dictionaryLimits,
      Codec.readEntries, Dictionary.Snappy.readGroup, Dictionary.Snappy.checkGroup,
      Fallback.Snappy.readGroup, Fallback.Snappy.checkGroup, Dictionary.Snappy.V2.readGroup,
      Dictionary.Snappy.V2.checkGroup, Fallback.Snappy.V2.readGroup, Fallback.Snappy.V2.checkGroup,
      Dictionary.Gzip.readGroup, Dictionary.Gzip.checkGroup, Fallback.Gzip.readGroup,
      Fallback.Gzip.checkGroup, Dictionary.Gzip.V2.readGroup, Dictionary.Gzip.V2.checkGroup,
      Fallback.Gzip.V2.readGroup, Fallback.Gzip.V2.checkGroup,
      Dictionary.checkGroupUsing, gzip_framing, framedOk, Bind.bind, Except.bind]

private theorem entries_wire {codec : Codec} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {frame : Parquet.Page.Frame} {entries : List Int64}
    (read : codec.readEntries limits leafLimits bound frame = .ok entries) :
    EntriesWire codec limits leafLimits bound frame entries := by
  cases codec with
  | snappy =>
    obtain ⟨header, status, expanded, kind, tag, cap, crc, decoded, size, outputCap, plain, count⟩ :=
      Dictionary.Snappy.readEntries_wire read
    exact ⟨header, expanded, kind, tag, cap, ⟨⟨status, crc⟩, decoded, size, outputCap⟩, plain, count⟩
  | gzip =>
    exact Dictionary.Gzip.readEntries_wire read

theorem readDictionary_wire {codec : Codec} {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readDictionary codec limits leafLimits bound index = .ok slots) :
    DictionaryWire codec limits leafLimits bound index slots := by
  cases framedOk : frameGroup codec limits leafLimits bound index with
  | error cause => simp [readDictionary, framedOk, Except.mapError, Bind.bind, Except.bind] at read
  | ok framed =>
    cases chosen : classifyFrames framed with
    | error cause => simp [readDictionary, framedOk, chosen, Except.mapError, Bind.bind, Except.bind] at read
    | ok profile =>
      have raw : readFramed codec limits leafLimits bound framed profile = .ok slots := by
        cases result : readFramed codec limits leafLimits bound framed profile <;>
          simp [readDictionary, framedOk, chosen, result, Except.mapError, Bind.bind, Except.bind] at read ⊢
        exact read
      let admission := Dictionary.checkFramedUsing framed (planData codec profile bound)
        (validate profile.fallback) (codec.readEntries limits leafLimits bound)
      have decoded : ∃ checked pages, admission = .ok checked ∧
          List.Forall₂ (if profile.fallback then
            Fallback.Snappy.DataWire (codec.dictionaryLimits limits) (codec.scalarLimits limits leafLimits)
              bound checked.entries.toArray
            else Dictionary.Snappy.DataWire (codec.dictionaryLimits limits) (codec.scalarLimits limits leafLimits)
              bound checked.entries.toArray) checked.data pages ∧
          slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
          slots.length = (checked.data.map (·.params.numValues)).sum := by
        cases mode : profile.fallback
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Dictionary.Snappy.readGroupUsing_wire (by simpa [readFramed, mode, admission] using raw)
        · simp only [↓reduceIte]
          apply Fallback.Snappy.readGroupUsing_wire (dictionaryTag := 8) (admission := admission)
          · intro checked checkedOk
            exact Fallback.checkSequence_wire (by
              simpa [validate, mode] using (checkFramed_wire checkedOk).2.2.2.1)
          · simpa [readFramed, mode, admission] using raw
      obtain ⟨checked, pages, admitted, data, ordered, rows⟩ := decoded
      obtain ⟨selected, cap, frames, chain, dictionaryOffset, dataOffset⟩ :=
        Dictionary.frameGroupUsing_wire framedOk
      obtain ⟨chunk, dictionary, plans, sequence, entries, rowCount⟩ := checkFramed_wire admitted
      refine ⟨framed, profile, checked, pages, framedOk, chosen, selected, frames, chain, cap,
        dictionaryOffset, dataOffset, chunk, dictionary, plans, sequence, entries_wire entries, ?_, data, ordered, ?_,
        rows.trans rowCount⟩
      · intro fallback
        exact Fallback.checkSequence_wire (by simpa [validate, fallback] using sequence)
      · rw [ordered, List.map_map]
        apply List.map_congr_left
        intro raw _
        cases raw <;> rfl

theorem readGroup_dictionary {codec : Codec} {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} (route : Leaf.ScalarAndDictionary.route bound index = .ok codec.branch) :
    Leaf.ScalarAndDictionary.WithV1.readGroup limits leafLimits bound index =
      readDictionary codec limits leafLimits bound index := by
  cases codec <;> simp only [Codec.branch] at route <;>
    simp [Leaf.ScalarAndDictionary.WithV1.readGroup, route, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_existing {branch : Leaf.ScalarAndDictionary.Branch} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (route : Leaf.ScalarAndDictionary.route bound index = .ok branch)
    (snappy : branch ≠ .dictionary .snappy) (gzip : branch ≠ .dictionary .gzip) :
    Leaf.ScalarAndDictionary.WithV1.readGroup limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readGroup limits leafLimits bound index).mapError .existing := by
  cases branch with
  | scalar codec => simp [Leaf.ScalarAndDictionary.WithV1.readGroup, Leaf.ScalarAndDictionary.readGroup,
      route, Except.mapError, Bind.bind, Except.bind]
  | dictionary codec =>
    cases codec <;>
      simp_all [Leaf.ScalarAndDictionary.WithV1.readGroup, Leaf.ScalarAndDictionary.readGroup,
        Except.mapError, Bind.bind, Except.bind]

theorem readDictionary_v2_agrees {codec : Codec} {limits : ScalarAndDictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {framed : Dictionary.FramedChunk}
    {profile : Profile} (framedOk : frameGroup codec limits leafLimits bound index = .ok framed)
    (chosen : classifyFrames framed = .ok profile) (version : profile.version = .v2) :
    readDictionary codec limits leafLimits bound index =
      (Leaf.ScalarAndDictionary.readSelected limits leafLimits bound index codec.branch).mapError .existing := by
  obtain ⟨_, mode, _⟩ := classifyFrames_ok chosen
  rcases profile with ⟨page, fallback⟩
  simp only at version
  subst page
  have plain : framed.data.any Snappy.Dispatch.V2.isPlainV2 = fallback := mode.symm
  have gzipPlain : framed.data.any Gzip.Dispatch.V2.isPlainV2 = fallback := plain
  cases codec <;>
    simp only [frameGroup, Codec.encoding, Codec.dictionaryLimits] at framedOk <;>
    cases fallback <;>
    simp [readDictionary, chosen, frameGroup, Codec.encoding, Codec.dictionaryLimits, framedOk,
      Codec.branch, Codec.error, Codec.readEntries, Codec.scalarLimits, readFramed, planData, validate,
      Leaf.ScalarAndDictionary.readSelected, Snappy.Dispatch.V2.readDictionary, Snappy.Dispatch.V2.planDictionary,
      Snappy.Dispatch.V2.dictionaryProfile, plain, Gzip.Dispatch.V2.readDictionary, Gzip.Dispatch.V2.planDictionary,
      Gzip.Dispatch.V2.dictionaryProfile, gzipPlain, Except.mapError, Except.map, Bind.bind, Except.bind] <;>
    split <;> simp_all

theorem readGroup_wire {limits : ScalarAndDictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : Leaf.ScalarAndDictionary.WithV1.readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  cases routed : Leaf.ScalarAndDictionary.route bound index with
  | error cause => simp [Leaf.ScalarAndDictionary.WithV1.readGroup, routed, Except.mapError, Bind.bind, Except.bind] at read
  | ok branch =>
    by_cases snappy : branch = .dictionary .snappy
    · subst branch
      rw [readGroup_dictionary (codec := .snappy) routed] at read
      exact .inl ⟨.snappy, routed, readDictionary_wire read⟩
    by_cases gzip : branch = .dictionary .gzip
    · subst branch
      rw [readGroup_dictionary (codec := .gzip) routed] at read
      exact .inl ⟨.gzip, routed, readDictionary_wire read⟩
    rw [readGroup_existing routed snappy gzip] at read
    apply Or.inr
    apply Leaf.ScalarAndDictionary.readGroup_wire
    cases result : Leaf.ScalarAndDictionary.readGroup limits leafLimits bound index <;>
      simp [Except.mapError, result] at read ⊢
    exact read

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1

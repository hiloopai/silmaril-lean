module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (CheckedChunk FramedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2
open Silmaril.Numeric.Timestamp (Ticks)

private theorem isPlainV2_iff {frame : Parquet.Page.Frame} :
    isPlainV2 frame = true ↔ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 := by
  cases kind : frame.value.kind <;> simp [isPlainV2, kind]

theorem dictionaryProfile_fallback_iff {frames : List Parquet.Page.Frame} :
    dictionaryProfile frames = .fallback ↔
      ∃ frame ∈ frames, ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 := by
  have choice : dictionaryProfile frames = .fallback ↔ frames.any isPlainV2 = true := by
    by_cases any : frames.any isPlainV2 <;> simp [dictionaryProfile, any]
  rw [choice, List.any_eq_true]
  simp only [isPlainV2_iff]

private theorem planDictionary_source {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index =
      .ok plan.framed ∧ dictionaryProfile plan.framed.data = plan.profile := by
  cases source : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index with
  | error cause => simp [planDictionary, source, Except.map] at planned
  | ok framed =>
    simp [planDictionary, source, Except.map] at planned
    subst plan
    exact ⟨rfl, rfl⟩

theorem planDictionary_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.profile = .fallback ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV2 header ∧ header.encoding = 0) := by
  obtain ⟨source, choice⟩ := planDictionary_source planned
  obtain ⟨selected, cap, wire, chain, dictionary, data⟩ := Leaf.Dictionary.frameGroupUsing_wire source
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, wire, chain, dictionary, data, by rw [← choice, dictionaryProfile_fallback_iff]⟩

theorem readDictionary_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readDictionary limits leafLimits bound index =
      match plan.profile with
      | .references => Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index := by
  obtain ⟨framed, _⟩ := planDictionary_source planned
  cases chosen : plan.profile <;>
    simp [readDictionary, planned, chosen, Leaf.Dictionary.Snappy.V2.readGroup, Leaf.Dictionary.Snappy.V2.checkGroup,
      Leaf.Fallback.Snappy.V2.readGroup, Leaf.Fallback.Snappy.V2.checkGroup, Leaf.Dictionary.checkGroupUsing,
      framed, Bind.bind, Except.bind]

theorem dictionary_framing_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index = .error cause) :
    readDictionary limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index = .error cause := by
  simp [readDictionary, planDictionary, failed, Leaf.Dictionary.Snappy.V2.readGroup, Leaf.Dictionary.Snappy.V2.checkGroup,
    Leaf.Fallback.Snappy.V2.readGroup, Leaf.Fallback.Snappy.V2.checkGroup, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Fallback.Snappy.readGroupUsing,
    Except.map, Bind.bind, Except.bind]

private theorem sameFrames {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} {checked : CheckedChunk}
    (planned : planDictionary limits leafLimits bound index = .ok plan)
    (selected : selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk)
    (framed : Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames) :
    checked.frames = plan.framed.frames := by
  obtain ⟨source, _⟩ := planDictionary_source planned
  obtain ⟨same, _, frames, _, _, _⟩ := Leaf.Dictionary.frameGroupUsing_wire source
  have chunk := Except.ok.inj (selected.symm.trans same)
  rw [chunk] at framed
  exact Except.ok.inj (framed.symm.trans frames)

theorem readDictionary_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} {slots : Slots bound}
    (planned : planDictionary limits leafLimits bound index = .ok plan)
    (read : readDictionary limits leafLimits bound index = .ok slots) :
    DictionaryWire limits leafLimits bound index plan slots := by
  rw [readDictionary_matches planned] at read
  unfold DictionaryWire
  cases chosen : plan.profile with
  | references =>
    rw [chosen] at read
    obtain ⟨checked, pages, admitted, decoded, ordered, ticks, rows⟩ := Leaf.Dictionary.Snappy.V2.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _⟩ := Leaf.Dictionary.Snappy.V2.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ordered, ticks, rows⟩
  | fallback =>
    rw [chosen] at read
    obtain ⟨checked, pages, admitted, decoded, ordered, ticks, rows⟩ := Leaf.Fallback.Snappy.V2.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _, _⟩ := Leaf.Fallback.Snappy.V2.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ordered, ticks, rows⟩

theorem hasDictionary_selected {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits} {bound : Bound}
    {index : Nat} {chunk : Leaf.Chunk} (selected : selectChunkWith encoding limits bound index = .ok chunk) :
    hasDictionary bound index = .ok chunk.column.metadata.dictionaryPageOffset.isSome := by
  obtain ⟨group, column, _⟩ := Leaf.selectChunkWith_sound selected
  simp [hasDictionary, group, column, pure, Except.pure]

private theorem selectChunk_lookup_error {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    selectChunkWith encoding limits bound index = .error cause := by
  cases group : bound.snapshot.groupAt index with
  | none =>
    simp [hasDictionary, group] at failed
    change Except.error (Leaf.Error.groupIndex index) = .error cause at failed
    simp [selectChunkWith, group, Except.error.inj failed]
  | some rowGroup =>
    cases column : rowGroup.columns[bound.ordinal - 1]? with
    | none =>
      simp [hasDictionary, group, column] at failed
      change Except.error (Leaf.Error.chunkIndex (bound.ordinal - 1)) = .error cause at failed
      simp [selectChunkWith, group, column, Except.error.inj failed]
    | some _ => simp [hasDictionary, group, column, pure, Except.pure] at failed

theorem readGroup_route_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.SnappyV2.readGroup leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index = .error cause := by
  have plain := selectChunk_lookup_error (encoding := .plain)
    (limits := {leafLimits with allowSnappy := true}) failed
  have dictionary := selectChunk_lookup_error (encoding := .snappyDictionary) (limits := leafLimits) failed
  exact ⟨by simp [readGroup, failed, Bind.bind, Except.bind],
    by simp [Leaf.SnappyV2.readGroup, Leaf.SnappyV2.checkGroup, Leaf.selectChunk, plain, Bind.bind, Except.bind],
    by simp [Leaf.Dictionary.Snappy.V2.readGroup, Leaf.Dictionary.Snappy.V2.checkGroup,
      Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing, Leaf.Dictionary.frameGroupUsing,
      dictionary, Bind.bind, Except.bind],
    by simp [Leaf.Fallback.Snappy.V2.readGroup, Leaf.Fallback.Snappy.V2.checkGroup,
      Leaf.Fallback.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing, Leaf.Dictionary.frameGroupUsing,
      dictionary, Bind.bind, Except.bind]⟩

theorem readGroup_plain_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : hasDictionary bound index = .ok false) :
    readGroup limits leafLimits bound index = Leaf.SnappyV2.readGroup leafLimits bound index := by
  simp [readGroup, routed, Bind.bind, Except.bind]

theorem readGroup_dictionary_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (routed : hasDictionary bound index = .ok true)
    (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      match plan.profile with
      | .references => Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index := by
  rw [show readGroup limits leafLimits bound index = readDictionary limits leafLimits bound index by
    simp [readGroup, routed, Bind.bind, Except.bind]]
  exact readDictionary_matches planned

theorem readGroup_dictionary_setup_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {cause : Leaf.Error}
    (routed : hasDictionary bound index = .ok true)
    (failed : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index = .error cause := by
  obtain ⟨dispatch, references, fallback⟩ := dictionary_framing_error failed
  exact ⟨by simp [readGroup, routed, dispatch, Bind.bind, Except.bind], references, fallback⟩

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots := by
  cases routed : hasDictionary bound index with
  | error cause => simp [readGroup, routed, Bind.bind, Except.bind] at read
  | ok route =>
    cases route with
    | false =>
      rw [readGroup_plain_matches routed] at read
      obtain ⟨_, _, checked, decoded, ordered, ticks, rows⟩ := Leaf.SnappyV2.readGroup_wire read
      exact .plain routed checked decoded ordered ticks rows
    | true =>
      have decoded : readDictionary limits leafLimits bound index = .ok slots := by
        simpa [readGroup, routed, Bind.bind, Except.bind] using read
      cases planned : planDictionary limits leafLimits bound index with
      | error cause => simp [readDictionary, planned, Bind.bind, Except.bind] at decoded
      | ok plan => exact .dictionary routed planned (readDictionary_wire planned decoded)

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2

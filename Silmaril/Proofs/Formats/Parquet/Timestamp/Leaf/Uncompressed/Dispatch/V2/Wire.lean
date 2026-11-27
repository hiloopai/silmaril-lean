module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (CheckedChunk FramedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2
open Silmaril.Numeric.Timestamp (Ticks)

private theorem isPlainV2_iff {frame : Parquet.Page.Frame} :
    isPlainV2 frame = true ↔ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 := by
  cases kind : frame.value.kind <;> simp [isPlainV2, Leaf.Snappy.Dispatch.V2.isPlainV2, kind]

private theorem scan_classifies (bound : Bound) (frames : List Parquet.Page.Frame) (ordinal : Nat)
    (seen : Bool) (planned : Except Leaf.Error (List Leaf.Dictionary.DataPage)) :
    (scanHeaders bound frames ordinal seen planned).hasPlain = (seen || frames.any isPlainV2) := by
  induction frames generalizing ordinal seen planned with
  | nil => simp [scanHeaders]
  | cons frame rest ih => simp [scanHeaders, ih, Bool.or_assoc]

private theorem scan_plans (bound : Bound) (frames : List Parquet.Page.Frame) (ordinal : Nat)
    (seen : Bool) (planned : Except Leaf.Error (List Leaf.Dictionary.DataPage)) :
    (scanHeaders bound frames ordinal seen planned).data = (do
      let earlier ← planned
      let later ← (frames.zipIdx ordinal).mapM fun (frame, i) => planAt bound frame i
      return earlier.reverse ++ later) := by
  induction frames generalizing ordinal seen planned with
  | nil => cases planned <;> simp [scanHeaders, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cons frame rest ih =>
    rw [scanHeaders, ih, List.zipIdx_cons, List.mapM_cons]
    cases planned with
    | error cause => rfl
    | ok earlier =>
      cases decoded : planAt bound frame ordinal with
      | error cause => simp [decoded, Bind.bind, Except.bind]
      | ok page =>
        simp [decoded, Bind.bind, Except.bind, Pure.pure, Except.pure, List.reverse_cons, List.append_assoc]
        cases (rest.zipIdx (ordinal + 1)).mapM (fun item => planAt bound item.1 item.2) <;> rfl

theorem scanHeaders_exact (bound : Bound) (frames : List Parquet.Page.Frame) (ordinal : Nat) :
    let scan := scanHeaders bound frames ordinal false (.ok [])
    (scan.hasPlain = true ↔ ∃ frame ∈ frames, ∃ header,
      frame.value.kind = .dataV2 header ∧ header.encoding = 0) ∧
    scan.data = (frames.zipIdx ordinal).mapM (fun (frame, i) => planAt bound frame i) := by
  dsimp only
  rw [scan_classifies, Bool.false_or, List.any_eq_true]
  refine ⟨by simp only [isPlainV2_iff], ?_⟩
  rw [scan_plans]
  cases (frames.zipIdx ordinal).mapM (fun (frame, i) => planAt bound frame i) <;> rfl

private theorem planAt_notPlain {bound : Bound} {frame : Parquet.Page.Frame} {ordinal : Nat}
    (notPlain : isPlainV2 frame = false) :
    planAt bound frame ordinal =
      (Leaf.Dictionary.Uncompressed.V2.planData bound frame).mapError (Leaf.Dictionary.atFrame ordinal frame) := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    have tag : header.encoding ≠ 0 := by
      simpa [isPlainV2, Leaf.Snappy.Dispatch.V2.isPlainV2, kind] using notPlain
    by_cases references : header.encoding = 8 <;>
      simp [planAt, Leaf.Fallback.Uncompressed.V2.planData, Leaf.Dictionary.Uncompressed.V2.planData,
        Leaf.Dictionary.Uncompressed.V2.planDataWith, Leaf.Fallback.admits, kind, tag, references]
  | dataV1 _ | dictionary _ | skipped _ =>
    simp [planAt, Leaf.Fallback.Uncompressed.V2.planData, Leaf.Dictionary.Uncompressed.V2.planData,
      Leaf.Dictionary.Uncompressed.V2.planDataWith, kind]

private theorem plans_notPlain (bound : Bound) (frames : List Parquet.Page.Frame) (ordinal : Nat)
    (notPlain : frames.any isPlainV2 = false) :
    (frames.zipIdx ordinal).mapM (fun (frame, i) => planAt bound frame i) =
      (frames.zipIdx ordinal).mapM (fun (frame, i) =>
        (Leaf.Dictionary.Uncompressed.V2.planData bound frame).mapError (Leaf.Dictionary.atFrame i frame)) := by
  induction frames generalizing ordinal with
  | nil => rfl
  | cons frame rest ih =>
    have tags : isPlainV2 frame = false ∧ rest.any isPlainV2 = false := by
      simpa using notPlain
    simp only [List.zipIdx_cons, List.mapM_cons]
    rw [planAt_notPlain tags.1, ih _ tags.2]

private theorem planDictionary_source {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .ok plan.framed ∧
      plan.headers = scanHeaders bound plan.framed.data 1 false (.ok []) := by
  cases source : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index with
  | error cause => simp [planDictionary, source, Except.map] at planned
  | ok framed =>
    simp [planDictionary, source, Except.map] at planned
    subst plan
    exact ⟨rfl, rfl⟩

theorem planDictionary_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    selectChunkWith .dictionary leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.column.metadata.codec = Payload.Codec.uncompressed.id ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.headers.hasPlain = true ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV2 header ∧ header.encoding = 0) := by
  obtain ⟨source, choice⟩ := planDictionary_source planned
  obtain ⟨selected, cap, wire, chain, dictionary, data⟩ := Leaf.Dictionary.frameGroupUsing_wire source
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, wire, chain, dictionary, data, by rw [choice]; exact (scanHeaders_exact bound _ 1).1⟩

theorem readDictionary_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readDictionary limits leafLimits bound index =
      if plan.headers.hasPlain then Leaf.Fallback.Uncompressed.V2.readGroup limits leafLimits bound index
      else Leaf.Dictionary.Uncompressed.V2.readGroup limits leafLimits bound index := by
  obtain ⟨framed, headers⟩ := planDictionary_source planned
  have plans := (scanHeaders_exact bound plan.framed.data 1).2
  rw [← headers] at plans
  cases chosen : plan.headers.hasPlain with
  | false =>
    have noPlain : plan.framed.data.any isPlainV2 = false := by
      rw [headers, scan_classifies, Bool.false_or] at chosen
      exact chosen
    rw [plans_notPlain bound _ 1 noPlain] at plans
    simp only [readDictionary, readFramedDictionary, planned, chosen, Leaf.Dictionary.Uncompressed.V2.readGroup,
      Leaf.Dictionary.Uncompressed.V2.checkGroup, Leaf.Dictionary.checkGroupUsing, framed,
      Leaf.Dictionary.checkFramedUsing, Bind.bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
    rw [← plans]
    cases plan.headers.data <;> rfl
  | true =>
    simp only [planAt] at plans
    simp only [readDictionary, readFramedDictionary, planned, chosen, Leaf.Fallback.Uncompressed.V2.readGroup,
      Leaf.Fallback.Uncompressed.V2.checkGroup, Leaf.Dictionary.checkGroupUsing, framed,
      Leaf.Dictionary.checkFramedUsing, Bind.bind, Except.bind, ↓reduceIte]
    rw [← plans]
    cases plan.headers.data <;> rfl

theorem dictionary_framing_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .error cause) :
    readDictionary limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause := by
  simp [readDictionary, planDictionary, failed, Leaf.Dictionary.Uncompressed.V2.readGroup, Leaf.Dictionary.Uncompressed.V2.checkGroup,
    Leaf.Fallback.Uncompressed.V2.readGroup, Leaf.Fallback.Uncompressed.V2.checkGroup, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Fallback.Snappy.readGroupUsing,
    Except.map, Bind.bind, Except.bind]

private theorem sameFrames {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} {checked : CheckedChunk}
    (planned : planDictionary limits leafLimits bound index = .ok plan)
    (selected : selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk)
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
  cases chosen : plan.headers.hasPlain with
  | false =>
    simp only [chosen, Bool.false_eq_true, ↓reduceIte] at read ⊢
    obtain ⟨checked, pages, admitted, decoded, ordered, ticks, rows⟩ := Leaf.Dictionary.Uncompressed.V2.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _⟩ := Leaf.Dictionary.Uncompressed.V2.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ordered, ticks, rows⟩
  | true =>
    simp only [chosen, ↓reduceIte] at read ⊢
    obtain ⟨checked, pages, admitted, decoded, ordered, ticks, rows⟩ := Leaf.Fallback.Uncompressed.V2.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _, _⟩ := Leaf.Fallback.Uncompressed.V2.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ordered, ticks, rows⟩

theorem hasDictionary_selected {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits} {bound : Bound}
    {index : Nat} {chunk : Leaf.Chunk} (selected : selectChunkWith encoding limits bound index = .ok chunk) :
    hasDictionary bound index = .ok chunk.column.metadata.dictionaryPageOffset.isSome :=
  Leaf.Snappy.Dispatch.V2.hasDictionary_selected selected

private theorem selectChunk_lookup_error {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    selectChunkWith encoding limits bound index = .error cause := by
  cases group : bound.snapshot.groupAt index with
  | none =>
    simp [hasDictionary, Leaf.Snappy.Dispatch.V2.hasDictionary, group] at failed
    change Except.error (Leaf.Error.groupIndex index) = .error cause at failed
    simp [selectChunkWith, group, Except.error.inj failed]
  | some rowGroup =>
    cases column : rowGroup.columns[bound.ordinal - 1]? with
    | none =>
      simp [hasDictionary, Leaf.Snappy.Dispatch.V2.hasDictionary, group, column] at failed
      change Except.error (Leaf.Error.chunkIndex (bound.ordinal - 1)) = .error cause at failed
      simp [selectChunkWith, group, column, Except.error.inj failed]
    | some _ => simp [hasDictionary, Leaf.Snappy.Dispatch.V2.hasDictionary, group, column, pure, Except.pure] at failed

theorem readGroup_route_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Uncompressed.V2.readGroup leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause := by
  have plain := selectChunk_lookup_error (encoding := .plain)
    (limits := {leafLimits with allowSnappy := false}) failed
  have dictionary := selectChunk_lookup_error (encoding := .dictionary) (limits := leafLimits) failed
  exact ⟨by simp [readGroup, failed, Bind.bind, Except.bind],
    by simp [Leaf.Uncompressed.V2.readGroup, Leaf.Uncompressed.V2.checkGroup, Leaf.selectChunk, plain, Bind.bind, Except.bind],
    by simp [Leaf.Dictionary.Uncompressed.V2.readGroup, Leaf.Dictionary.Uncompressed.V2.checkGroup,
      Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing, Leaf.Dictionary.frameGroupUsing,
      dictionary, Bind.bind, Except.bind],
    by simp [Leaf.Fallback.Uncompressed.V2.readGroup, Leaf.Fallback.Uncompressed.V2.checkGroup,
      Leaf.Fallback.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing, Leaf.Dictionary.frameGroupUsing,
      dictionary, Bind.bind, Except.bind]⟩

theorem readGroup_plain_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : hasDictionary bound index = .ok false) :
    readGroup limits leafLimits bound index = Leaf.Uncompressed.V2.readGroup leafLimits bound index := by
  simp [readGroup, routed, Bind.bind, Except.bind]

theorem readGroup_dictionary_matches {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (routed : hasDictionary bound index = .ok true)
    (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      if plan.headers.hasPlain then Leaf.Fallback.Uncompressed.V2.readGroup limits leafLimits bound index
      else Leaf.Dictionary.Uncompressed.V2.readGroup limits leafLimits bound index := by
  rw [show readGroup limits leafLimits bound index = readDictionary limits leafLimits bound index by
    simp [readGroup, routed, Bind.bind, Except.bind]]
  exact readDictionary_matches planned

theorem readGroup_dictionary_setup_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {cause : Leaf.Error}
    (routed : hasDictionary bound index = .ok true)
    (failed : Leaf.Dictionary.frameGroupUsing .dictionary limits leafLimits bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Uncompressed.V2.readGroup limits leafLimits bound index = .error cause := by
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
      obtain ⟨_, _, checked, decoded, ordered, ticks, rows⟩ := Leaf.Uncompressed.V2.readGroup_wire read
      exact .plain routed checked decoded ordered ticks rows
    | true =>
      have decoded : readDictionary limits leafLimits bound index = .ok slots := by
        simpa [readGroup, routed, Bind.bind, Except.bind] using read
      cases planned : planDictionary limits leafLimits bound index with
      | error cause => simp [readDictionary, planned, Bind.bind, Except.bind] at decoded
      | ok plan => exact .dictionary routed planned (readDictionary_wire planned decoded)

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2

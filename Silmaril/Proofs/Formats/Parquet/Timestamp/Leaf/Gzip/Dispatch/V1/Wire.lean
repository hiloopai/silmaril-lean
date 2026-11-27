module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (CheckedChunk FramedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1
open Silmaril.Numeric.Timestamp (Ticks)

private theorem isPlainV1_iff {frame : Parquet.Page.Frame} :
    isPlainV1 frame = true ↔ ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 0 := by
  cases kind : frame.value.kind <;> simp [isPlainV1, kind]

theorem profile_fallback_iff {frames : List Parquet.Page.Frame} :
    profile frames = .fallback ↔
      ∃ frame ∈ frames, ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 0 := by
  have choice : profile frames = .fallback ↔ frames.any isPlainV1 = true := by
    by_cases any : frames.any isPlainV1 <;> simp [profile, any]
  rw [choice, List.any_eq_true]
  simp only [isPlainV1_iff]

private theorem planGroup_source {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    Leaf.Dictionary.frameGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index =
      .ok plan.framed ∧ profile plan.framed.data = plan.choice := by
  cases source : Leaf.Dictionary.frameGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index with
  | error cause => simp [planGroup, source, Except.map] at planned
  | ok framed =>
    simp [planGroup, source, Except.map] at planned
    subst plan
    exact ⟨rfl, rfl⟩

theorem planGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.choice = .fallback ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV1 header ∧ header.encoding = 0) := by
  obtain ⟨source, choice⟩ := planGroup_source planned
  obtain ⟨selected, cap, wire, chain, dictionary, data⟩ := Leaf.Dictionary.frameGroupUsing_wire source
  exact ⟨selected, cap, wire, chain, dictionary, data, by rw [← choice, profile_fallback_iff]⟩

theorem readGroup_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      match plan.choice with
      | .dictionary => Leaf.Dictionary.Gzip.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Gzip.readGroup limits leafLimits bound index := by
  obtain ⟨framed, _⟩ := planGroup_source planned
  cases chosen : plan.choice <;>
    simp [readGroup, planned, chosen, Leaf.Dictionary.Gzip.readGroup, Leaf.Dictionary.Gzip.checkGroup,
      Leaf.Fallback.Gzip.readGroup, Leaf.Fallback.Gzip.checkGroup, Leaf.Dictionary.checkGroupUsing,
      framed, Bind.bind, Except.bind]

theorem framing_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Gzip.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Gzip.readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, planGroup, failed, Leaf.Dictionary.Gzip.readGroup, Leaf.Dictionary.Gzip.checkGroup,
    Leaf.Fallback.Gzip.readGroup, Leaf.Fallback.Gzip.checkGroup, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.Snappy.readGroupUsing, Leaf.Fallback.Snappy.readGroupUsing,
    Except.map, Bind.bind, Except.bind]

private theorem sameFrames {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} {checked : CheckedChunk}
    (planned : planGroup limits leafLimits bound index = .ok plan)
    (selected : selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok checked.chunk)
    (framed : Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames) :
    checked.frames = plan.framed.frames := by
  obtain ⟨source, _⟩ := planGroup_source planned
  obtain ⟨same, _, frames, _, _, _⟩ := Leaf.Dictionary.frameGroupUsing_wire source
  have chunk := Except.ok.inj (selected.symm.trans same)
  rw [chunk] at framed
  exact Except.ok.inj (framed.symm.trans frames)

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} {slots : Slots bound}
    (planned : planGroup limits leafLimits bound index = .ok plan)
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages,
      (match plan.choice with
       | .dictionary => Leaf.Dictionary.Gzip.checkGroup limits leafLimits bound index
       | .fallback => Leaf.Fallback.Gzip.checkGroup limits leafLimits bound index) = .ok checked ∧
      checked.frames = plan.framed.frames ∧
      Leaf.Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      List.Forall₂ (fun page raw =>
        match plan.choice with
        | .dictionary => Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
            bound checked.entries.toArray page raw
        | .fallback => Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
            bound checked.entries.toArray page raw) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  rw [readGroup_matches planned] at read
  cases chosen : plan.choice with
  | dictionary =>
    rw [chosen] at read
    obtain ⟨checked, pages, admitted, decoded, ticks, rows⟩ := Leaf.Dictionary.Gzip.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _⟩ := Leaf.Dictionary.Gzip.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ticks, rows⟩
  | fallback =>
    rw [chosen] at read
    obtain ⟨checked, pages, admitted, decoded, ticks, rows⟩ := Leaf.Fallback.Gzip.readGroup_wire read
    obtain ⟨selected, _, _, framed, _, _, _, entries, _, _, _⟩ := Leaf.Fallback.Gzip.checkGroup_wire admitted
    exact ⟨checked, pages, admitted, sameFrames planned selected framed, entries, decoded, ticks, rows⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1

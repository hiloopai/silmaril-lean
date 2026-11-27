module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1
open Silmaril.Numeric.Timestamp (Ticks)

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ admits info.encoding = true ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.snappy.id, info.encoding, .v1
          (DictionaryChunk.Internal.levelTag bound.levels.maxDefinition info.definitionLevelEncoding)
          (DictionaryChunk.Internal.levelTag bound.levels.maxRepetition info.repetitionLevelEncoding)⟩ := by
  cases kind : frame.value.kind with
  | dataV1 info =>
    cases checked : Leaf.Dictionary.Snappy.planDataWith admits bound frame with
    | error cause => simp [planDataWith, kind, checked, Bind.bind, Except.bind] at planned
    | ok original =>
      obtain ⟨source, params, encoding⟩ := Leaf.Dictionary.Snappy.planDataWith_wire checked
      unfold Timestamp.Page.parameters at params
      split at params
      · simp only [kind, Except.ok.injEq] at params
        have tag : admits info.encoding = true := by simpa [← params] using encoding
        simp only [planDataWith, kind, checked, Bind.bind, Except.bind, Except.ok.injEq,
          pure, Except.pure] at planned
        subst page
        exact ⟨source, info, rfl, tag, by simp [← params]⟩
      · contradiction
  | dataV2 _ | dictionary _ | skipped _ => simp [planDataWith, kind, Bind.bind, Except.bind] at planned

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ info.encoding = 2 ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.snappy.id, 2, .v1
          (DictionaryChunk.Internal.levelTag bound.levels.maxDefinition info.definitionLevelEncoding)
          (DictionaryChunk.Internal.levelTag bound.levels.maxRepetition info.repetitionLevelEncoding)⟩ := by
  obtain ⟨same, info, kind, tag, params⟩ := planDataWith_wire (admits := (· == 2)) planned
  have encoding : info.encoding = 2 := by simpa using tag
  exact ⟨same, info, kind, encoding, by simpa [encoding] using params⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyLegacyDictionaryV1 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Snappy.readEntriesWith .plainDictionary limits leafLimits bound checked.dictionary =
        .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, entries, plans, _, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (plan := planData bound)
      (fun plan => (planData_wire plan).1) admitted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, frames, chain, dictionary, first, entries, plans, rows⟩

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Dictionary.Snappy.DataWire limits leafLimits bound checked.entries.toArray)
        checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ :=
    Leaf.Dictionary.Snappy.readGroupUsing_wire read
  obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  refine ⟨checked, pages, admitted, decoded, ?_, count.trans rows⟩
  rw [mapped, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot <;> rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1

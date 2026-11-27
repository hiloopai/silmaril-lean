module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip
open Silmaril.Numeric.Timestamp (Ticks)

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV1 info ∧ (info.encoding = 8 ∨ info.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.gzip.id, info.encoding,
        .v1 info.definitionLevelEncoding info.repetitionLevelEncoding⟩ := by
  obtain ⟨same, info, kind, tag, params⟩ :=
    Leaf.Dictionary.Gzip.planDataWith_wire (admits := Leaf.Fallback.admits) planned
  exact ⟨same, info, kind, by simpa [Leaf.Fallback.admits] using tag, params⟩

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, entries, plans, phase, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (plan := planData bound)
      (fun plan => (planData_wire plan).1) admitted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, frames, chain, dictionary, first, entries, plans, Leaf.Fallback.checkSequence_wire phase, rows⟩

theorem plain_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (plain : page.params.encoding = 0)
    (read : Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits) bound entries page slots) :
    ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ words,
      Leaf.Dictionary.Gzip.StoredMember bound page.frame leafLimits.page.compressedBytes
        leafLimits.page.uncompressedBytes expanded ∧
      FlatPage.split layout leafLimits.page.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues leafLimits.page.levels sections.definitions = .ok prepared.mask ∧
      prepared.scalars = sections.scalars ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨_, verified, _, reference | physical⟩ := read
  · simp [plain] at reference
  · obtain ⟨prepared, words, preparedOk, decoded, mask, signed, _, _⟩ :=
      ScalarPage.decode_sound physical.2
    obtain ⟨expanded, layout, sections, member, split, definition, scalar⟩ :=
      Leaf.Dictionary.Gzip.prepared_member (admits := Leaf.Fallback.admits) planned verified preparedOk
    exact ⟨expanded, layout, sections, prepared, words, member, split, definition, scalar, decoded, mask, signed⟩

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
        bound checked.entries.toArray) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  have order {checked} (admitted : checkGroup limits leafLimits bound index = .ok checked) :
      Leaf.Fallback.Ordered checked.data := by
    obtain ⟨_, _, _, _, _, _, _, _, _, phase, _⟩ := checkGroup_wire admitted
    exact phase
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ :=
    Leaf.Fallback.Snappy.readGroupUsing_wire order read
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  refine ⟨checked, pages, admitted, decoded, ?_, count.trans rows⟩
  rw [mapped, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot <;> rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip

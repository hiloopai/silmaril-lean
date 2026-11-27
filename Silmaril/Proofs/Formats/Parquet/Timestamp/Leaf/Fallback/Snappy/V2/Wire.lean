module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2
open Silmaril.Numeric.Timestamp (Ticks)

theorem planData_wire {bound : Bound} {frame : Parquet.Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ info, frame.value.kind = .dataV2 info ∧ (info.encoding = 8 ∨ info.encoding = 0) ∧
      page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.snappy.id, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes (some info.isCompressed)⟩ := by
  obtain ⟨same, info, kind, tag, params⟩ :=
    Leaf.Dictionary.Snappy.V2.planDataWith_wire (admits := Leaf.Fallback.admits) planned
  exact ⟨same, info, kind, by simpa [Leaf.Fallback.admits] using tag, params⟩

theorem checkGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk}
    (admitted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .snappyDictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Leaf.Dictionary.Snappy.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, planData bound page.frame = .ok page) ∧
      Leaf.Fallback.Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat := by
  obtain ⟨selected, cap, frames, chain, dictionary, first, entries, plans, phase, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (plan := planData bound)
      (fun plan => (planData_wire plan).1) admitted
  obtain ⟨_, _, _, _, _, codec, _, _, _, _⟩ := Leaf.selectChunkWith_sound selected
  exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
    cap, frames, chain, dictionary, first, entries, plans, Leaf.Fallback.checkSequence_wire phase, rows⟩

theorem checkGroup_no_reentry {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {checked : CheckedChunk} {i j : Nat} {a b : DataPage}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (earlier : checked.data[i]? = some a) (later : checked.data[j]? = some b)
    (before : i < j) (plain : a.params.encoding = 0) : b.params.encoding = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ordered, _⟩ := checkGroup_wire admitted
  obtain ⟨refs, suffix, sequence, _, _, refTags, plainTags⟩ := ordered
  rw [sequence] at earlier later
  have past : refs.length ≤ i := by
    by_contra! shorter
    rw [List.getElem?_append_left shorter] at earlier
    have tag := refTags a (List.mem_of_getElem? earlier)
    omega
  rw [List.getElem?_append_right (by omega : refs.length ≤ j)] at later
  exact plainTags b (List.mem_of_getElem? later)

theorem readGroup_first_header_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {framed : Leaf.Dictionary.FramedChunk} {frame : Parquet.Page.Frame}
    {before after : List (Parquet.Page.Frame × Nat)} {pages : List DataPage} {cause : Leaf.DictionaryPageError}
    (framedOk : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index = .ok framed)
    (split : framed.data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) = .ok pages)
    (failed : planData bound frame = .error cause) :
    readGroup limits leafLimits bound index = .error (.dictionaryPage ordinal frame.header.start cause) := by
  have rejected : (framed.data.zipIdx 1).mapM (fun (item, i) =>
      (planData bound item).mapError (Leaf.Dictionary.atFrame i item)) =
      .error (.dictionaryPage ordinal frame.header.start cause) := by
    rw [split, List.mapM_append, earlier]
    simp [failed, Leaf.Dictionary.atFrame, Except.mapError, Bind.bind, Except.bind]
  simp [readGroup, checkGroup, Leaf.Fallback.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.checkFramedUsing, framedOk, rejected, Bind.bind, Except.bind]

theorem readGroup_phase_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {framed : Leaf.Dictionary.FramedChunk} {pages : List DataPage} {cause : Leaf.Error}
    (framedOk : Leaf.Dictionary.frameGroupUsing .snappyDictionary limits leafLimits bound index = .ok framed)
    (planned : (framed.data.zipIdx 1).mapM (fun (frame, ordinal) =>
      (planData bound frame).mapError (Leaf.Dictionary.atFrame ordinal frame)) = .ok pages)
    (failed : Leaf.Fallback.checkSequence pages = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, checkGroup, Leaf.Fallback.Snappy.readGroupUsing, Leaf.Dictionary.checkGroupUsing,
    Leaf.Dictionary.checkFramedUsing, framedOk, planned, failed, Bind.bind, Except.bind]

theorem plain_decodes {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {slots : List (Option Int64)}
    (planned : planData bound page.frame = .ok page) (plain : page.params.encoding = 0)
    (read : Leaf.Fallback.Snappy.DataWire limits leafLimits bound entries page slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ words,
      page.frame.value.kind = .dataV2 header ∧ header.numRows = header.numValues ∧
      Leaf.Dictionary.Snappy.V2.BodyWire bound page.frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨status, layout, prepared, words, verified, expandedBound, wire, decoded, mask, signed⟩ :=
    Leaf.Fallback.Snappy.plain_decodes plain read
  obtain ⟨header, definitions, storedValues, kind, rows, body, readMask, present⟩ :=
    Leaf.Dictionary.Snappy.V2.body_wire (admits := Leaf.Fallback.admits) planned verified expandedBound wire
  exact ⟨header, layout, definitions, storedValues, prepared, words,
    kind, rows, body, readMask, present, decoded, mask, signed⟩

theorem readGroup_wire {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (Leaf.Fallback.Snappy.DataWire limits leafLimits
        bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat := by
  have order {checked} (admitted : checkGroup limits leafLimits bound index = .ok checked) :
      Leaf.Fallback.Ordered checked.data := by
    obtain ⟨_, _, _, _, _, _, _, _, _, phase, _⟩ := checkGroup_wire admitted
    exact phase
  obtain ⟨checked, pages, admitted, decoded, mapped, count⟩ :=
    Leaf.Fallback.Snappy.readGroupUsing_wire order read
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire admitted
  refine ⟨checked, pages, admitted, decoded, mapped, ?_, count.trans rows⟩
  rw [mapped, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot <;> rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.V2

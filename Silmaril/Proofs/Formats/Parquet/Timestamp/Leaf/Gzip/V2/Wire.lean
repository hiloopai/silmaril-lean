module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunkWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits leafLimits bound index = .ok group) :
    selectChunkWith .gzipPlainV2 leafLimits bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      group.chunk.span.stop - group.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset := by
  unfold checkGroup at checked
  obtain ⟨chunk, selected, checked⟩ := bind_ok checked
  by_cases cap : limits.dictionary.maxChunkBytes < chunk.span.stop - chunk.span.start
  · simp [cap, Bind.bind, Except.bind] at checked
  · simp only [cap, ↓reduceIte] at checked
    obtain ⟨frames, framed, checked⟩ := bind_ok checked
    have wire := mapError_ok framed
    by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat
    · simp [rows, pure, Except.pure] at checked
      subst group
      obtain ⟨_, _, _, _, _, codec, metadata, _, span, _⟩ := Leaf.selectChunkWith_sound selected
      have noDictionary := Leaf.ChunkEncoding.gzipPlainV2_noDictionary metadata
      have offset := Footer.checkDataSpan_some_iff.mp (by
        simpa [Parquet.Page.columnSpan, noDictionary] using span)
      exact ⟨selected, by simpa [Leaf.ChunkEncoding.admitsCodec, Payload.Codec.id] using codec,
        Nat.le_of_not_gt cap, wire, (Parquet.Page.readChunk_chain wire).2.2, rows, noDictionary, offset.1⟩
    · simp [rows, Bind.bind, Except.bind] at checked

theorem decodePage_wire {limits : ScalarPage.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)} (read : decodePage limits bound frame ordinal = .ok slots) :
    PageWire limits bound frame slots := by
  unfold decodePage at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨page, admitted, read⟩ := bind_ok read
  have plan := mapError_ok admitted
  have decoded := mapError_ok read
  obtain ⟨same, header, kind, _, params⟩ := Leaf.Dictionary.Gzip.V2.planDataWith_wire plan
  have count := (ScalarPage.decode_counts decoded).1
  exact ⟨page, status, plan, same, mapError_ok verified, decoded,
    by simpa [Leaf.Internal.pageSlots, kind, params] using count⟩

theorem pageWire_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire (limits.withFuel leafLimits).page bound frame slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ words,
      frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧ header.numRows = header.numValues ∧
      Leaf.Dictionary.Gzip.V2.BodyWire bound frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨page, status, plan, rfl, verified, decoded, _⟩ := wire
  obtain ⟨_, header, kind, tag, _⟩ := Leaf.Dictionary.Gzip.V2.planDataWith_wire plan
  obtain ⟨prepared, words, preparedOk, values, mask, signed, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨original, layout, definitions, stored, originalKind, rows, body, readMask, present⟩ :=
    Leaf.Dictionary.Gzip.V2.prepared_wire (limits := limits) (leafLimits := leafLimits) plan verified preparedOk
  have same : header = original := by simpa using kind.symm.trans originalKind
  subst original
  exact ⟨header, layout, definitions, stored, prepared, words, kind, by simpa using tag,
    rows, body, readMask, present, values, mask, signed⟩

theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ group pages, checkGroup limits leafLimits bound index = .ok group ∧
      List.Forall₂ (PageWire (limits.withFuel leafLimits).page bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨group, checked, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (PageWire (limits.withFuel leafLimits).page bound) group.frames pages := by
    rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => decodePage_wire read
  have counts : pages.map List.length = group.frames.map Leaf.Internal.pageSlots := by
    clear read checked decoded
    generalize group.frames = frames at raw ⊢
    induction raw with
    | nil => rfl
    | cons head _ ih =>
      obtain ⟨_, _, _, _, _, _, count⟩ := head
      exact congrArg₂ List.cons count ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨group, pages, checked, raw, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · rw [mapped, List.length_map, List.length_flatten, counts, (checkGroup_wire checked).2.2.2.2.2.1]

theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits leafLimits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage (limits.withFuel leafLimits).page bound item i) = .ok outputs)
    (failed : decodePage (limits.withFuel leafLimits).page bound frame ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, checked, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2

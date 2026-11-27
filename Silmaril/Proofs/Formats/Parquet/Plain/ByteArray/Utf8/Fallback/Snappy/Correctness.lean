module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy
open Silmaril.Formats.Arrow.MixedFlat

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem map_present (slots : List (Option String)) :
    (slots.map (Option.map Utf8.Dictionary.octets)).filterMap id =
      (slots.filterMap id).map Utf8.Dictionary.octets := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => cases slot <;> simp [ih]

theorem decodePlainBytes_wire {limits : Utf8.Fallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePlainBytes limits metadata source frame = .ok slots) : PlainBytesWire limits source frame slots := by
  unfold decodePlainBytes at read
  split at read <;> try contradiction
  rename_i params original
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i expanded
  obtain ⟨status, verified, read⟩ := bind_ok read
  have decoded := mapError_ok read
  obtain ⟨page, values, prepared, plain, mask, present, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, validated, wire⟩ := ScalarPage.prepare_sound prepared
  have rawRead : Plain.ByteArray.decode (plainLimits limits) (page.mask.count true) page.scalars = .ok values := plain
  obtain ⟨_, exactPlain, _, _⟩ := Plain.ByteArray.decode_ok_iff.mp rawRead
  have count : slots.length = ByteArrayFallback.declaredSlots frame := by
    have exactCount := (ScalarPage.decode_counts decoded).1
    unfold ByteArrayFallback.declaredSlots
    cases kind : frame.value.kind <;>
      simp [FlatColumn.pageParameters, kind] at original ⊢ <;> subst params <;> exact exactCount
  exact ⟨params, layout, page, original, Utf8.Dictionary.Snappy.stored_wire (mapError_ok verified),
    Nat.le_of_not_gt expanded, validated, wire, mask, exactPlain.trans (congrArg Plain.ByteArray.wire present).symm,
    count⟩

theorem decodePlain_wire {limits : Utf8.Fallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option String)}
    (read : decodePlain limits metadata source frame = .ok slots) : PlainPageWire limits source frame slots := by
  unfold decodePlain at read
  obtain ⟨raw, physical, read⟩ := bind_ok read
  have octets : slots.map (Option.map Utf8.Dictionary.octets) = raw :=
    Utf8.decodeSlotsWith_exact (mapError_ok read)
  obtain ⟨params, layout, page, original, stored, expanded, valid, wire, mask, exactPlain, count⟩ :=
    decodePlainBytes_wire physical
  refine ⟨params, layout, page, original, stored, expanded, valid, wire, ?_, ?_, ?_⟩
  · simpa [← octets, List.map_map, Function.comp_def] using mask
  · rw [← octets, map_present] at exactPlain
    exact exactPlain
  · simpa [← octets] using count

theorem decodeData_wire {limits : Utf8.Fallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array String)} {frame : Page.Frame} {slots : List (Option String)}
    (read : decodeData limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  cases dictionary with
  | none => contradiction
  | some entries =>
    simp only [decodeData] at read
    split at read <;> try contradiction
    · rename_i tag
      obtain ⟨original, bound, wire⟩ := Utf8.Dictionary.Snappy.decodePage_wire (mapError_ok read)
      cases bound
      exact ⟨entries, rfl, .inl ⟨tag, wire⟩⟩
    · rename_i tag
      exact ⟨entries, rfl, .inr ⟨tag, decodePlain_wire read⟩⟩

private theorem pages_count {limits : Utf8.Fallback.Snappy.Limits} {source : Bytes}
    {entries : Array String} {frames : List Page.Frame} {pages : List (List (Option String))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    have count := match wire with
    | .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    | .inr ⟨_, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    simp [count, ih]

private theorem readFrames_wire {limits : Utf8.Fallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option String)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  have ⟨fits, size⟩ := Utf8.Dictionary.Snappy.checkExpandedChunk_wire checked
  refine ⟨fits, size, ?_⟩
  cases split : ByteArrayFallback.splitLeading frames with
  | mk leading originalData =>
    simp only [split] at read
    obtain ⟨_, phaseCheck, read⟩ := bind_ok read
    have schedule := Utf8.Fallback.checkPhasesWith_wire phaseCheck
    obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, opened, ordered, flatten⟩ :=
      ByteArrayFallback.readFramesWith_wire read
    cases dictionary with
    | none =>
      cases opened
      cases data with
      | nil => simp at dataAt
      | cons frame rest =>
        cases ordered with
        | cons first _ =>
          obtain ⟨_, impossible, _⟩ := decodeData_wire first
          contradiction
    | some frame =>
      obtain ⟨text, parsed, opened⟩ := bind_ok opened
      cases opened
      have dictionaryWire := Utf8.Dictionary.Snappy.readDictionary_wire (mapError_ok parsed)
      have sameData : data = originalData := by
        obtain ⟨_, _, kind, _⟩ := dictionaryWire
        rw [order] at split
        simpa [ByteArrayFallback.splitLeading, kind] using congrArg Prod.snd split
      have pagesWire : List.Forall₂ (PageWire limits source text) data pages :=
        ordered.imp (fun _ _ decoded => by
          obtain ⟨_, eq, wire⟩ := decodeData_wire decoded
          cases eq
          exact wire)
      exact ⟨frame, data, text, pages, order, dictionaryAt.symm, dataAt, dictionaryWire,
        sameData.symm ▸ schedule, pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Utf8.Fallback.Snappy.Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Utf8.Fallback.Snappy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Utf8.Dictionary.openFile parquet.toLimits input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : Utf8.Dictionary.openFile parquet.toLimits input name with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases read : (List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked) with
    | error cause => simp [convert, opened, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      have emitted : OrderedWriter.emit ipc (Utf8.fields name .optional)
          (groups.map (Utf8.batch name .optional)) = .ok wire := by
        cases h : OrderedWriter.emit ipc (Utf8.fields name .optional) (groups.map (Utf8.batch name .optional)) <;>
          simp_all [convert, Except.mapError, Bind.bind, Except.bind]
      obtain ⟨decoded, observed, schema, values, framing⟩ := OrderedWriter.emit_readback emitted
      refine ⟨checked, groups, decoded, rfl, (List.mapM_eq_ok_iff_forall₂.mp read).imp
        (fun _ _ group => readGroup_wire group), observed, schema, ?_, framing⟩
      simpa [List.map_map, Function.comp_def, Utf8.batch, OrderedWriter.BatchInput.observe,
        OrderedWriter.Column.field, OrderedWriter.Column.observe] using values

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy

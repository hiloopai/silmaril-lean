module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary
open Silmaril.Formats.Arrow.MixedFlat

private theorem entry_exact {entry : Bytes × Nat} {text : String}
    (h : decodeEntry entry = .ok text) : octets text = entry.1 := by
  rcases entry with ⟨bytes, index⟩
  by_cases valid : bytes.data.IsValidUTF8
  · have same : String.fromUTF8 bytes.data valid = text := by
      simpa [decodeEntry, String.fromUTF8?, valid] using h
    subst text
    cases bytes
    rfl
  · simp [decodeEntry, String.fromUTF8?, valid] at h

theorem decodeEntries_exact {raw : List Bytes} {text : List String}
    (h : raw.zipIdx.mapM decodeEntry = .ok text) : text.map octets = raw := by
  have reads := (List.mapM_eq_ok_iff_forall₂.mp h).flip.imp (fun _ _ h => entry_exact h)
  have same : List.Forall₂ (· = ·) (text.map octets) (raw.zipIdx.map Prod.fst) :=
    List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr reads)
  rwa [List.forall₂_eq_eq_eq, List.zipIdx_map_fst] at same

theorem readDictionary_wire {limits : Utf8.Dictionary.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {text : Array String}
    (read : readDictionary limits metadata source frame = .ok text) : DictionaryWire limits source frame text := by
  cases physical : ByteArrayFallback.readDictionary limits metadata source frame with
  | error cause => simp [readDictionary, physical, Except.mapError, Bind.bind, Except.bind] at read
  | ok raw =>
    cases strict : raw.toList.zipIdx.mapM decodeEntry with
    | error cause => simp [readDictionary, physical, strict, Except.mapError, Bind.bind, Except.bind] at read
    | ok texts =>
      have output : texts.toArray = text := by
        simpa [readDictionary, physical, strict, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using read
      have exactBytes : text.map octets = raw := by
        apply Array.toList_inj.mp
        simp [← output, decodeEntries_exact strict]
      unfold DictionaryWire
      rw [exactBytes]
      exact ByteArrayFallback.readDictionary_wire physical

theorem decodePage_wire {limits : Utf8.Dictionary.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array String)} {frame : Page.Frame} {text : List (Option String)}
    (read : decodePage limits metadata source dictionary frame = .ok text) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame text := by
  unfold decodePage at read
  cases bounded : ByteArrayFallback.bodyLimits limits.file.column.maxPageBytes frame.value with
  | error cause => simp [bounded, Except.mapError, Bind.bind, Except.bind] at read
  | ok validated =>
    simp only [bounded, Except.mapError, Bind.bind, Except.bind] at read
    split at read <;> try contradiction
    rename_i params original
    split at read <;> try contradiction
    rename_i tag
    have encoding : params.encoding = 8 := Decidable.not_not.mp tag
    split at read <;> try contradiction
    split at read <;> try contradiction
    cases dictionary with
    | none => contradiction
    | some entries =>
      dsimp only at read
      cases decoded : DictionaryIndex.decode entries params limits.file.scalar limits.indices
          (FlatColumn.frameBody source frame) with
      | error cause => simp [decoded] at read
      | ok slots =>
        have same : slots = text := by simpa [decoded] using read
        subst slots
        obtain ⟨_, page, indices, prepared, parsed, mask, lookedUp⟩ := DictionaryIndex.decode_ok_iff.mp decoded
        obtain ⟨layout, valid, exact⟩ := ScalarPage.prepareFor_sound prepared
        have rawLookups := congrArg (List.map (Option.map octets)) lookedUp
        simp only [List.map_map, Function.comp_def, Option.map_some] at rawLookups
        refine ⟨entries, rfl, params, layout, page, indices, original, encoding, ?_, exact, parsed,
          lookedUp, ?_, mask, ?_⟩
        · simpa [encoding] using valid
        · simpa only [Array.getElem?_map, Function.comp_def] using rawLookups
        · simpa [ByteArrayFallback.declaredSlots, original] using (DictionaryIndex.decode_counts decoded).1

private theorem pages_count {limits : Utf8.Dictionary.Limits} {source : Bytes} {entries : Array String}
    {data : List Page.Frame} {pages : List (List (Option String))}
    (ordered : List.Forall₂ (PageWire limits source entries) data pages) :
    pages.flatten.length = (data.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
    simp [count, ih]

private theorem readFrames_wire {limits : Utf8.Dictionary.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option String)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, leading, ordered, flatten⟩ :=
    ByteArrayFallback.readFramesWith_wire read
  cases dictionary with
  | none =>
    cases leading
    cases data with
    | nil => simp at dataAt
    | cons frame rest =>
      cases ordered with
      | cons readPage tail =>
        obtain ⟨entries, impossible, _⟩ := decodePage_wire readPage
        contradiction
  | some frame =>
    cases h : readDictionary limits metadata source frame with
    | error cause => simp [Option.mapM, h] at leading
    | ok text =>
      have bound : entries = some text := by
        simpa [Option.mapM, h, Bind.bind, Except.bind, Pure.pure, Except.pure] using leading.symm
      subst entries
      have pagesWire : List.Forall₂ (PageWire limits source text) data pages :=
        ordered.imp (fun _ _ readPage => by
          obtain ⟨entries, same, wire⟩ := decodePage_wire readPage
          cases same
          exact wire)
      exact ⟨frame, data, text, pages, order, dictionaryAt.symm, dataAt, readDictionary_wire h,
        pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Utf8.Dictionary.Limits} {name : String} {checked : Checked name} {index : Nat}
    {text : List (Option String)} (read : readGroup parquet checked index = .ok text) :
    ∃ group, GroupWire parquet checked index group text := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, decoded⟩ := ByteArrayFallback.readBoundGroupWith_wire read
  exact ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, readFrames_wire decoded⟩

theorem convert_readback {parquet : Utf8.Dictionary.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : openFile parquet input name with
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

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary

module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy
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

theorem stored_wire {cap : Nat} {source : Bytes} {frame : Page.Frame} {status : Page.Checksum.Status}
    (verified : Page.Checksum.verify cap source frame = .ok status) : StoredWire cap source frame := by
  have ⟨bound, extent⟩ : frame.value.compressedSize ≤ cap ∧ Page.Checksum.PayloadWithin source frame := by
    cases status with
    | absent => exact ⟨(Page.Checksum.verify_absent_iff.mp verified).1,
        (Page.Checksum.verify_absent_iff.mp verified).2.1⟩
    | valid _ => exact ⟨(Page.Checksum.verify_valid_iff.mp verified).1,
        (Page.Checksum.verify_valid_iff.mp verified).2.1⟩
  have ⟨origin, exactLength⟩ := Page.Checksum.payload_exact extent
  exact ⟨⟨status, verified⟩, origin, exactLength, bound⟩

theorem readDictionaryBytes_wire {limits : Utf8.Dictionary.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : List Bytes}
    (read : readDictionaryBytes limits metadata source frame = .ok entries) : DictionaryBytesWire limits source frame entries := by
  unfold readDictionaryBytes at read
  split at read <;> try contradiction
  rename_i header original
  split at read <;> try contradiction
  rename_i tag
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i count
  dsimp only at read
  split at read <;> try contradiction
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨expanded, physical, read⟩ := bind_ok read
  obtain ⟨codec, matched, expansion, _, _, length, cap⟩ := Payload.decode_sound (mapError_ok physical)
  have selected := Option.some.inj ((Payload.Codec.ofId_id .snappy).symm.trans matched)
  subst codec
  obtain ⟨_, bytes, entriesCount, _⟩ := Plain.ByteArray.decode_ok_iff.mp (mapError_ok read)
  exact ⟨header, expanded, original, Decidable.not_not.mp tag, Nat.le_of_not_gt count,
    stored_wire (mapError_ok verified), expansion, length, cap, by simpa using bytes, entriesCount⟩

theorem readDictionary_wire {limits : Utf8.Dictionary.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : Array String}
    (read : readDictionary limits metadata source frame = .ok entries) : DictionaryWire limits source frame entries := by
  unfold readDictionary at read
  obtain ⟨raw, parsed, read⟩ := bind_ok read
  obtain ⟨text, strict, read⟩ := bind_ok read
  obtain ⟨header, expanded, original, tag, count, stored, expansion, length, cap, bytes, entriesCount⟩ :=
    readDictionaryBytes_wire parsed
  have octets := Utf8.Dictionary.decodeEntries_exact (mapError_ok strict)
  cases read
  refine ⟨header, expanded, original, tag, count, stored, expansion, length, cap, ?_, ?_⟩
  · simpa [octets] using bytes
  · have sizes := congrArg List.length octets
    simp only [List.length_map] at sizes
    simpa using sizes.trans entriesCount

theorem decodeIndexPage_wire {α : Type} {limits : Utf8.Dictionary.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array α)} {frame : Page.Frame} {text : List (Option α)}
    (read : decodeIndexPage limits metadata source dictionary frame = .ok text) :
    ∃ entries, dictionary = some entries ∧ IndexPageWire limits source entries frame text := by
  unfold decodeIndexPage at read
  split at read <;> try contradiction
  rename_i params original
  dsimp only at read
  split at read <;> try contradiction
  rename_i tag
  have encoding : params.encoding = 8 := Decidable.not_not.mp tag
  split at read <;> try contradiction
  split at read <;> try contradiction
  cases dictionary with
  | none => contradiction
  | some entries =>
    dsimp only at read
    split at read <;> try contradiction
    rename_i expanded
    obtain ⟨status, verified, read⟩ := bind_ok read
    have decoded := mapError_ok read
    obtain ⟨_, page, indices, prepared, parsed, mask, lookedUp⟩ := DictionaryIndex.decode_ok_iff.mp decoded
    obtain ⟨layout, valid, exact⟩ := ScalarPage.prepareFor_sound prepared
    refine ⟨entries, rfl, params, layout, page, indices, original, encoding,
      stored_wire (mapError_ok verified), Nat.le_of_not_gt expanded, ?_, exact, parsed, lookedUp, mask, ?_⟩
    · simpa [encoding] using valid
    · have count := (DictionaryIndex.decode_counts decoded).1
      unfold ByteArrayFallback.declaredSlots
      cases kind : frame.value.kind <;>
        simp [FlatColumn.pageParameters, kind] at original ⊢ <;> subst params <;> exact count

theorem decodePage_wire {limits : Utf8.Dictionary.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array String)} {frame : Page.Frame} {text : List (Option String)}
    (read : decodePage limits metadata source dictionary frame = .ok text) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame text := by
  obtain ⟨entries, available, params, layout, page, indices, original, encoding, stored, expanded,
    valid, exact, parsed, lookedUp, mask, count⟩ := decodeIndexPage_wire read
  have rawLookups := congrArg (List.map (Option.map Utf8.Dictionary.octets)) lookedUp
  simp only [List.map_map, Function.comp_def, Option.map_some] at rawLookups
  refine ⟨entries, available, params, layout, page, indices, original, encoding, stored, expanded,
    valid, exact, parsed, lookedUp, ?_, mask, count⟩
  simpa only [Array.getElem?_map, Function.comp_def] using rawLookups

private theorem pages_count {limits : Utf8.Dictionary.Snappy.Limits} {source : Bytes} {entries : Array String}
    {data : List Page.Frame} {pages : List (List (Option String))}
    (ordered : List.Forall₂ (PageWire limits source entries) data pages) :
    pages.flatten.length = (data.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
    simp [count, ih]

theorem checkExpandedChunk_wire {ε : Type} {limits : Utf8.Dictionary.Snappy.Limits}
    {metadata : Footer.ColumnMetadata} {group column : Nat} {name : String} {frames : List Page.Frame}
    (checked : checkExpandedChunk (ε := ε) limits metadata group column name frames = .ok ()) :
    expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧ (expandedBytes frames : Int) = metadata.totalUncompressedSize := by
  unfold checkExpandedChunk at checked
  dsimp only at checked
  split at checked <;> try contradiction
  rename_i fits
  split at checked <;> try contradiction
  rename_i size
  exact ⟨Nat.le_of_not_gt fits, Decidable.not_not.mp size⟩

private theorem readFrames_wire {limits : Utf8.Dictionary.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option String)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  have ⟨fits, size⟩ := checkExpandedChunk_wire checked
  refine ⟨fits, size, ?_⟩
  obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, leading, ordered, flatten⟩ :=
    ByteArrayFallback.readFramesWith_wire read
  cases dictionary with
  | none =>
    cases leading
    cases data with
    | nil => simp at dataAt
    | cons frame rest =>
      cases ordered with
      | cons first _ =>
        obtain ⟨_, impossible, _⟩ := decodePage_wire first
        contradiction
  | some frame =>
    obtain ⟨text, parsed, leading⟩ := bind_ok leading
    cases leading
    have pagesWire : List.Forall₂ (PageWire limits source text) data pages :=
      ordered.imp (fun _ _ decoded => by
        obtain ⟨_, eq, wire⟩ := decodePage_wire decoded
        cases eq
        exact wire)
    exact ⟨frame, data, text, pages, order, dictionaryAt.symm, dataAt, readDictionary_wire parsed,
      pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem storedBytes_chain {chunk : Footer.Span} {start stop : Nat} {frames : List Page.Frame}
    (chain : Page.Chain chunk start stop frames) : start ≤ stop ∧ storedBytes frames = stop - start := by
  induction chain with
  | nil cursor => simp [storedBytes]
  | @cons start stop frame rest within _ ih =>
    have header := within.headerStart
    have progress := within.headerProgress
    have adjacent := within.adjacent
    have payload := within.payloadWidth
    have ⟨ordered, exact⟩ := ih
    simp only [storedBytes, List.map_cons, List.sum_cons] at exact ⊢
    omega

theorem storedBytes_exact {limits : Page.Limits} {source : Bytes} {footerStart : Nat}
    {metadata : Footer.ColumnMetadata} {chunk : Footer.Span} {frames : List Page.Frame}
    (located : Page.columnSpan footerStart metadata = some chunk)
    (framed : Page.readChunk limits source chunk = .ok frames) :
    (storedBytes frames : Int) = metadata.totalCompressedSize := by
  have exact := (storedBytes_chain (Page.readChunk_chain framed).2.2).2
  have ⟨starts, stops, _, ordered, _⟩ := Footer.checkDataSpan_some_iff.mp located
  omega

theorem readGroup_wire {parquet : Utf8.Dictionary.Snappy.Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Utf8.Dictionary.Snappy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
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

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy

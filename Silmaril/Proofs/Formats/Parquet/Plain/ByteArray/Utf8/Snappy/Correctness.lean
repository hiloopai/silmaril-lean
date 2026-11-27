module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Snappy
open Silmaril.Formats.Arrow.MixedFlat

variable {parquet : File.Limits} {input : Bytes} {name : String} {layout : FlatColumn.Layout}
variable {checked : Utf8.Checked name layout}

private theorem payload_within {limits : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status} (verified : Page.Checksum.verify limits source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent => exact (Page.Checksum.verify_absent_iff.mp verified).2.1
  | valid _ => exact (Page.Checksum.verify_valid_iff.mp verified).2.1

private theorem sizes_at_header {layout : FlatColumn.Layout} {codec : Int}
    {header : Page.Header} {params : ScalarPage.Parameters}
    (obtained : FlatColumn.pageParameters layout codec header = some params) :
    params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ := by
  unfold FlatColumn.pageParameters at obtained
  split at obtained <;> simp at obtained <;> subst params <;> rfl

private theorem page_caps {limits : File.Limits} {layout : FlatColumn.Layout} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {raw : List (Option Bytes)}
    (wire : File.PageWire limits layout metadata source frame raw) :
    frame.value.compressedSize ≤ limits.column.maxPageBytes ∧
      frame.value.uncompressedSize ≤ limits.column.maxPageBytes := by
  obtain ⟨params, levels, _, _, obtained, validated, _⟩ := wire
  have sizes := sizes_at_header obtained
  simp only [ScalarPage.validate, ScalarPage.validateFor] at validated
  split at validated <;> try contradiction
  split at validated <;> try contradiction
  split at validated <;> try contradiction
  rename_i compressed
  split at validated <;> try contradiction
  rename_i uncompressed
  rw [sizes] at compressed uncompressed
  exact ⟨Nat.le_of_not_gt compressed, Nat.le_of_not_gt uncompressed⟩

theorem page_wire {limits : File.Limits} {layout : FlatColumn.Layout} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {frame : Page.Frame} {text : List (Option String)}
    (wire : FlatColumn.CheckedCallbackWire .snappy limits.column (decodePage limits layout)
      leaf metadata source frame text) : PageWire limits layout metadata source frame text := by
  obtain ⟨⟨status, crc⟩, decoded, count⟩ := wire
  change Page.Checksum.verify limits.column.maxPageBytes source frame = .ok status at crc
  have span := (Page.Checksum.payload_exact (payload_within crc)).1
  cases physical : File.decodePage limits layout leaf metadata frame.value (FlatColumn.frameBody source frame) with
  | error cause => simp [decodePage, physical, Except.mapError, Bind.bind, Except.bind] at decoded
  | ok raw =>
    have strict : Utf8.decodeSlotsWith PageError.invalidText raw = .ok text := by
      simpa [decodePage, physical, Except.mapError, Bind.bind, Except.bind] using decoded
    have bytes := Utf8.decodeSlotsWith_exact strict
    have page := File.decodePage_wire physical
    have caps := page_caps page
    exact ⟨⟨status, crc⟩, span, caps.1, caps.2, count, bytes ▸ page⟩

theorem readGroup_wire {index : Nat} {text : List (Option String)}
    (read : readGroup parquet checked index = .ok text) :
    ∃ group, GroupWire parquet checked index group text := by
  obtain ⟨group, column, span, frames, pages, groupAt, columnAt, path, physical, count,
    codec, located, framed, declared, callbacks, output, rows⟩ := FlatColumn.readColumnFor_checked_wire read
  exact ⟨group, column, span, frames, pages, groupAt, columnAt, path, physical, count, codec, located,
    framed, declared, callbacks.imp (fun _ _ wire => page_wire wire), output, rows⟩

theorem convert_readback {ipc : Arrow.MixedFlat.Limits} {wire : KBytes}
    (written : convert parquet ipc input name layout = .ok wire) :
    ∃ (checked : Utf8.Checked name layout) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Utf8.openFile parquet input name layout = .ok checked ∧
      List.Forall₂ (fun index text => ∃ group, GroupWire parquet checked index group text)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name layout ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, layout == .optional, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : Utf8.openFile parquet input name layout with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases read : (List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked) with
    | error cause => simp [convert, opened, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      have emitted : OrderedWriter.emit ipc (Utf8.fields name layout)
          (groups.map (Utf8.batch name layout)) = .ok wire := by
        cases h : OrderedWriter.emit ipc (Utf8.fields name layout) (groups.map (Utf8.batch name layout)) <;>
          simp_all [convert, Except.mapError, Bind.bind, Except.bind]
      obtain ⟨decoded, observed, schema, values, framing⟩ := OrderedWriter.emit_readback emitted
      refine ⟨checked, groups, decoded, rfl, (List.mapM_eq_ok_iff_forall₂.mp read).imp
        (fun _ _ group => readGroup_wire group), observed, schema, ?_, framing⟩
      simpa [List.map_map, Function.comp_def, Utf8.batch, OrderedWriter.BatchInput.observe,
        OrderedWriter.Column.field, OrderedWriter.Column.observe] using values

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Snappy

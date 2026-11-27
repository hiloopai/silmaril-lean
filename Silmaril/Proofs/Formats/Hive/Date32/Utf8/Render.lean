module

public import Silmaril.Formats.Hive.Date32.Utf8.Render.Defs
import Silmaril.Formats.Hive.Date32.Render.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Silmaril.Formats.Hive.WritePlan.Restore.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8.Render

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32.Utf8
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File (Kind Value)

private theorem convert_encodeField (field : TypedPartitions.Field Kind)
    (value : Value field.kind) (text : String) (encoded : encode field value = .ok text) :
    convert field text = .ok value := by
  rcases field with ⟨name, kind, missing⟩
  cases kind with
  | int32 layout =>
    have printed : Silmaril.Formats.Hive.Date32.encodeText value = .ok text := by
      cases out : Silmaril.Formats.Hive.Date32.encodeText value <;> simp_all [encode, Except.mapError]
    exact (Silmaril.Formats.Hive.Date32.encodeText_ok_iff value text).mp printed
  | byteArray layout =>
    have valid : String.fromUTF8? value.data = some text := by
      cases out : String.fromUTF8? value.data <;> simp_all [encode]
    unfold String.fromUTF8? at valid
    split at valid
    · cases valid
      rfl
    · cases valid

theorem encode_convert_leftInverse (keys : Keys) :
    WritePlan.CellLeftInverse keys.schema encode convert :=
  fun i => convert_encodeField keys.schema.fields[i]

private theorem rendered_entries {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {directory : String}
    (written : renderDirectory options cells = .ok directory) :
    ∃ entries, WritePlan.encodeEntries encode cells = .ok entries ∧
      PartitionPath.render options entries = .ok directory := by
  cases out : WritePlan.encodeEntries encode cells with
  | error cause => simp [renderDirectory, out, Bind.bind, Except.bind] at written
  | ok entries =>
    refine ⟨entries, rfl, ?_⟩
    cases path : PartitionPath.render options entries <;>
      simp_all [renderDirectory, Bind.bind, Except.bind, Except.mapError]

theorem renderDirectory_parse {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {directory : String}
    (written : renderDirectory options cells = .ok directory) :
    ∃ entries, WritePlan.encodeEntries encode cells = .ok entries ∧
      PartitionPath.parse options directory = .ok entries ∧ entries.map Prod.fst = keys.schema.keys := by
  obtain ⟨entries, encoded, rendered⟩ := rendered_entries options cells written
  exact ⟨entries, encoded, PartitionPath.parse_render_of_ok rendered, WritePlan.encodeEntries_keys encode cells encoded⟩

theorem prepareFile_renderDirectory {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {directory path leaf : String}
    (written : renderDirectory options cells = .ok directory)
    (split : Manifest.splitFile path = .ok (directory, leaf)) :
    Manifest.prepareFile keys.schema options convert path = .ok ⟨⟨path, directory, leaf⟩, cells⟩ := by
  obtain ⟨_, encoded, rendered⟩ := rendered_entries options cells written
  have parsed := PartitionPath.parse_render_of_ok rendered
  have decoded := WritePlan.decode_renderedEntries options encode convert (encode_convert_leftInverse keys)
    cells encoded rendered
  simp [Manifest.prepareFile, Manifest.prepareFileWith, Manifest.prepareFileWithFileParser,
    Manifest.DirectoryParser.asFileParser, split, parsed, rendered, decoded, Except.mapError, Except.bind, Except.map]

private theorem renderSegments_first_collision (options : PartitionPath.Options) (entries : PartitionPath.Partition)
    (entry : PartitionPath.Entry)
    (found : entries.find? (fun part => part.2 == some options.nullMarker) = some entry) :
    entries.mapM (PartitionPath.renderSegment options) = .error (.nullMarkerCollision entry.1) := by
  induction entries with
  | nil => cases found
  | cons first rest ih =>
    rcases first with ⟨key, value⟩
    cases hit : (value == some options.nullMarker) with
    | false =>
      have tail := ih (by simpa [List.find?_cons, hit] using found)
      simp [List.mapM_cons, PartitionPath.renderSegment, hit, tail, Bind.bind, Except.bind,
        pure, Pure.pure, Except.pure]
    | true =>
      have same : (key, value) = entry := by simpa [List.find?_cons, hit] using found
      subst entry
      simp [List.mapM_cons, PartitionPath.renderSegment, hit, Bind.bind, Except.bind]
      rfl

theorem renderDirectory_first_markerCollision {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) {entries : PartitionPath.Partition} {entry : PartitionPath.Entry}
    (encoded : WritePlan.encodeEntries encode cells = .ok entries)
    (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options entries = .ok ())
    (found : entries.find? (fun part => part.2 == some options.nullMarker) = some entry) :
    renderDirectory options cells = .error (.render (.nullMarkerCollision entry.1)) := by
  simp [renderDirectory, encoded, PartitionPath.render, marker, valid,
    renderSegments_first_collision options entries entry found, Bind.bind, Except.bind, Except.mapError]

end Silmaril.Proofs.Formats.Hive.Date32.Utf8.Render

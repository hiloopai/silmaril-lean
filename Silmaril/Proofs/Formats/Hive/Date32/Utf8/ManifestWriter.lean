module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Defs
import Silmaril.Formats.Hive.Date32.Utf8.Render.Thms
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Formats.Hive.WritePlan.Restore.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms
import Mathlib.Data.List.Forall2
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32.Utf8
open Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter
open Int32ByteArrayGroup.File (Value)
open WritePlan.FlatInt32 (filePath filename)
open WritePlan.FlatInt32.RowGroups (planCuts)
open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name : Type*}

theorem fileInput_rows (schema : Schema) (sizes : List Nat) (rows : Scan.Table schema.physical Value) :
    (fileInput schema sizes rows).groups.map MixedV1Writer.Multi.Group.rows =
      (WritePlan.FlatInt32.RowGroups.splitSlots sizes rows).map
        (List.map fun row => (row (0 : Fin 2), row (1 : Fin 2))) := by
  have zipped (group : Scan.Table schema.physical Value) :
      (group.map fun row => row (0 : Fin 2)).zip (group.map fun row => row (1 : Fin 2)) =
        group.map fun row => (row (0 : Fin 2), row (1 : Fin 2)) := by
    induction group with
    | nil => rfl
    | cons row rest ih => simp [ih]
  simp [fileInput, MixedV1Writer.Multi.Group.rows, List.map_map, Function.comp_def,
    PlainV1Writer.Input.slots, PlainByteArrayV1Writer.Input.slots]
  exact List.map_congr_left (fun group _ => zipped group)

private theorem emitBucket_ok (schema : Schema) (limits : Limits) (bucket : Bucket schema) (file : File)
    (written : emitBucket schema limits bucket = .ok file) : FileMatches schema limits bucket file := by
  let path := filePath bucket.directory
  cases split : Manifest.splitFile path with
  | error cause => simp [emitBucket, path, split, Bind.bind, Except.bind, Except.mapError] at written
  | ok parts =>
    by_cases same : parts = (bucket.directory, filename)
    · cases cuts : planCuts limits.cuts bucket.rows.length with
      | error cause =>
        simp [emitBucket, path, split, same, cuts, Bind.bind, Except.bind, Except.mapError] at written
      | ok sizes =>
        cases encoded : MixedV1Writer.Multi.emit limits.writer (fileInput schema sizes bucket.rows) with
        | error cause =>
          simp [emitBucket, path, split, same, cuts, encoded, Bind.bind, Except.bind, Except.mapError] at written
        | ok output =>
          have sameFile : (⟨path, sizes, output.bytes⟩ : File) = file := by
            simpa [emitBucket, path, split, same, cuts, encoded, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure] using written
          subst file
          exact ⟨rfl, split.trans (congrArg Except.ok same), cuts, output, encoded, rfl⟩
    · simp [emitBucket, path, split, same, Bind.bind, Except.bind, Except.mapError] at written

private theorem mapM_files (schema : Schema) (limits : Limits) (buckets : List (Bucket schema)) (files : List File)
    (written : buckets.mapM (emitBucket schema limits) = .ok files) :
    List.Forall₂ (FileMatches schema limits) buckets files := by
  induction buckets generalizing files with
  | nil => cases written; exact .nil
  | cons bucket rest ih =>
    cases front : emitBucket schema limits bucket with
    | error cause => simp [List.mapM_cons, front, Bind.bind, Except.bind] at written
    | ok first =>
      cases back : rest.mapM (emitBucket schema limits) with
      | error cause => simp [List.mapM_cons, front, back, Bind.bind, Except.bind] at written
      | ok tail =>
        have same : first :: tail = files := by
          simpa [List.mapM_cons, front, back, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] using written
        subst files
        exact .cons (emitBucket_ok schema limits bucket first front) (ih tail back)

private theorem certify_ok (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (buckets : List (Bucket schema)) (files : List File) (rows : Scan.Table schema.toScan Value)
    (expected : WritePlan.restore schema.physical schema.keys.schema options convert buckets = .ok rows)
    (checked : certify schema options limits buckets files = .ok ()) :
    ∃ trace, readManifest schema options limits files = .ok trace ∧ trace.termination = .eos ∧
      trace.batches.map (·.rowCount) = files.flatMap (·.groupRows) ∧ trace.rows = rows := by
  cases read : readManifest schema options limits files with
  | error cause => simp [certify, expected, read, Bind.bind, Except.bind, Except.mapError] at checked
  | ok trace =>
    by_cases eos : trace.termination = .eos
    · by_cases sizes : trace.batches.map (·.rowCount) = files.flatMap (·.groupRows)
      · by_cases same : trace.rows = rows
        · exact ⟨trace, rfl, eos, sizes, same⟩
        · simp [certify, expected, read, eos, sizes, same, Bind.bind, Except.bind, Except.mapError] at checked
      · simp [certify, expected, read, eos, sizes, Bind.bind, Except.bind, Except.mapError] at checked
    · simp [certify, expected, read, eos, Bind.bind, Except.bind, Except.mapError] at checked

private theorem batchRows_split {schema : Schema} (trace : Events.Trace schema.toScan Value ReadError) :
    trace.batches.map (·.toRows) = (trace.batches.map (·.rowCount)).splitLengths trace.rows := by
  unfold Events.Trace.rows
  induction trace.batches with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.flatMap_cons, List.splitLengths_cons]
    rw [← AlignedColumns.length_toRows head, List.take_left, List.drop_left, ih]

theorem emit_readback (db : Packed Name String Value) (name : Name) (schema : Schema)
    (options : PartitionPath.Options) (limits : Limits) (rows : Scan.Table schema.toScan Value) (files : List File)
    (source : namedRows db name schema = .ok rows) (written : emit db name schema options limits = .ok files) :
    ∃ buckets, WritePlan.reference schema.physical schema.keys.schema options encode rows = .ok buckets ∧
      List.Forall₂ (FileMatches schema limits) buckets files ∧
      ∃ trace, readManifest schema options limits files = .ok trace ∧ trace.termination = .eos ∧
        trace.batches.map (·.rowCount) = files.flatMap (·.groupRows) ∧
        trace.rows = WritePlan.groupOriginalRows options encode rows ∧
        trace.batches.map (·.toRows) =
          (files.flatMap (·.groupRows)).splitLengths (WritePlan.groupOriginalRows options encode rows) := by
  cases names : PartitionPath.validateKeys [schema.intName, schema.byteName] with
  | error cause => simp [emit, source, names, Bind.bind, Except.bind, Except.mapError] at written
  | ok checked =>
    cases checked
    cases route : WritePlan.plan schema.physical schema.keys.schema options encode rows with
    | error cause => simp [emit, source, names, route, Bind.bind, Except.bind, Except.mapError] at written
    | ok buckets =>
      by_cases zero : limits.cuts.rowsPerGroup = 0
      · simp [emit, source, names, route, zero, Bind.bind, Except.bind, Except.mapError] at written
      · cases payloads : buckets.mapM (emitBucket schema limits) with
        | error cause => simp [emit, source, names, route, zero, payloads, Bind.bind, Except.bind, Except.mapError] at written
        | ok ready =>
          cases certified : certify schema options limits buckets ready with
          | error cause =>
            simp [emit, source, names, route, zero, payloads, certified, Bind.bind, Except.bind, Except.mapError] at written
          | ok checked =>
            cases checked
            have same : ready = files := by
              simpa [emit, source, names, route, zero, payloads, certified, Bind.bind, Except.bind, Except.mapError,
                pure, Pure.pure, Except.pure] using written
            subst files
            have restored := WritePlan.restore_plan_eq_groupedRows options encode convert
              (encode_convert_leftInverse schema.keys) rows buckets route
            obtain ⟨trace, read, eos, counts, values⟩ := certify_ok schema options limits buckets ready _ restored certified
            refine ⟨buckets, (WritePlan.plan_eq_reference schema.physical schema.keys.schema options encode rows).symm.trans route,
              mapM_files schema limits buckets ready payloads, trace, read, eos, counts, values, ?_⟩
            rw [← counts, ← values]
            exact batchRows_split trace

end Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter

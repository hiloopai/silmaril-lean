module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs
import Silmaril.Formats.Hive.Manifest.Pruning.Thms
import Silmaril.Formats.Hive.Manifest.Thms
import Silmaril.Formats.Arrow.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32.Utf8
open Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter
open Int32ByteArrayGroup.File (Value)
open TypedPartitions (partitionCells)

private theorem all_eos_of_assemble {α Kind Error : Type*}
    {Cell : Kind → Type*} {output : Scan.Schema String Kind}
    (observe : α → Events.Trace output Cell Error) (items : List α)
    (eos : (ParquetScan.assemble observe items).termination = .eos) :
    ∀ item ∈ items, (observe item).termination = .eos := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    cases headDone : (observe first).termination <;> simp [ParquetScan.assemble, headDone] at eos
    intro item hit
    rcases List.mem_cons.mp hit with rfl | member
    · exact headDone
    · exact ih eos item member

theorem readSelected_eq_postfilter (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (projection : Scan.Projection schema.toScan) (keep : Scan.Predicate schema.keys.schema.toScan Value)
    (files : List File) (full : Events.Trace schema.toScan Value ReadError)
    (read : readManifest schema options limits files = .ok full) (eos : full.termination = .eos) :
    ∃ selected, readSelected schema options limits projection keep files = .ok selected ∧
      selected.rows = projection.scan (fun row => keep (partitionCells row)) full.rows ∧
      selected.termination = .eos := by
  change Scan.Projection (schema.keys.schema.extend
    (Int32ByteArrayGroup.File.schema schema.intField schema.byteField)) at projection
  cases admitted : preparePaths schema.intField schema.byteField schema.keys options (files.map (·.path)) with
  | error cause => simp [readManifest, scanPaths, admitted, Except.map] at read
  | ok prepared =>
    let opener := Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField
      schema.keys.schema (resolve files)
    let idProjection := Scan.Projection.id
      (schema.keys.schema.extend (Int32ByteArrayGroup.File.schema schema.intField schema.byteField))
    have strictFull : Manifest.scan opener idProjection (fun _ => some true) prepared = full := by
      simp only [readManifest, scanPaths, admitted, Except.map] at read
      exact Except.ok.inj read
    have every : ∀ file ∈ prepared,
        (Manifest.scanFile opener idProjection (fun _ => some true) file).termination = .eos :=
      all_eos_of_assemble _ _ (by rw [← strictFull] at eos; exact eos)
    have safe : Manifest.RejectedFilesReachEOF opener projection keep prepared := by
      intro file member _
      exact (Manifest.scanFile_termination_eq_full opener projection keep file).trans (every file member)
    let selected := Manifest.scanSkippingRejected opener projection keep prepared
    refine ⟨selected, ?_, ?_, ?_⟩
    · simp [readSelected, scanSelectedPaths, admitted, selected, opener, Except.map]
    · have obs := Events.EventStream.equivalent_open_iff.mp
        (Manifest.scan_equivalent_thenFilter opener projection keep prepared)
      have strictRows := obs.1
      change _ = ((Manifest.scan opener idProjection (fun _ => some true) prepared).scan
        projection (fun row => keep (partitionCells row))).rows at strictRows
      rw [strictFull] at strictRows
      exact (congrArg Events.Trace.rows (Manifest.scanSkippingRejected_eq_scan opener projection keep prepared safe)).trans
        (strictRows.trans (Events.Trace.rows_scan full projection (fun row => keep (partitionCells row))))
    · have obs := Events.EventStream.equivalent_open_iff.mp
        (Manifest.scan_equivalent_thenFilter opener projection keep prepared)
      have strictTerm := obs.2
      change _ = ((Manifest.scan opener idProjection (fun _ => some true) prepared).scan
        projection (fun row => keep (partitionCells row))).termination at strictTerm
      rw [strictFull] at strictTerm
      exact (congrArg Events.Trace.termination
        (Manifest.scanSkippingRejected_eq_scan opener projection keep prepared safe)).trans (strictTerm.trans eos)

theorem scanSelectedPaths_first_retained_error {Failure : Type} (schema : Schema) (options : PartitionPath.Options)
    (limits : Limits) (lookup : String → Except Failure Bytes) (projection : Scan.Projection schema.toScan)
    (keep : Scan.Predicate schema.keys.schema.toScan Value) (paths : List String)
    (before after : List (Manifest.File schema.keys.schema Value)) (bad : Manifest.File schema.keys.schema Value)
    (cause : Manifest.FileError (Manifest.Int32ByteArray.Error Failure))
    (admitted : preparePaths schema.intField schema.byteField schema.keys options paths = .ok (before ++ bad :: after))
    (selected : (keep bad.cells).getD false = true)
    (exhausted : ∀ file ∈ before, (keep file.cells).getD false = true →
      (Manifest.scanFile (Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField
        schema.keys.schema lookup) projection keep file).termination = .eos)
    (failed : (Manifest.scanFile (Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField
      schema.keys.schema lookup) projection keep bad).termination = .readError cause) :
    let runFile := Manifest.scanFile (Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField
      schema.keys.schema lookup) projection keep
    ∃ trace, scanSelectedPaths schema options limits lookup projection keep paths = .ok trace ∧
      trace.rows = (before.filter fun file => (keep file.cells).getD false).flatMap (fun file => (runFile file).rows) ++
        (runFile bad).rows ∧ trace.termination = .readError cause := by
  change Scan.Projection (schema.keys.schema.extend
    (Int32ByteArrayGroup.File.schema schema.intField schema.byteField)) at projection
  dsimp only
  let opener := Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField schema.keys.schema lookup
  let retained := before.filter fun file => (keep file.cells).getD false
  let runFile := Manifest.scanFile opener projection keep
  let result := Manifest.scan opener projection keep (retained ++ bad :: after.filter fun file => (keep file.cells).getD false)
  have stopped : (runFile bad).termination ≠ .eos := by simp [runFile, opener, failed]
  have prefixOk : ∀ file ∈ retained, (runFile file).termination = .eos := by
    intro file hit
    obtain ⟨member, keepFile⟩ := List.mem_filter.mp hit
    exact exhausted file member keepFile
  have exactPrefix := Manifest.scan_first_terminal opener projection keep retained bad
    (after.filter fun file => (keep file.cells).getD false) prefixOk stopped
  refine ⟨result, ?_, exactPrefix.1, exactPrefix.2.trans failed⟩
  simp only [scanSelectedPaths, admitted, Except.map]
  rw [Manifest.scanSkippingRejected_eq_scan_filter]
  simp [List.filter_append, selected, result, retained, opener]

end Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter

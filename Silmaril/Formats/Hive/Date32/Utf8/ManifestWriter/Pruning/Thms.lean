module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning
import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Thms
import Silmaril.Formats.Hive.Manifest.Pruning.Thms

public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)
open TypedPartitions (partitionCells)
open Silmaril.Formats.Relational.NamedTable (Packed)

/-- Admission errors precede resolution even when every predicate result
would be false or unknown. -/
theorem scanSelectedPaths_admission_error {Failure : Type} (schema : Schema) (options : PartitionPath.Options)
    (limits : Limits) (lookup : String → Except Failure Bytes) (projection : Scan.Projection schema.toScan)
    (keep : Scan.Predicate schema.keys.schema.toScan Value) (paths : List String)
    {cause : Manifest.PrepareError Date32.Error}
    (failed : preparePaths schema.intField schema.byteField schema.keys options paths = .error cause) :
    scanSelectedPaths schema options limits lookup projection keep paths = .error cause := by
  simp [scanSelectedPaths, failed, Except.map]

/-- The only files sent to the checked scan are the stable retained
occurrences. This statement includes their batch and error observations. -/
theorem scanSelectedPaths_eq_scan_filter {Failure : Type} (schema : Schema) (options : PartitionPath.Options)
    (limits : Limits) (lookup : String → Except Failure Bytes) (projection : Scan.Projection schema.toScan)
    (keep : Scan.Predicate schema.keys.schema.toScan Value) (paths : List String)
    {files : List (Manifest.File schema.keys.schema Value)}
    (admitted : preparePaths schema.intField schema.byteField schema.keys options paths = .ok files) :
    scanSelectedPaths schema options limits lookup projection keep paths =
      .ok (Manifest.scan (Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField
        schema.keys.schema lookup) projection keep (files.filter fun file => (keep file.cells).getD false)) := by
  change Scan.Projection (schema.keys.schema.extend
    (Int32ByteArrayGroup.File.schema schema.intField schema.byteField)) at projection
  simp only [scanSelectedPaths, admitted, Except.map]
  rw [Manifest.scanSkippingRejected_eq_scan_filter]

/-- An exhausted strict read certifies the skipped occurrences. Selection
then agrees with stable post-filtering and typed projection through EOS. -/
theorem readSelected_eq_postfilter (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (projection : Scan.Projection schema.toScan) (keep : Scan.Predicate schema.keys.schema.toScan Value)
    (files : List File) (full : Events.Trace schema.toScan Value ReadError)
    (read : readManifest schema options limits files = .ok full) (eos : full.termination = .eos) :
    ∃ selected, readSelected schema options limits projection keep files = .ok selected ∧
      selected.rows = projection.scan (fun row => keep (partitionCells row)) full.rows ∧
      selected.termination = .eos :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.readSelected_eq_postfilter schema options limits
    projection keep files full read eos

/-- For this writer's certified output, recover the filtered and projected
original rows in stable routed order. -/
theorem emit_readSelected {Name : Type*} (db : Packed Name String Value) (name : Name)
    (schema : Schema) (options : PartitionPath.Options) (limits : Limits) (rows : Scan.Table schema.toScan Value)
    (projection : Scan.Projection schema.toScan) (keep : Scan.Predicate schema.keys.schema.toScan Value) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.toScan, rows⟩)
    (written : emit db name schema options limits = .ok files) :
    ∃ selected, readSelected schema options limits projection keep files = .ok selected ∧
      selected.rows = projection.scan (fun row => keep (partitionCells row))
        (WritePlan.groupOriginalRows options encode rows) ∧ selected.termination = .eos := by
  obtain ⟨_, _, _, full, read, eos, _, exactRows, _⟩ := emit_readback db name schema options limits rows files found written
  rw [← exactRows]
  exact readSelected_eq_postfilter schema options limits projection keep files full read eos

/-- A reached retained read error keeps the exact cause and the selected
row prefix, including any completed groups in the failed file. Rejected
occurrences supply no premise about their payload. -/
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
        (runFile bad).rows ∧ trace.termination = .readError cause :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.scanSelectedPaths_first_retained_error schema options limits
    lookup projection keep paths before after bad cause admitted selected exhausted failed

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

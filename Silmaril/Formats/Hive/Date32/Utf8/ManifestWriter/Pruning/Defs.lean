module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Defs
public import Silmaril.Formats.Hive.Manifest.Pruning.Defs

/-! Opt-in partition selection over a typed paired Hive manifest. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)

/-- Complete typed path admission, then open only files for which the
partition predicate is SQL true. Project the retained native groups. -/
def scanSelectedPaths {Failure : Type} (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (lookup : String → Except Failure Bytes) (projection : Scan.Projection schema.toScan)
    (keep : Scan.Predicate schema.keys.schema.toScan Value) (paths : List String) :
    Except (Manifest.PrepareError Date32.Error)
      (Events.Trace projection.schema Value (Manifest.FileError (Manifest.Int32ByteArray.Error Failure))) :=
  (preparePaths schema.intField schema.byteField schema.keys options paths).map
    (Manifest.scanSkippingRejected
      (Manifest.int32ByteArraySnapshotOpener limits.reader schema.intField schema.byteField schema.keys.schema lookup)
      projection keep)

/-- Select and project the supplied paired manifest by the original keys. -/
def readSelected (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (projection : Scan.Projection schema.toScan) (keep : Scan.Predicate schema.keys.schema.toScan Value)
    (files : List File) :
    Except (Manifest.PrepareError Date32.Error) (Events.Trace projection.schema Value ReadError) :=
  scanSelectedPaths schema options limits (resolve files) projection keep (files.map (·.path))

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms

public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)
open WritePlan.FlatInt32.RowGroups (splitSlots)
open Silmaril.Formats.Relational.NamedTable (Packed)

theorem namedRows_of_observe {Name : Type*} (db : Packed Name String Value) (name : Name)
    (schema : Schema) (rows : Scan.Table schema.toScan Value)
    (found : Scan.observePacked db name = some ⟨schema.toScan, rows⟩) :
    namedRows db name schema = .ok rows := by
  simp [namedRows, found]

/-- Each input group has the exact ordered paired slots of its consecutive cut. -/
theorem fileInput_rows (schema : Schema) (sizes : List Nat) (rows : Scan.Table schema.physical Value) :
    (fileInput schema sizes rows).groups.map MixedV1Writer.Multi.Group.rows =
      (splitSlots sizes rows).map (List.map fun row => (row (0 : Fin 2), row (1 : Fin 2))) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.fileInput_rows schema sizes rows

/-- The deterministic cuts account for every row within the declared caps. -/
theorem FileMatches.cutBounds {schema : Schema} {limits : Limits} {bucket : Bucket schema} {file : File}
    (matched : FileMatches schema limits bucket file) :
    file.groupRows.sum = bucket.rows.length ∧ bucket.rows.length ≤ limits.cuts.maxRowsPerFile ∧
      file.groupRows.length ≤ limits.cuts.maxGroupsPerFile ∧
      ∀ count ∈ file.groupRows, 0 < count ∧ count ≤ limits.cuts.rowsPerGroup :=
  (WritePlan.FlatInt32.RowGroups.planCuts_exact matched.planned).2

/-- The original routing error precedes file emission. -/
theorem emit_routing_error {Name : Type*} (db : Packed Name String Value) (name : Name) (schema : Schema)
    (options : PartitionPath.Options) (limits : Limits) (rows : Scan.Table schema.toScan Value)
    (source : namedRows db name schema = .ok rows)
    (names : PartitionPath.validateKeys [schema.intName, schema.byteName] = .ok ())
    {cause : WritePlan.Error EncodeError}
    (failed : WritePlan.plan schema.physical schema.keys.schema options encode rows = .error cause) :
    emit db name schema options limits = .error (.routing cause) := by
  simp [emit, source, names, failed, Except.mapError, Bind.bind, Except.bind]

/-- The files match the independent route order and cuts. Checked reopen
through paired ingress reaches EOS with the exact group counts and typed
original rows in first-seen directory order, stable inside each directory. -/
theorem emit_readback {Name : Type*} (db : Packed Name String Value) (name : Name) (schema : Schema)
    (options : PartitionPath.Options) (limits : Limits) (rows : Scan.Table schema.toScan Value) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.toScan, rows⟩)
    (written : emit db name schema options limits = .ok files) :
    ∃ buckets, WritePlan.reference schema.physical schema.keys.schema options encode rows = .ok buckets ∧
      List.Forall₂ (FileMatches schema limits) buckets files ∧
      ∃ trace, readManifest schema options limits files = .ok trace ∧ trace.termination = .eos ∧
        trace.batches.map (·.rowCount) = files.flatMap (·.groupRows) ∧
        trace.rows = WritePlan.groupOriginalRows options encode rows ∧
        trace.batches.map (·.toRows) =
          (files.flatMap (·.groupRows)).splitLengths (WritePlan.groupOriginalRows options encode rows) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.emit_readback db name schema options limits rows files
    (namedRows_of_observe db name schema rows found) written

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

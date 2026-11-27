module

public import Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.Defs
import Silmaril.Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8
import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Thms

public section

namespace Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Date32.Utf8.ManifestWriter (File Limits Schema emit emit_readSelected readSelected)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (partitionCells)

variable {Name : Type*} {schema : Scan.Schema String Kind}

/-- Vacancy takes precedence in the result. A failed source or an incomplete
trace returns its typed error without an updated database. -/
theorem importResult_outcome [DecidableEq Name] (db : Database Name) (name : Name)
    (result : ScanResult schema) :
    importResult db name result =
      if (db name).isSome then .error .nameConflict
      else match result with
      | .error reason => .error (.openError (.admission reason))
      | .ok trace =>
        match trace.termination with
        | .closed => .error .closed
        | .readError reason => .error (.readError (.runtime reason))
        | .closeError reason => .error (.closeError (.runtime reason))
        | .eos => .ok (Function.update db name (some ⟨schema, trace.rows⟩)) :=
  Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8.importResult_outcome db name result

/-- Exact selected schema and rows are installed only after successful EOS. -/
theorem importSelected_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (layout : Schema) (options : PartitionPath.Options) (limits : Limits) (projection : Scan.Projection layout.toScan)
    (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    importSelected db name layout options limits projection keep files = .ok next ↔
      db name = none ∧ ∃ trace,
        readSelected layout options limits projection keep files = .ok trace ∧ trace.termination = .eos ∧
        next = Function.update db name (some ⟨projection.schema, trace.rows⟩) :=
  Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8.importSelected_ok_iff
    db next name layout options limits projection keep files

/-- Preserve projected positions, including zero-column row counts, and
preserve every other named entry. -/
theorem importSelected_observe [DecidableEq Name] (db next : Database Name) (name : Name)
    (layout : Schema) (options : PartitionPath.Options) (limits : Limits) (projection : Scan.Projection layout.toScan)
    (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File)
    (loaded : importSelected db name layout options limits projection keep files = .ok next) :
    ∃ trace,
      readSelected layout options limits projection keep files = .ok trace ∧ trace.termination = .eos ∧
      Scan.observePacked next name = some ⟨projection.schema, trace.rows⟩ ∧
      trace.rows.length = (trace.batches.map AlignedColumns.rowCount).sum ∧
      ∀ other, other ≠ name → next other = db other :=
  Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8.importSelected_observe
    db next name layout options limits projection keep files loaded

/-- A certified writer result installs the stable filtered projection of the
original routed rows at the requested vacant name. -/
theorem emit_importSelected [DecidableEq Name] (source target : Database Name) (sourceName dest : Name)
    (layout : Schema) (options : PartitionPath.Options) (limits : Limits) (rows : Scan.Table layout.toScan Value)
    (projection : Scan.Projection layout.toScan) (keep : Scan.Predicate layout.keys.schema.toScan Value)
    (files : List File) (found : Scan.observePacked source sourceName = some ⟨layout.toScan, rows⟩)
    (written : emit source sourceName layout options limits = .ok files) (vacant : target dest = none) :
    importSelected target dest layout options limits projection keep files =
      .ok (Function.update target dest (some ⟨projection.schema,
        projection.scan (fun row => keep (partitionCells row))
          (WritePlan.groupOriginalRows options Date32.Utf8.encode rows)⟩)) := by
  obtain ⟨selected, read, exactRows, eos⟩ :=
    emit_readSelected source sourceName layout options limits rows projection keep files found written
  exact (importSelected_ok_iff target _ dest layout options limits projection keep files).mpr
    ⟨vacant, selected, read, eos, by rw [exactRows]⟩

end Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8

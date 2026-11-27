module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Scan.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Formats.Hive.Manifest.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)
open Silmaril.Formats.Parquet

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

theorem scanSnapshots_equivalent_thenFilter (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (files : List (File schema Value)) :
    Events.EventStream.Equivalent
      (.ok ⟨projection.schema, scan (snapshotOpener limits lookup bind) projection predicate files⟩)
      (.ok ⟨projection.schema, scanSnapshotsThenFilter limits lookup bind projection predicate files⟩) :=
  Manifest.scan_equivalent_thenFilter (snapshotOpener limits lookup bind) projection predicate files

theorem scanFile_eof_of_snapshot (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (predicate : Scan.Predicate schema.toScan Value)
    (file : File schema Value) (clean : SnapshotReachesEOF limits lookup bind file.path.declared) :
    (scanFile (snapshotOpener limits lookup bind) projection predicate file).termination = .eos := by
  obtain ⟨bytes, found, exhausted⟩ := clean
  cases opened : Snapshot.openSource limits bind bytes with
  | error reason => simp [Snapshot.readAll, opened, Except.map, Parquet.Reader.readAll,
      Events.EventStream.collect] at exhausted
  | ok source =>
    have same := ParquetScan.readFile_eq_reader source (source.groups.length + 1)
    simp only [Snapshot.readAll, opened, Except.map, Parquet.Reader.readAll, same,
      Events.EventStream.collect, Events.Trace.collect, Except.ok.injEq] at exhausted
    cases keep : (predicate file.cells).getD false <;>
      simp [scanFile, snapshotOpener, found, opened, Except.map, ParquetScan.scanPartition,
        ParquetScan.assemble, exhausted, keep]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

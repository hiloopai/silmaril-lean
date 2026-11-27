module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Defs
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Scan

public section

namespace Silmaril.Formats.Hive.Manifest.Heterogeneous

open Silmaril.Relational
open Parquet.FlatProjection.Events (Cell)

/-- The checked file carries the shared Hive binding, direct Parquet open and full-leaf collision check. -/
theorem bindFile_exact {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry} {bound : BoundFile schema}
    (accepted : bindFile schema options limits entry = .ok bound) :
    Manifest.prepareFile schema.partitions options convertCell entry.path = .ok bound.partition ∧
      Parquet.FlatProjection.Events.openFile limits entry.bytes schema.ordinals = .ok bound.physical ∧
      ∃ root leaves, bound.physical.snapshot.metadata.schema = root :: leaves ∧
        Parquet.Footer.ColumnOrder.isFlat root leaves = true ∧
        leaves.find? (fun leaf => schema.partitions.keys.contains leaf.name) = none :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.bindFile_exact accepted

/-- Each original typed row is augmented with the literal path's one virtual tuple. -/
theorem extend_rows {schema : Schema} (entry : Entry × Nat)
    (cells : Scan.Row schema.partitions.toScan Cell) (physical : PhysicalTrace schema) :
    (extend entry cells physical).rows =
      physical.rows.map (fun row => TypedPartitions.extendRow row cells) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.extend_rows entry cells physical

/-- Typed constants preserve each original group and its row count. -/
theorem extend_counts {schema : Schema} (entry : Entry × Nat) (cells : Scan.Row schema.partitions.toScan Cell)
    (physical : PhysicalTrace schema) :
    (extend entry cells physical).batches.map (·.rowCount) = physical.batches.map (·.rowCount) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.extend_counts entry cells physical

/-- A bound file reads exactly the direct ordered Parquet Events plus its typed partition constants. -/
theorem readFile_direct {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry × Nat} {bound : BoundFile schema}
    (accepted : bindFile schema options limits entry.1 = .ok bound) :
    Parquet.FlatProjection.Events.readAll limits entry.1.bytes schema.ordinals =
        .ok ⟨bound.physical.schema, bound.physical.trace limits⟩ ∧
      readFile schema options limits entry = extend entry bound.partition.cells (bound.trace limits) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.readFile_direct accepted

/-- The physical failure keeps its exact group/column cause and the earlier augmented batches. -/
theorem readFile_read_error {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {entry : Entry × Nat} {bound : BoundFile schema}
    {cause : Parquet.FlatProjection.Events.Error}
    (accepted : bindFile schema options limits entry.1 = .ok bound)
    (failed : (bound.physical.trace limits).termination = .readError cause) :
    readFile schema options limits entry =
      ⟨(extend entry bound.partition.cells (bound.trace limits)).batches,
        .readError (.file entry.2 entry.1.path (.readParquet cause))⟩ :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.readFile_read_error accepted failed

/-- Dataset EOS witnesses successful direct reads in manifest order and preserves every group boundary. -/
theorem read_eos {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {manifest : List Entry} {trace : Trace schema}
    (readOk : Heterogeneous.read schema options limits manifest = .ok trace) (eos : trace.termination = .eos) :
    ∃ files, List.Forall₂ (FileBatches schema options limits) manifest.zipIdx files ∧
      trace.batches = files.flatten :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.read_eos readOk eos

/-- The first failing file retains the complete earlier files and its own completed group prefix. -/
theorem read_first_error {schema : Schema} {options : PartitionPath.Options}
    {limits : Parquet.FlatProjection.Events.Limits} {manifest : List Entry}
    {before after : List (Entry × Nat)} {current : Entry × Nat} {cause : Error}
    (admitted : checkSchema schema = .ok ())
    (split : manifest.zipIdx = before ++ current :: after)
    (earlier : ∀ entry ∈ before, (readFile schema options limits entry).termination = .eos)
    (failed : (readFile schema options limits current).termination = .readError cause) :
    Heterogeneous.read schema options limits manifest = .ok
      ⟨before.flatMap (fun entry => (readFile schema options limits entry).batches) ++
        (readFile schema options limits current).batches, .readError cause⟩ :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.read_first_error admitted split earlier failed

/-- Logical per-file projection agrees exactly with projecting the ordered dataset trace. -/
theorem project_agrees (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (manifest : List Entry) (p : Scan.Projection schema.output) :
    project schema options limits manifest p =
      (Heterogeneous.read schema options limits manifest).map (fun trace => trace.scan p (fun _ => some true)) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.project_agrees schema options limits manifest p

/-- A projection keeps the original batch counts even at width zero. -/
theorem project_counts {schema : Schema} (p : Scan.Projection schema.output) (trace : Trace schema) :
    (trace.scan p (fun _ => some true)).batches.map (·.rowCount) = trace.batches.map (·.rowCount) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.project_counts p trace

end Silmaril.Formats.Hive.Manifest.Heterogeneous

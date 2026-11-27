module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Defs

/-! Partition-only pruning over literal native Hive manifest occurrences. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

inductive PruneError (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | file (index : Nat) (path : String) (reason : ReadError Failure)
  deriving BEq

/-- Check and bind the literal path before evaluating the predicate. Only
true selects the payload. Errors carry the original zero-based occurrence
index, including skipped and duplicate paths. -/
def readPrunedFile {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate schema.toScan Cell) (entry : File × Nat) :
    Except (PruneError Failure) (Scan.Table (schema.extend (physical leaf)) Cell) :=
  let (file, index) := entry
  let result : Except (ReadError Failure) _ := do
    let directory ← checkFilePath file.path
    let cells ← (decodeDirectory schema options decode directory).mapError ReadError.partition
    if (predicate cells).getD false then
      let rows ← readPayload limits leaf file
      return (⟨cells, rows⟩ : TypedPartitions.TypedPartition (physical leaf) schema Cell).materialize
    else return []
  result.mapError (PruneError.file index file.path)

/-- Check schema first, then visit literal occurrences in order. On each
occurrence validate the path, leaf and typed directory cells before testing
the predicate. False and unknown skip payload validation. The first reached
failure aborts the restore and returns no partial table. -/
def restorePruned {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate schema.toScan Cell) (files : List File) :
    Except (PruneError Failure) (Scan.Table (schema.extend (physical leaf)) Cell) := do
  (TypedPartitions.checkSchema (physical leaf) schema).mapError PruneError.schema
  let rows ← files.zipIdx.mapM (readPrunedFile leaf schema options decode limits predicate)
  return rows.flatten

end Silmaril.Formats.Hive.WritePlan.FlatInt32

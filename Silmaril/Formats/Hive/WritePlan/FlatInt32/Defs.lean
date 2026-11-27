module

public import Silmaril.Formats.Hive.Manifest.Defs
public import Silmaril.Formats.Hive.WritePlan.Restore.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
public import Silmaril.Formats.Relational.NamedTable.Defs

/-! Emit and restore one native INT32 file per checked Hive write bucket. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

abbrev Database (Name : Type*) := Silmaril.Formats.Relational.NamedTable.Packed Name String Cell

/-- Exactly one OPTIONAL, unannotated INT32 data leaf. -/
def physical (leaf : String) : Scan.Schema String Unit := ⟨1, fun _ => (leaf, ())⟩

def filename : String := "part-0.parquet"

def filePath (directory : String) : String :=
  if directory.isEmpty then filename else directory ++ "/" ++ filename

/-- A pure manifest occurrence with the literal relative path, exact
physical row count, and complete Parquet bytes. -/
structure File where
  path : String
  rowCount : Nat
  bytes : Bytes

inductive EmitError (Failure : Type*) where
  | missingName
  | schemaMismatch
  | routing (reason : WritePlan.Error Failure)
  | path (path : String) (reason : Manifest.PathError)
  | pathMismatch (path : String)
  | parquet (path : String) (reason : FlatInt32Writer.Error)
  deriving BEq, Repr

/-- Bind the actual stored table at its exact ordered augmented schema. -/
def namedRows {Name Failure : Type*} (db : Database Name) (name : Name)
    (expected : Scan.Schema String Unit) : Except (EmitError Failure) (Scan.Table expected Cell) :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some stored =>
    if same : List.ofFn expected.kind = List.ofFn stored.schema.kind then
      have width : expected.width = stored.schema.width := by simpa using congrArg List.length same
      .ok (stored.rows.map fun row i => row (i.cast width))
    else .error .schemaMismatch

def writerInput (leaf : String) (rows : Scan.Table (physical leaf) Cell) : FlatInt32Writer.Input :=
  ⟨rows.length, [⟨leaf, .optional (rows.map fun row => row (0 : Fin 1))⟩]⟩

def emitBucket {Failure : Type*} (limits : FlatInt32Writer.Limits) (leaf : String)
    (bucket : Bucket (physical leaf) Cell) : Except (EmitError Failure) File := do
  let path := filePath bucket.directory
  let split ← (Manifest.splitFile path).mapError (EmitError.path path)
  if split ≠ (bucket.directory, filename) then throw (.pathMismatch path)
  let file ← (FlatInt32Writer.emit limits (writerInput leaf bucket.rows)).mapError (EmitError.parquet path)
  return ⟨path, bucket.rows.length, file.bytes⟩

/-- Finish routing before emitting any manifest. Visit the planned buckets
in their original directory order and return only a complete manifest. -/
def emit {Name Failure : Type*} (db : Database Name) (name : Name)
    (leaf : String) (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell Failure) (limits : FlatInt32Writer.Limits) :
    Except (EmitError Failure) (List File) := do
  let rows ← namedRows db name (schema.extend (physical leaf))
  let buckets ← (WritePlan.plan (physical leaf) schema options encode rows).mapError EmitError.routing
  buckets.mapM (emitBucket limits leaf)

abbrev SnapshotError := Snapshot.Error (Snapshot.FlatInt32.Error Unit)

inductive ReadError (Failure : Type*) where
  | path (path : String) (reason : Manifest.PathError)
  | filename (path : String)
  | parquet (path : String) (reason : SnapshotError)
  | stopped (path : String) (reason : Events.Termination SnapshotError)
  | shape (path : String)
  | partition (reason : RestoreError Failure)
  deriving BEq

/-- The writer's checked page/footer limits and the manifest's advertised
dimensions for one column. -/
def readLimits (limits : FlatInt32Writer.Limits) (rows : Nat) : Snapshot.FlatInt32.Limits :=
  ⟨⟨limits.footer, 2⟩,
    ⟨limits.footer, limits.pageReader, rows, 1, rows, limits.page.scalar.compressedBytes⟩,
    limits.page.scalar⟩

def readBucket {Failure : Type*} (limits : FlatInt32Writer.Limits) (leaf : String) (file : File) :
    Except (ReadError Failure) (Bucket (physical leaf) Cell) := do
  let (directory, name) ← (Manifest.splitFile file.path).mapError (ReadError.path file.path)
  if name ≠ filename then throw (.filename file.path)
  let ⟨opened, trace⟩ ← (Snapshot.FlatInt32.readAll (readLimits limits file.rowCount)
    (physical leaf) file.bytes).mapError (ReadError.parquet file.path)
  if trace.termination ≠ .eos then throw (.stopped file.path trace.termination)
  let rows := trace.rows
  if trace.batches.length ≠ 1 ∨ rows.length ≠ file.rowCount then throw (.shape file.path)
  if width : opened.width = 1 then
    return ⟨directory, rows.map fun row i => row (i.cast width.symm)⟩
  else throw (.shape file.path)

/-- Check each literal file in manifest order, then restore directory cells
using the shared typed Hive binder. -/
def restore {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (limits : FlatInt32Writer.Limits) (files : List File) :
    Except (ReadError Failure) (Scan.Table (schema.extend (physical leaf)) Cell) := do
  let buckets ← files.mapM (readBucket limits leaf)
  (WritePlan.restore (physical leaf) schema options decode buckets).mapError ReadError.partition

end Silmaril.Formats.Hive.WritePlan.FlatInt32

module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Defs

/-! Ordered group batches from a checked, partition-pruned native manifest. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert extendRow)
open Snapshot.FlatInt32 (Cell)

structure Position where
  fileIndex : Nat
  path : String
  groupIndex : Nat
  deriving DecidableEq, Repr

structure GroupBatch (schema : Scan.Schema String Unit) where
  position : Position
  columns : Scan.Columns schema Cell

/-- An exhausted scan has `result = .ok ()`. A read failure keeps the
preceding complete batches and its original typed cause. -/
structure Trace (schema : Scan.Schema String Unit) (Failure : Type*) where
  batches : List (GroupBatch schema)
  result : Except (ReadError Failure) Unit

variable {schema : Scan.Schema String Unit} {Failure : Type*}

def Trace.toArrow (trace : Trace schema Failure) : Arrow.Events.Trace schema Cell (ReadError Failure) :=
  ⟨trace.batches.map (·.columns),
    match trace.result with | .ok () => .eos | .error reason => .readError reason⟩

def Trace.rows (trace : Trace schema Failure) : Scan.Table schema Cell :=
  trace.batches.flatMap fun batch => batch.columns.toRows

def Trace.finish (trace : Trace schema Failure) : Except (ReadError Failure) (Scan.Table schema Cell) :=
  trace.result.map fun _ => trace.rows

/-- Project typed columns in each batch while preserving its position and
explicit row count, including projections of width zero. -/
def Trace.project (trace : Trace schema Failure) (projection : Scan.Projection schema) :
    Trace projection.schema Failure :=
  ⟨trace.batches.map fun batch => ⟨batch.position, projection.projectColumns batch.columns⟩, trace.result⟩

/-- Concatenate complete prefix batches. A failure consumes the current
position and ends the scan before visiting the suffix. -/
def Trace.assemble {α : Type*} (traceOf : α → Trace schema Failure) : List α → Trace schema Failure
  | [] => ⟨[], .ok ()⟩
  | item :: rest =>
    let trace := traceOf item
    match trace.result with
    | .error _ => trace
    | .ok () =>
      let tail := assemble traceOf rest
      ⟨trace.batches ++ tail.batches, tail.result⟩

def groupBatch {leaf : String} {partitions : PartitionSchema Unit}
    (cells : Scan.Row partitions.toScan Cell) (position : Position) (slots : List (Option Int32)) :
    GroupBatch (partitions.extend (physical leaf)) :=
  ⟨position, AlignedColumns.ofRows (slots.map fun slot => extendRow (fun _ => slot) cells)⟩

def scanGroup {leaf : String} {partitions : PartitionSchema Unit} (cells : Scan.Row partitions.toScan Cell)
    (file : File) (index : Nat) (source : Reader.Source Nat (physical leaf) Cell SnapshotError) (ordinal : Nat) :
    Trace (partitions.extend (physical leaf)) Failure :=
  match readSlots source ordinal with
  | .error reason => ⟨[], .error (.file index file.path (.payload reason))⟩
  | .ok slots => ⟨[groupBatch cells ⟨index, file.path, ordinal⟩ slots], .ok ()⟩

/-- Read each checked group at its original footer ordinal. -/
def scanSource {leaf : String} {partitions : PartitionSchema Unit} (cells : Scan.Row partitions.toScan Cell)
    (file : File) (index : Nat) (source : Reader.Source Nat (physical leaf) Cell SnapshotError) :
    Trace (partitions.extend (physical leaf)) Failure :=
  Trace.assemble (scanGroup cells file index source) source.groups

/-- Every reached path is bound before the partition predicate. A rejected
file emits no groups and skips opening the payload. -/
def scanFile (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (entry : File × Nat) :
    Trace (partitions.extend (physical leaf)) Failure :=
  let (file, index) := entry
  match bindFileCells partitions options decode file with
  | .error reason => ⟨[], .error (.file index file.path reason)⟩
  | .ok cells =>
    if (predicate cells).getD false then
      match openGroupSource policy limits leaf file with
      | .error reason => ⟨[], .error (.file index file.path (.payload reason))⟩
      | .ok source => scanSource cells file index source
    else ⟨[], .ok ()⟩

/-- Schema and policy failures precede schema emission. After successful
admission, emit one tagged batch per decoded group, then exactly EOS or the
first reached error. Literal repeats keep distinct occurrence indices. -/
def scanPruned (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File) :
    Except (ReadError Failure) (Trace (partitions.extend (physical leaf)) Failure) :=
  (checkRead (Failure := Failure) leaf partitions policy).map fun _ =>
    Trace.assemble (scanFile leaf partitions options decode policy limits predicate) files.zipIdx

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

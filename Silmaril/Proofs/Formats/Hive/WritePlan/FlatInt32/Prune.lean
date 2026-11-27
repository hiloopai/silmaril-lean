module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Prune.Defs
import Silmaril.Formats.Hive.TypedPartitions.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.Prune

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan
open Silmaril.Formats.Hive.WritePlan.FlatInt32
open TypedPartitions (PartitionSchema Convert TypedPartition materialize partitionCells)
open Snapshot.FlatInt32 (Cell)

variable {Failure : Type*} {leaf : String} {schema : PartitionSchema Unit}
variable (options : PartitionPath.Options) (decode : Convert Cell Failure)
variable (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell)

private def bindBucket (bucket : Bucket (physical leaf) Cell) :
    Except (RestoreError Failure) (TypedPartition (physical leaf) schema Cell) :=
  (decodeDirectory schema options decode bucket.directory).map fun cells => ⟨cells, bucket.rows⟩

private theorem mapM_cons_ok {α β ε : Type*} {f : α → Except ε β}
    {head : α} {tail : List α} {items : List β}
    (success : (head :: tail).mapM f = .ok items) :
    ∃ first rest, items = first :: rest ∧ f head = .ok first ∧ tail.mapM f = .ok rest := by
  cases first : f head <;> cases rest : tail.mapM f <;>
    simp_all [List.mapM_cons, bind, Except.bind, pure, Except.pure]

private theorem readPrunedFile_eq_filter {file : File} {index : Nat}
    {bucket : Bucket (physical leaf) Cell} {typed : TypedPartition (physical leaf) schema Cell}
    (read : readBucket (Failure := Failure) limits leaf file = .ok bucket)
    (bound : bindBucket options decode bucket = .ok typed) :
    readPrunedFile leaf schema options decode limits predicate (file, index) =
      .ok (Scan.select (fun row => predicate (partitionCells row)) typed.materialize) := by
  cases path : checkFilePath (Failure := Failure) file.path with
  | error error => simp [readBucket, path, bind, Except.bind] at read
  | ok directory =>
    cases payload : readPayload (Failure := Failure) limits leaf file with
    | error error => simp [readBucket, path, payload, bind, Except.bind] at read
    | ok rows =>
      simp [readBucket, path, payload, bind, Except.bind, pure, Except.pure] at read
      subst bucket
      cases binding : decodeDirectory schema options decode directory with
      | error error => simp [bindBucket, binding, Except.map] at bound
      | ok cells =>
        simp [bindBucket, binding, Except.map] at bound
        subst typed
        cases keep : (predicate cells).getD false <;>
          simp [readPrunedFile, path, payload, binding, keep, Except.mapError, bind, Except.bind,
            pure, Except.pure, Scan.select, TypedPartition.materialize, List.filter_map, Function.comp_def]

private theorem prune_eq_filter {files : List File} {buckets : List (Bucket (physical leaf) Cell)}
    {typed : List (TypedPartition (physical leaf) schema Cell)}
    (read : files.mapM (readBucket (Failure := Failure) limits leaf) = .ok buckets)
    (bound : buckets.mapM (bindBucket options decode) = .ok typed) (index : Nat) :
    ((files.zipIdx index).mapM (readPrunedFile leaf schema options decode limits predicate)).map List.flatten =
      .ok (Scan.select (fun row => predicate (partitionCells row)) (materialize typed)) := by
  induction files generalizing buckets typed index with
  | nil =>
    cases read
    cases bound
    rfl
  | cons file files ih =>
    obtain ⟨bucket, buckets, rfl, firstRead, tailRead⟩ := mapM_cons_ok read
    obtain ⟨entry, typed, rfl, firstBound, tailBound⟩ := mapM_cons_ok bound
    have first := readPrunedFile_eq_filter options decode limits predicate (index := index) firstRead firstBound
    have tail := ih tailRead tailBound (index + 1)
    cases result : (files.zipIdx (index + 1)).mapM (readPrunedFile leaf schema options decode limits predicate) with
    | error error => simp [result, Except.map] at tail
    | ok remaining =>
      simp [result, Except.map] at tail
      simp [List.mapM_cons, first, result, tail, materialize, Scan.select, Except.map, bind, Except.bind,
        pure, Except.pure]

theorem restorePruned_eq_filter {files : List File} {rows : Scan.Table (schema.extend (physical leaf)) Cell}
    (restored : restore leaf schema options decode limits files = .ok rows) :
    restorePruned leaf schema options decode limits predicate files =
      .ok (Scan.select (fun row => predicate (partitionCells row)) rows) := by
  cases read : files.mapM (readBucket (Failure := Failure) limits leaf) with
  | error reason => simp [FlatInt32.restore, read, bind, Except.bind] at restored
  | ok buckets =>
    cases admitted : TypedPartitions.checkSchema (Failure := Failure) (physical leaf) schema with
    | error reason => simp [FlatInt32.restore, read, WritePlan.restore, admitted, Except.mapError, bind, Except.bind] at restored
    | ok admittedUnit =>
      cases admittedUnit
      simp only [FlatInt32.restore, read, bind, Except.bind, WritePlan.restore, admitted] at restored
      change ((buckets.mapM (bindBucket options decode)).map materialize).mapError
        ReadError.partition = .ok rows at restored
      cases bound : buckets.mapM (bindBucket (schema := schema) options decode) with
      | error reason => simp [bound, Except.mapError, Except.map] at restored
      | ok typed =>
        simp [bound, Except.mapError, Except.map] at restored
        subst rows
        simpa [restorePruned, admitted, Except.mapError, Except.map, bind, Except.bind,
          pure, Except.pure] using prune_eq_filter options decode limits predicate read bound 0

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.Prune

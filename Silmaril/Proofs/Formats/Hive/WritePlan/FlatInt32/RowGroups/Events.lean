module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Defs
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan.FlatInt32 (physical SnapshotError)
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
open TypedPartitions (PartitionSchema Convert extendRow TypedPartition materialize)
open Snapshot.FlatInt32 (Cell)

variable {schema : Scan.Schema String Unit} {Failure : Type*}

private theorem assemble_finish {α : Type*} (traceOf : α → Trace schema Failure) (items : List α) :
    (Trace.assemble traceOf items).finish = (items.mapM (fun item => (traceOf item).finish)).map List.flatten := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.mapM_cons]
    cases current : (traceOf item).result with
    | error reason =>
      have head : (traceOf item).finish = .error reason := by simp [Trace.finish, current, Except.map]
      rw [head]
      simp [Trace.assemble, current, Trace.finish, Except.map, bind, Except.bind]
    | ok unitValue =>
      cases unitValue
      have head : (traceOf item).finish = .ok (traceOf item).rows := by simp [Trace.finish, current, Except.map]
      have step : (Trace.assemble traceOf (item :: rest)).finish =
          (Trace.assemble traceOf rest).finish.map ((traceOf item).rows ++ ·) := by
        cases tail : (Trace.assemble traceOf rest).result <;>
          simp [Trace.assemble, current, tail, Trace.finish, Trace.rows, List.flatMap_append, Except.map]
      rw [step, ih, head]
      cases rest.mapM (fun item => (traceOf item).finish) <;> rfl

private theorem mapM_mapExcept {α β γ ε δ : Type*} (read : α → Except ε β)
    (values : β → γ) (error : ε → δ) (items : List α) :
    items.mapM (fun item => ((read item).map values).mapError error) =
      ((items.mapM read).map (List.map values)).mapError error := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons]
    rw [ih]
    cases read item <;> cases rest.mapM read <;> rfl

private theorem mapError_id {α ε : Type*} (result : Except ε α) : result.mapError id = result := by
  cases result <;> rfl

theorem assemble_first_error {α : Type*} (traceOf : α → Trace schema Failure)
    (before : List α) (bad : α) (after : List α) (reason : ReadError Failure)
    (done : ∀ entry ∈ before, (traceOf entry).result = .ok ())
    (failed : (traceOf bad).result = .error reason) :
    Trace.assemble traceOf (before ++ bad :: after) =
      ⟨before.flatMap (fun entry => (traceOf entry).batches) ++ (traceOf bad).batches, .error reason⟩ := by
  induction before with
  | nil =>
    simp [Trace.assemble, failed]
    exact congrArg (Trace.mk (traceOf bad).batches) failed
  | cons entry rest ih =>
    have beforeTrace := ih (fun entry mem => done entry (List.mem_cons_of_mem _ mem))
    simp [Trace.assemble, done entry (by simp), beforeTrace, List.append_assoc]

variable {leaf : String} {partitions : PartitionSchema Unit}

private theorem scanGroups_finish (cells : Scan.Row partitions.toScan Cell) (file : File) (index : Nat)
    (source : Reader.Source Nat (physical leaf) Cell SnapshotError) (ordinals : List Nat) :
    (Trace.assemble (scanGroup (Failure := Failure) cells file index source) ordinals).finish =
      ((ordinals.mapM (readSlots source)).map fun groups =>
        groups.flatten.map fun slot => extendRow (fun _ => slot) cells).mapError
          (fun reason => .file index file.path (.payload reason)) := by
  rw [assemble_finish]
  have step (ordinal : Nat) : (scanGroup (Failure := Failure) cells file index source ordinal).finish =
      ((readSlots source ordinal).map fun slots => slots.map fun slot => extendRow (fun _ => slot) cells).mapError
        (fun reason => .file index file.path (.payload reason)) := by
    cases read : readSlots source ordinal <;>
      simp [scanGroup, read, Trace.finish, Trace.rows, groupBatch, Except.map, Except.mapError]
  simp only [step]
  rw [mapM_mapExcept]
  cases ordinals.mapM (readSlots source) <;> simp [Except.map, Except.mapError]

private theorem scanFile_finish (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (entry : File × Nat) :
    (scanFile leaf partitions options decode policy limits predicate entry).finish =
      (readPart leaf partitions options decode policy limits predicate entry).map TypedPartition.materialize := by
  obtain ⟨file, index⟩ := entry
  cases path : bindFileCells partitions options decode file with
  | error reason => simp [scanFile, readPart, path, Trace.finish, Except.map, Except.mapError, bind, Except.bind]
  | ok cells =>
    cases keep : (predicate cells).getD false
    · simp [scanFile, readPart, path, keep, Trace.finish, Trace.rows,
        TypedPartition.materialize, Except.map, Except.mapError, bind, Except.bind, pure, Except.pure]
    · cases opened : openGroupSource policy limits leaf file with
      | error reason =>
        simp [scanFile, readPart, path, keep, opened, readPayload, Trace.finish, Except.map, Except.mapError, bind, Except.bind]
      | ok source =>
        rw [show (scanFile leaf partitions options decode policy limits predicate (file, index)) =
          scanSource cells file index source by simp [scanFile, path, keep, opened]]
        rw [scanSource, scanGroups_finish]
        cases read : source.groups.mapM (readSlots source) <;>
          simp [readPart, readPayload, path, keep, opened, read, TypedPartition.materialize,
            Except.map, Except.mapError, bind, Except.bind, pure, Except.pure, List.map_map, Function.comp_def]

private theorem mapM_materialize {α : Type*} (read : α → Except (ReadError Failure) (TypedPartition (physical leaf) partitions Cell))
    (items : List α) :
    (items.mapM (fun item => (read item).map TypedPartition.materialize)).map List.flatten =
      (items.mapM read).map materialize := by
  have fused := mapM_mapExcept read TypedPartition.materialize id items
  simp only [mapError_id] at fused
  rw [fused]
  cases items.mapM read <;> rfl

theorem finish_scanPruned (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File) :
    (scanPruned leaf partitions options decode policy limits predicate files).bind Trace.finish =
      restorePruned leaf partitions options decode policy limits predicate files := by
  cases admitted : checkRead (Failure := Failure) leaf partitions policy with
  | error reason => simp [scanPruned, restorePruned, admitted, Except.map, bind, Except.bind]
  | ok unitValue =>
    cases unitValue
    simp [scanPruned, restorePruned, admitted, Except.map, bind, Except.bind]
    rw [assemble_finish]
    simp only [scanFile_finish]
    exact mapM_materialize _ _

private theorem assembleScanGroups_of_prefix (cells : Scan.Row partitions.toScan Cell) (file : File)
    (index : Nat) (source : Reader.Source Nat (physical leaf) Cell SnapshotError)
    (before after : List Nat) (groups : Slots) (decoded : before.mapM (readSlots source) = .ok groups) :
    Trace.assemble (scanGroup (Failure := Failure) cells file index source) (before ++ after) =
      let tail := Trace.assemble (scanGroup cells file index source) after
      ⟨(before.zip groups).map (fun (ordinal, slots) => groupBatch cells ⟨index, file.path, ordinal⟩ slots) ++
        tail.batches, tail.result⟩ := by
  induction before generalizing groups with
  | nil =>
    cases decoded
    simp
  | cons ordinal rest ih =>
    rw [List.mapM_cons] at decoded
    cases head : readSlots source ordinal with
    | error reason => simp [head, bind, Except.bind] at decoded
    | ok slots =>
      cases tail : rest.mapM (readSlots source) with
      | error reason => simp [head, tail, bind, Except.bind] at decoded
      | ok rows =>
        simp [head, tail, bind, Except.bind, pure, Except.pure] at decoded
        subst groups
        simp [Trace.assemble, scanGroup, head, ih rows tail]

theorem scanSource_batches (cells : Scan.Row partitions.toScan Cell) (file : File) (index : Nat)
    (source : Reader.Source Nat (physical leaf) Cell SnapshotError) (groups : Slots)
    (decoded : source.groups.mapM (readSlots source) = .ok groups) :
    scanSource (Failure := Failure) cells file index source =
      ⟨(source.groups.zip groups).map (fun (ordinal, slots) => groupBatch cells ⟨index, file.path, ordinal⟩ slots), .ok ()⟩ := by
  simpa only [scanSource, Trace.assemble, List.append_nil] using
    assembleScanGroups_of_prefix (Failure := Failure) cells file index source source.groups [] groups decoded

theorem scanSource_first_error (cells : Scan.Row partitions.toScan Cell) (file : File) (index : Nat)
    (source : Reader.Source Nat (physical leaf) Cell SnapshotError) (before after : List Nat) (failed : Nat)
    (groups : Slots) (cause : PayloadError) (split : source.groups = before ++ failed :: after)
    (decoded : before.mapM (readSlots source) = .ok groups) (error : readSlots source failed = .error cause) :
    scanSource (Failure := Failure) cells file index source =
      ⟨(before.zip groups).map (fun (ordinal, slots) => groupBatch cells ⟨index, file.path, ordinal⟩ slots),
        .error (.file index file.path (.payload cause))⟩ := by
  unfold scanSource
  rw [split, assembleScanGroups_of_prefix cells file index source before (failed :: after) groups decoded]
  simp [Trace.assemble, scanGroup, error]

theorem project_finish (trace : Trace schema Failure) (projection : Scan.Projection schema) :
    (trace.project projection).finish = trace.finish.map projection.project := by
  cases outcome : trace.result with
  | error reason => simp [Trace.finish, Trace.project, outcome, Except.map]
  | ok done =>
    simp [Trace.finish, Trace.project, outcome, Except.map, Trace.rows, List.flatMap_map, Function.comp_def]
    unfold Scan.Projection.project
    rw [List.map_flatMap]
    apply congrArg (fun f : GroupBatch schema → Scan.Table projection.schema Cell => trace.batches.flatMap f)
    funext batch
    exact projection.rowsEquiv_projectColumns batch.columns

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

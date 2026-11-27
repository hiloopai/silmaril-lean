module

public import Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.Defs
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable
open Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8
open Date32.Utf8.ManifestWriter (File Limits Schema readSelected)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*} {schema : Scan.Schema String Kind}

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
        | .eos => .ok (Function.update db name (some ⟨schema, trace.rows⟩)) := by
  cases occupied : (db name).isSome
  · cases result with
    | error reason => simp [importResult, importCollected, collectResult, occupied]
    | ok trace =>
      cases outcome : trace.termination <;> simp [importResult, importCollected, collectResult, occupied, outcome]
  · simp [importResult, importCollected, occupied]

theorem importSelected_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (layout : Schema) (options : PartitionPath.Options) (limits : Limits) (projection : Scan.Projection layout.toScan)
    (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    importSelected db name layout options limits projection keep files = .ok next ↔
      db name = none ∧ ∃ trace,
        readSelected layout options limits projection keep files = .ok trace ∧ trace.termination = .eos ∧
        next = Function.update db name (some ⟨projection.schema, trace.rows⟩) := by
  rw [importSelected, importResult_outcome]
  cases occupied : db name with
  | some old => simp
  | none =>
    cases result : readSelected layout options limits projection keep files with
    | error reason => simp
    | ok trace =>
      cases outcome : trace.termination <;> simp [outcome, eq_comm]

theorem importSelected_observe [DecidableEq Name] (db next : Database Name) (name : Name)
    (layout : Schema) (options : PartitionPath.Options) (limits : Limits) (projection : Scan.Projection layout.toScan)
    (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File)
    (loaded : importSelected db name layout options limits projection keep files = .ok next) :
    ∃ trace,
      readSelected layout options limits projection keep files = .ok trace ∧ trace.termination = .eos ∧
      Scan.observePacked next name = some ⟨projection.schema, trace.rows⟩ ∧
      trace.rows.length = (trace.batches.map AlignedColumns.rowCount).sum ∧
      ∀ other, other ≠ name → next other = db other := by
  obtain ⟨_, trace, read, eos, rfl⟩ :=
    (importSelected_ok_iff db next name layout options limits projection keep files).mp loaded
  refine ⟨trace, read, eos, ?_, ?_, fun other different => Function.update_of_ne different _ _⟩
  · simp [Scan.observePacked, Silmaril.Relational.Database.Packed.erase, Silmaril.Relational.Database.Partial.map]
  · simp [Events.Trace.rows, List.length_flatMap, Function.comp_def]

end Silmaril.Proofs.Formats.Relational.NamedTable.FromHiveDateUtf8

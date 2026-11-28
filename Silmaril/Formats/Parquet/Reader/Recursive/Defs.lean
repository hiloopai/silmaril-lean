module

public import Silmaril.Formats.Parquet.Reader.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs

/-! Lift checked recursive logical row groups to the common Arrow reader. -/

namespace Silmaril.Formats.Parquet.Reader.Recursive

open Silmaril.Relational
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)
open Arrow.RecursiveSchema.Stream.Events (Signature Value signature declarations fieldName rowsOfBatch eraseBatch)

@[expose] public section

abbrev Trace (source : Signature) (Error : Type) := Arrow.Events.Trace source Value Error
abbrev EventStream (Error : Type) := Arrow.Events.EventStream (Option String) Value Error

structure Groups (fields : List Field) (Group Failure Error : Type) where
  order : List Group
  readGroup : Group → Except Failure Observation
  report : Group → Failure → Error
  checked : ∀ {group batch}, readGroup group = .ok batch →
    batch.rows.length = batch.rowCount ∧ ∀ row ∈ batch.rows, RowFits fields row

def groupRows {fields : List Field} {Failure Error : Type} (report : Failure → Error)
    (result : Except Failure Observation)
    (typed : ∀ batch, result = .ok batch → ∀ row ∈ batch.rows, RowFits fields row) :
    Except Error (Reader.RowGroup (signature fields) Value) :=
  match result with
  | .error cause => .error (report cause)
  | .ok batch => .ok (rowsOfBatch fields batch (typed batch rfl))

def Groups.toReader {fields : List Field} {Group Failure Error : Type}
    (groups : Groups fields Group Failure Error) : Reader.Source Group (signature fields) Value Error :=
  ⟨groups.order, fun group => groupRows (groups.report group) (groups.readGroup group)
    (fun _ decoded => (groups.checked decoded).2), fun _ => .ok ()⟩

def Groups.events {fields : List Field} {Group Failure Error : Type}
    (groups : Groups fields Group Failure Error) : EventStream Error :=
  Reader.readAll (.ok ⟨signature fields, groups.toReader⟩)

/-- Each successful group contributes its full observation. The first
failure contributes its original error and consumes the cursor. -/
inductive Prefix {Group Failure Error : Type} (readGroup : Group → Except Failure Observation)
    (report : Group → Failure → Error) :
    List Group → List Observation → Arrow.Events.Termination Error → Prop where
  | eos : Prefix readGroup report [] [] .eos
  | failed {group rest cause} :
      readGroup group = .error cause →
      Prefix readGroup report (group :: rest) [] (.readError (report group cause))
  | more {group rest batch batches terminal} :
      readGroup group = .ok batch →
      Prefix readGroup report rest batches terminal →
      Prefix readGroup report (group :: rest) (batch :: batches) terminal

structure Wire {fields : List Field} {Group Failure Error : Type}
    (groups : Groups fields Group Failure Error) (source : Signature) (events : Trace source Error) : Prop where
  fieldsExact : declarations source = fields.map (fun field => (fieldName field, field))
  completed : Prefix groups.readGroup groups.report groups.order (events.batches.map eraseBatch) events.termination

inductive Selection where
  | field
  | empty
  deriving DecidableEq, Repr

def Selection.columns (selection : Selection) (source : Signature) : Scan.Projection source :=
  match selection with
  | .field => Scan.Projection.id source
  | .empty => ⟨0, Fin.elim0⟩

end

end Silmaril.Formats.Parquet.Reader.Recursive

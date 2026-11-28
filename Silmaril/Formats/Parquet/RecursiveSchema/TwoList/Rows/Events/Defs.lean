module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs
public import Silmaril.Formats.Parquet.Reader.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms

/-! Direct Arrow events for the bounded two-LIST profile. One successful
group read contributes one batch. An error stops at the original group. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature Value declarations signature fieldName eraseBatch rowsOfBatch)
open Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)

@[expose] public section

inductive Error where
  | openError (original : TwoList.Error)
  | group (ordinal : Nat) (original : Rows.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Signature) := Arrow.Events.Trace source Value Error
abbrev EventStream := Arrow.Events.EventStream (Option String) Value Error

/-- Convert only a complete typed batch. The shared reader transposes the
positional rows when emitting the event. -/
def groupRows (fields : List Arrow.RecursiveSchema.Field) (group : Nat)
    (result : Except Rows.Error Observation)
    (typed : ∀ batch, result = .ok batch → ∀ row ∈ batch.rows, RowFits fields row) :
    Except Error (Reader.RowGroup (signature fields) Value) :=
  match result with
  | .error cause => .error (.group group cause)
  | .ok batch => .ok (rowsOfBatch fields batch (typed batch rfl))

def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error (Reader.RowGroup (signature (arrowSchema schema.plan).fields) Value) :=
  groupRows (arrowSchema schema.plan).fields group (Rows.readGroup limits schema group) (by
    intro batch accepted
    obtain ⟨_, _, _, _, _, wire⟩ := (Rows.readGroup_wire accepted).original
    exact wire.typed)

def sourceOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) :
    Reader.Source Nat (signature (arrowSchema schema.plan).fields) Value Error :=
  ⟨List.range snapshot.groupCount, readGroup limits schema, fun _ => .ok ()⟩

def readSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) : EventStream :=
  Reader.readAll (.ok ⟨_, sourceOf limits schema⟩)

def read (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits) (bytes : Bytes) : EventStream :=
  match TwoList.openFile schemaLimits bytes with
  | .error cause => .error (.openError cause)
  | .ok source => readSource limits source.schema

/-- Select the single original top-level field or select no fields. -/
inductive Selection where
  | field
  | empty
  deriving DecidableEq, Repr

def Selection.columns (selection : Selection) (source : Signature) : Scan.Projection source :=
  match selection with
  | .field => Scan.Projection.id source
  | .empty => ⟨0, Fin.elim0⟩

/-- Project only after reading the original groups. At width zero the row
count and the first reached source failure are still observed. -/
def readProjected (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits) (bytes : Bytes)
    (selection : Selection) : EventStream :=
  Arrow.RecursiveSchema.Stream.Events.project (read schemaLimits limits bytes) selection.columns

inductive GroupPrefix {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) :
    List Nat → List Observation → Arrow.Events.Termination Error → Prop where
  | eos : GroupPrefix limits schema [] [] .eos
  | failed {group rest cause} :
      Rows.readGroup limits schema group = .error cause →
      GroupPrefix limits schema (group :: rest) [] (.readError (.group group cause))
  | more {group rest batch batches terminal} :
      Rows.readGroup limits schema group = .ok batch →
      Rows.GroupWire limits schema group batch →
      GroupPrefix limits schema rest batches terminal →
      GroupPrefix limits schema (group :: rest) (batch :: batches) terminal

structure SourceWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot)
    (source : Signature) (events : Trace source) : Prop where
  fields : declarations source = (arrowSchema schema.plan).fields.map (fun field => (fieldName field, field))
  groups : GroupPrefix limits schema (List.range snapshot.groupCount)
    (events.batches.map eraseBatch) events.termination

structure FileWire (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits) (bytes : Bytes)
    (source : Signature) (events : Trace source) : Prop where
  original : ∃ opened, TwoList.openFile schemaLimits bytes = .ok opened ∧
    SourceWire limits opened.schema source events

/-- Both original layouts check through the existing chunk reader and agree
on the full ordered trace for each original group ordinal. -/
structure Reframe {leftSchemaLimits rightSchemaLimits : Snapshot.Limits}
    {leftSnapshot rightSnapshot : Snapshot.Checked}
    (leftLimits : Chunk.Limits) (left : Compiled leftSchemaLimits leftSnapshot)
    (rightLimits : Chunk.Limits) (right : Compiled rightSchemaLimits rightSnapshot) : Prop where
  plan : left.plan = right.plan
  count : leftSnapshot.groupCount = rightSnapshot.groupCount
  groups : ∀ group ∈ List.range leftSnapshot.groupCount,
    ∃ (leftBinding : Chunk.Binding left group) (rightBinding : Chunk.Binding right group)
      (leftColumn rightColumn : Chunk.Observation),
      Chunk.bind left group = .ok leftBinding ∧ Chunk.bind right group = .ok rightBinding ∧
      Chunk.read leftLimits leftBinding = .ok leftColumn ∧
      Chunk.read rightLimits rightBinding = .ok rightColumn ∧
      atoms leftColumn.pages = atoms rightColumn.pages

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

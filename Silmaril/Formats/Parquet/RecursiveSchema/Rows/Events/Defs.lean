module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Defs
public import Silmaril.Formats.Parquet.Reader.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Thms

/-! Direct shared Arrow Events from the original checked recursive Parquet
snapshot, with one positional batch per complete row group. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events

@[expose] public section

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Value Signature signature declarations fieldName eraseBatch)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

inductive Error where
  | openError (original : RecursiveSchema.Error)
  | group (ordinal : Nat) (original : Rows.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Signature) := Arrow.Events.Trace source Value Error
abbrev EventStream := Arrow.Events.EventStream (Option String) Value Error

/-- Cast the checked untyped observation to positional recursive cells.
The shared row-group reader transposes it once, including an empty group. -/
def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error (Reader.RowGroup (signature schema.arrow.fields) Value) :=
  match original : Rows.readGroup limits schema group with
  | .error cause => .error (.group group cause)
  | .ok observed =>
    .ok (Arrow.RecursiveSchema.Stream.Events.rowsOfBatch schema.arrow.fields observed
      (by exact (RecursiveSchema.Rows.readGroup_wire original).typed))

def sourceOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) :
    Reader.Source Nat (signature schema.arrow.fields) Value Error :=
  ⟨List.range snapshot.groupCount, readGroup limits schema, fun _ => .ok ()⟩

def readSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) : EventStream :=
  Reader.readAll (.ok ⟨signature schema.arrow.fields, sourceOf limits schema⟩)

/-- Open the original bytes once. Footer/schema refusals take place
before any schema or batch is emitted. -/
def read (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (bytes : Bytes) : EventStream :=
  match openFile schemaLimits bytes with
  | .error cause => .error (.openError cause)
  | .ok source => readSource limits source.schema

abbrev projectTrace {source : Signature} (projection : Scan.Projection source) (trace : Trace source) :
    Trace projection.schema :=
  Arrow.RecursiveSchema.Stream.Events.projectTrace projection trace

def readProjected (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (bytes : Bytes)
    (projection : (source : Signature) → Scan.Projection source) : EventStream :=
  Arrow.RecursiveSchema.Stream.Events.project (read schemaLimits limits bytes) projection

/-- A complete original group contributes exactly one observation. The
remaining original indices are unobserved after the first failed group. -/
inductive GroupPrefix {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) :
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
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot)
    (source : Signature) (events : Trace source) : Prop where
  fields : declarations source = schema.arrow.fields.map (fun field => (fieldName field, field))
  groups : GroupPrefix limits schema (List.range snapshot.groupCount)
    (events.batches.map eraseBatch) events.termination

structure FileWire (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (bytes : Bytes)
    (source : Signature) (events : Trace source) : Prop where
  original : ∃ opened, openFile schemaLimits bytes = .ok opened ∧
    SourceWire limits opened.schema source events

end

end Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events

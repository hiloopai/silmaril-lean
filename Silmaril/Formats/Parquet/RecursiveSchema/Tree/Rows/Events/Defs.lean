module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms

/-! Typed Arrow Events from the shared Tree row-group reader. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events

open Silmaril.Relational
open Parquet.Reader.Recursive (Groups Wire)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch project projectTrace)

@[expose] public section

inductive Error where
  | openError (original : Repeated.Error)
  | group (ordinal : Nat) (original : Rows.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Signature) := Parquet.Reader.Recursive.Trace source Error
abbrev EventStream := Parquet.Reader.Recursive.EventStream Error

def sourceOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) :
    Groups schema.arrow.fields Nat Rows.Error Error :=
  ⟨List.range snapshot.groupCount, Rows.readGroup schema limits, Error.group, by
    intro group batch accepted
    obtain ⟨result, _, rfl⟩ := Rows.readGroup_checked accepted
    exact ⟨result.exact.rows.trans result.exact.rowCount.symm, result.typed⟩⟩

def readSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) : EventStream :=
  (sourceOf limits schema).events

def read (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (input : Bytes) : EventStream :=
  match Tree.openFile schemaLimits input with
  | .error cause => .error (.openError cause)
  | .ok source => readSource limits source.schema

/-- Ordered positional selection uses the standard Arrow projection. The full
native reader validates every source leaf before selecting the output columns. -/
def readProjected (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (input : Bytes)
    (selection : (source : Signature) → Scan.Projection source) : EventStream :=
  project (read schemaLimits limits input) selection

/-- Project a logical observation by source position, retaining the explicit
row count and one zero-width row per input row at width zero. -/
def projectObservation {source : Signature} (selection : Scan.Projection source)
    (batch : Observation) : Observation :=
  ⟨batch.rowCount, batch.rows.map fun row =>
    List.ofFn fun i => row[(selection.index i).val]?.getD none⟩

def CheckedRead {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) (batch : Observation) : Prop :=
  ∃ result, Rows.readGroupChecked schema limits group = .ok result ∧ result.observation = batch

structure SourceWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot)
    (source : Signature) (events : Trace source) : Prop where
  logical : Wire (sourceOf limits schema) source events
  groups : List.Forall₂ (CheckedRead limits schema)
    ((List.range snapshot.groupCount).take events.batches.length) (events.batches.map eraseBatch)

structure FileWire (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (input : Bytes)
    (source : Signature) (events : Trace source) : Prop where
  original : ∃ opened, Tree.openFile schemaLimits input = .ok opened ∧ SourceWire limits opened.schema source events

structure ProjectedWire (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (input : Bytes)
    (selection : (source : Signature) → Scan.Projection source)
    (events : Σ source : Signature, Trace source) : Prop where
  original : ∃ (source : Signature) (trace : Trace source) (opened : Source schemaLimits input),
    Tree.openFile schemaLimits input = .ok opened ∧
    SourceWire limits opened.schema source trace ∧
    events = ⟨(selection source).schema, projectTrace (selection source) trace⟩ ∧
    declarations events.1 = List.ofFn (fun i => source.kind ((selection source).index i)) ∧
    events.2.batches.map eraseBatch = (trace.batches.map eraseBatch).map (projectObservation (selection source)) ∧
    events.2.termination = trace.termination

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events

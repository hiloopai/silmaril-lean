module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms

/-! Arrow Events for the original native LIST-path groups. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events

open Parquet.Reader.Recursive (Groups Selection Wire)
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch project)

@[expose] public section

inductive Error where
  | openError (original : ListPath.Error)
  | group (ordinal : Nat) (original : Reader.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Signature) := Parquet.Reader.Recursive.Trace source Error
abbrev EventStream := Parquet.Reader.Recursive.EventStream Error

def sourceOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) :
    Groups schema.plan.arrow.fields Nat Reader.Error Error :=
  ⟨List.range snapshot.groupCount, Reader.readGroup limits schema, Error.group, by
    intro group batch accepted
    obtain ⟨_, _, _, _, _, logical⟩ := (Reader.readGroup_wire accepted).original
    exact ⟨logical.count.trans logical.rowCount.symm, logical.typed⟩⟩

def readSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) : EventStream :=
  (sourceOf limits schema).events

def read (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits) (input : Bytes) : EventStream :=
  match ListPath.openFile schemaLimits input with
  | .error cause => .error (.openError cause)
  | .ok source => readSource limits source.schema

/-- Width zero still uses the original source reader, including its
complete groups and the first reached native failure. -/
def readProjected (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits)
    (input : Bytes) (selection : Selection) : EventStream :=
  project (read schemaLimits limits input) selection.columns

structure SourceWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot)
    (source : Signature) (events : Trace source) : Prop where
  logical : Wire (sourceOf limits schema) source events
  groups : List.Forall₂ (Reader.GroupWire limits schema)
    ((List.range snapshot.groupCount).take events.batches.length) (events.batches.map eraseBatch)

structure FileWire (schemaLimits : Snapshot.Limits) (limits : Chunk.Limits) (input : Bytes)
    (source : Signature) (events : Trace source) : Prop where
  original : ∃ opened, ListPath.openFile schemaLimits input = .ok opened ∧
    SourceWire limits opened.schema source events

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events

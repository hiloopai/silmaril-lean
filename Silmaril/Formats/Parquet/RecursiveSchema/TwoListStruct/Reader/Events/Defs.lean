module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms

/-! Arrow Events for the original native TwoListStruct groups. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events

open Parquet.Reader.Recursive (Groups Selection Wire)
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch project)

@[expose] public section

inductive Error where
  | openError (original : TwoListStruct.Error)
  | group (ordinal : Nat) (original : Reader.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Signature) := Parquet.Reader.Recursive.Trace source Error
abbrev EventStream := Parquet.Reader.Recursive.EventStream Error

def sourceOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Reader.Limits) (schema : Compiled schemaLimits snapshot) :
    Groups schema.plan.arrow.fields Nat Reader.Error Error :=
  ⟨List.range snapshot.groupCount, Reader.readGroup limits schema, Error.group, by
    intro group batch accepted
    have wire := Reader.readGroup_wire accepted
    obtain ⟨_, _, _, _, _, _, _, _, count, _, _⟩ := wire.original
    exact ⟨count, Reader.readGroup_typed accepted⟩⟩

def readSource {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Reader.Limits) (schema : Compiled schemaLimits snapshot) : EventStream :=
  (sourceOf limits schema).events

def read (schemaLimits : Snapshot.Limits) (limits : Reader.Limits) (input : Bytes) : EventStream :=
  match TwoListStruct.openFile schemaLimits input with
  | .error cause => .error (.openError cause)
  | .ok source => readSource limits source.schema

/-- Width zero still uses the original source reader, including its
complete groups and the first reached native failure. -/
def readProjected (schemaLimits : Snapshot.Limits) (limits : Reader.Limits)
    (input : Bytes) (selection : Selection) : EventStream :=
  project (read schemaLimits limits input) selection.columns

structure SourceWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Reader.Limits) (schema : Compiled schemaLimits snapshot)
    (source : Signature) (events : Trace source) : Prop where
  logical : Wire (sourceOf limits schema) source events
  groups : List.Forall₂ (Reader.GroupWire limits schema)
    ((List.range snapshot.groupCount).take events.batches.length) (events.batches.map eraseBatch)

structure FileWire (schemaLimits : Snapshot.Limits) (limits : Reader.Limits) (input : Bytes)
    (source : Signature) (events : Trace source) : Prop where
  original : ∃ opened, TwoListStruct.openFile schemaLimits input = .ok opened ∧
    SourceWire limits opened.schema source events

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events

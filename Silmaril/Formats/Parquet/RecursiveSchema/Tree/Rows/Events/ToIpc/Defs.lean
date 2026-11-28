module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Defs

/-! Strict Arrow V5 IPC from the shared recursive Tree Events source. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (schemaOf)

@[expose] public section

abbrev Error := Arrow.RecursiveSchema.Stream.Events.ToIpc.Error Events.Error

/-- Validate the original Tree groups, apply the selected view and pass the
result to the common strict emitter. The default view selects the full schema. -/
def convert (schemaLimits : Snapshot.Limits) (limits : Rows.Limits)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (input : Bytes)
    (selection : (source : Signature) → Scan.Projection source := Scan.Projection.id) :
    Except Error KBytes :=
  Arrow.RecursiveSchema.Stream.Events.ToIpc.emit ipc (Events.readProjected schemaLimits limits input selection)

structure Completed (schemaLimits : Snapshot.Limits) (limits : Rows.Limits) (input : Bytes)
    (selection : (source : Signature) → Scan.Projection source)
    (events : Σ source : Signature, Events.Trace source) : Prop where
  selected : Events.ProjectedWire schemaLimits limits input selection events
  terminal : events.2.termination = .eos
  groups : ∃ source opened, Tree.openFile schemaLimits input = .ok opened ∧
    List.Forall₂ (fun group batch => ∃ result,
      Rows.readGroupChecked opened.schema limits group = .ok result ∧
      batch = Events.projectObservation (selection source) result.observation)
      (List.range opened.snapshot.groupCount) (events.2.batches.map eraseBatch)

structure Readback (schemaLimits : Snapshot.Limits) (limits : Rows.Limits)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (input : Bytes)
    (selection : (source : Signature) → Scan.Projection source) (wire : KBytes) : Prop where
  original : ∃ events,
    Events.readProjected schemaLimits limits input selection = .ok events ∧
    Completed schemaLimits limits input selection events ∧
    Arrow.RecursiveSchema.Stream.Writer.Readback ipc (schemaOf events.1)
      (events.2.batches.map eraseBatch) wire

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc

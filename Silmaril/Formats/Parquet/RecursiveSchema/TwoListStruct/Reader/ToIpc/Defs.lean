module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Defs

/-! Strict Arrow V5 IPC from the checked original TwoListStruct event source. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

open Parquet.Reader.Recursive (Selection)

@[expose] public section

abbrev Error := Arrow.RecursiveSchema.Stream.Events.ToIpc.Error Events.Error

def convert (schemaLimits : Snapshot.Limits) (limits : Reader.Limits)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (input : Bytes) (selection : Selection := .field) :
    Except Error KBytes :=
  Arrow.RecursiveSchema.Stream.Events.ToIpc.emit ipc (Events.readProjected schemaLimits limits input selection)

/-- The native file's complete original groups correspond one for one
to the strict IPC observations under the selected declaration. -/
structure Readback (schemaLimits : Snapshot.Limits) (limits : Reader.Limits)
    (ipc : Arrow.RecursiveSchema.Batch.Limits) (input : Bytes) (selection : Selection) (wire : KBytes) : Prop where
  original : ∃ opened groups,
    TwoListStruct.openFile schemaLimits input = .ok opened ∧
    Reader.readAll limits opened.schema = .ok groups ∧
    List.Forall₂ (Reader.GroupWire limits opened.schema) (List.range opened.snapshot.groupCount) groups ∧
    Arrow.RecursiveSchema.Stream.Writer.Readback ipc (selection.schema opened.schema.plan.arrow)
      (groups.map selection.batch) wire

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

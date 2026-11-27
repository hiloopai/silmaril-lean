module

public import Silmaril.Formats.Arrow.RecursiveSchema.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Wire

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema

/-- An accepted AST binds every node to its original ordered Field vector
and table, within the configured depth and total field-occurrence limits. -/
theorem readMessage_wire {limits : Limits} {bytes : KBytes} {schema : Schema}
    (accepted : readMessage limits bytes = .ok schema) :
    SchemaWire limits bytes schema :=
  Proofs.Formats.Arrow.RecursiveSchema.readMessage_wire accepted

/-- The AST binds to the original padded Schema metadata of the modern IPC
frame. The returned cursor is exactly the end of that metadata. -/
theorem readFrame_wire {limits : Limits} {input : KBytes} {schema : Schema} {next : Nat}
    (accepted : readFrame limits input = .ok (schema, next)) :
    ∃ size, next = 8 + size ∧
      EnvelopeWire limits.ipc input.toList 0 (.metadata size) ∧
      (input.slice 8 size).toList = (input.toList.drop 8).take size ∧
      SchemaWire limits (input.slice 8 size) schema :=
  Proofs.Formats.Arrow.RecursiveSchema.readFrame_wire accepted

end Silmaril.Formats.Arrow.RecursiveSchema
